//! This module generates wrappers around verilator modules which are used
//! with spade-cxx to feed values to and from verilated units

use itertools::Itertools;
use nesty::{Code, code};
use num::ToPrimitive;
use spade_common::num_ext::InfallibleToBigUint;

use crate::{Entity, codegen::mangle_input, types::Type, unit_name::UnitNameKind};

impl Type {
    fn output_wrappers(
        &self,
        root_class: &str,
        path: Vec<&str>,
        class_name: &str,
    ) -> (String, String) {
        if self.size() == 0u32.to_biguint() {
            return (String::new(), String::new());
        }
        let (field_decls, field_impls, field_members, field_constructor_calls) = match self {
            Type::Struct(fields) => fields
                .iter()
                .map(|(name, ty)| {
                    let mut path = path.clone();
                    path.push(name);
                    let field_class_name = format!("{class_name}_{name}");
                    let (decls, impls) = ty.output_wrappers(root_class, path, &field_class_name);

                    let member = format!("{field_class_name}* {name};");

                    let constructor = format!(", {name}(init_{field_class_name}(root))");

                    (decls, impls, member, constructor)
                })
                .multiunzip(),
            _ => (
                "".to_string(),
                "".to_string(),
                "".to_string(),
                "".to_string(),
            ),
        };

        let field_as_strings = path.iter().map(|p| format!(r#""{p}""#)).join(", ");
        let declaration = code! {
            [0] field_decls;
            [0] format!("class {class_name};");
            [0] format!("{class_name}* init_{class_name}({root_class}* root);");
        }
        .to_string();

        let implementation = code! {
            [0] field_impls;
            [0] format!("class {class_name} {{");
            [1]     "public:";
            [2]         format!("{class_name}({root_class}* root)");
            [4]         format!(": root(root) ");
            [4]         field_constructor_calls;
            [2]         "{}";
            [4]         format!("{root_class}* root;");
            [2]         "bool operator==(std::string const& other) const {";
            [3]             format!(r#"auto field = root->s_ext->output_field({{{field_as_strings}}});"#);
            [3]             format!("auto val = spade::new_bit_string(root->output_string_fn());");
            [3]             format!(r#"return root"#);
            [3]             format!(r#"         ->s_ext"#);
            [3]             format!(r#"         ->compare_field(*field, other, *val)"#);
            [3]             format!(r#"         ->matches();"#);
            [2]         "}";
            [2]         format!("void assert_eq(std::string const& expected, std::string const& source_loc) {{");
            [3]             format!(r#"auto field = root->s_ext->output_field({{{field_as_strings}}});"#);
            [3]             format!("auto val = spade::new_bit_string(root->output_string_fn());");
            [3]             format!(r#"root"#);
            [3]             format!(r#"    ->s_ext"#);
            [3]             format!(r#"    ->assert_eq(*field, expected, *val, source_loc);"#);
            [2]         "}";
            [2]         format!("std::string spade_repr() {{");
            [3]             format!(r#"auto field = root->s_ext->output_field({{{field_as_strings}}});"#);
            [3]             format!("auto val = spade::new_bit_string(root->output_string_fn());");
            [3]             format!(r#"return std::string(root"#);
            [3]             format!(r#"    ->s_ext"#);
            [3]             format!(r#"    ->field_value(*field, *val));"#);
            [2]         "}";
            [2]         field_members;
            [0] "};";
            [0] format!("{class_name}* init_{class_name}({root_class}* root) {{");
            [1]     format!("return new {class_name}(root);");
            [0] "}";
        }.to_string();

        (declaration, implementation)
    }
}

impl Entity {
    fn input_wrapper(&self, parent_class_name: &str) -> (String, String) {
        let class_name = format!("{parent_class_name}_i");

        let (constructor_calls, fields_in_parent, field_classes): (Vec<_>, Vec<_>, Vec<_>) = self
            .inputs
            .iter()
            .filter(|f| f.ty.size() != 0u32.to_biguint())
            .map(|f| {
                let field_name = &f.name;
                let field_name_mangled = mangle_input(&f.no_mangle, &f.name);
                let field_class_name = format!("{class_name}_{field_name}");

                let assignment = if f.ty.size() <= 64u32.to_biguint() {
                    format!("parent.top->{field_name_mangled} = value->as_u64();")
                } else {
                    let size_u64 = f.ty.size().to_u64().expect("Input size does not fit in u64");
                    code! {
                        [0] "auto value_split = value->as_u32_chunks();";
                        [0] (0..(size_u64 / 32))
                            .map(|i| format!("parent.top->{field_name_mangled}[{i}] = value_split[{i}];"))
                            .join("\n");
                        [0] if size_u64 % 32 != 0 {
                                let idx = size_u64 / 32;
                                vec![format!("parent.top->{field_name_mangled}[{idx}] = value_split[{idx}];")]
                            } else {
                                vec![]
                            }
                    }.to_string()
                };

                let class = code! {
                    [0] format!("class {field_class_name} {{");
                    [1]     "public:";
                    [2]         format!("{field_class_name}({parent_class_name}& parent)");
                    [3]             ": parent(parent)";
                    [2]         "{}";
                    [2]         format!("{field_class_name}& operator=(std::string const& val) {{");
                    [3]             format!(r#"auto value = parent.s_ext->port_value("{field_name}", val);"#);
                    [3]             assignment;
                    [3]             "return *this;";
                    [2]         "}";
                    [1]     "private:";
                    [2]         format!("{parent_class_name}& parent;");
                    [0] "};"
                }.to_string();

                let constructor_call = format!(", {field_name}(parent)");
                let field = format!("{field_class_name} {field_name};");

                (constructor_call, field, class)
            })
            .multiunzip();

        let constructor = code! {
            [0] format!("{class_name}({parent_class_name}& parent)");
            [1]     ": parent(parent)";
            [1]     constructor_calls;
            [0] "{}"
        };

        let pre_declaration = code! {
            [0] format!("class {class_name};");
            // NOTE: Ugly hack to avoid having to generate both a cpp and hpp file while retaining
            // a loop in the 'dependency graph'. We'll define a free standing function to
            // initialize the input
            [0] format!("{class_name}* init_{class_name}({parent_class_name}& t);");
        }
        .to_string();
        let implementation = code! {
            [0] field_classes;
            [0] format!("class {class_name} {{");
            [1]     "public:";
            [2]         constructor;
            [2]         fields_in_parent;
            [1]     "private:";
            [2]         format!("{parent_class_name}& parent;");
            [0] "};";
            [0] format!("{class_name}* init_{class_name}({parent_class_name}& t) {{");
            [1]     format!("return new {class_name}(t);");
            [0] "}"
        }
        .to_string();

        (pre_declaration, implementation)
    }

    pub fn verilator_wrapper(&self) -> Option<String> {
        // Units which are mangled have no stable name in verilator, so we won't generate
        // them
        let name = match &self.name.kind {
            UnitNameKind::Unescaped(name) => name,
            UnitNameKind::Escaped { .. } => return None,
        };

        let class_name = format!("{name}_spade_t");
        let output_class_name = format!("{class_name}_o");

        let has_output = self.output_type.size() != 0u32.to_biguint();

        let constructor = code! {
            [0] format!("{class_name}(std::string spade_state, std::string spade_top, V{name}* top)");
            [1]     ": s_ext(spade::setup_spade(spade_top, spade_state))";
            [1]     ", top(top)";
            [1]     format!(", i(init_{class_name}_i(*this))");
            [1]     if has_output {format!(", o(init_{class_name}_o(this))")} else {String::new()};
            [0]  "{";
            [0] "}";
        };

        let (output_declaration, output_impl) =
            self.output_type
                .output_wrappers(&class_name, vec![], &output_class_name);

        let size = self.output_type.size();
        let size_u64 = self
            .output_type
            .size()
            .to_u64()
            .expect("Output size does not fit in 64 bits");
        let output_string_generator = if !has_output {
            code! {}
        } else if size <= 64u32.to_biguint() {
            code! {
                [0] format!("std::bitset<{size}> bits = this->top->output___05F;");
                [0] "std::stringstream ss;";
                [0] "ss << bits;";
                [0] "return ss.str();";
            }
        } else {
            code! {
                [0] "std::bitset<32> bits;";
                [0] "std::stringstream ss;";
                [0] if size_u64 % 32 != 0 {
                        code!{
                            [0] format!("std::bitset<{}> bits_;", size_u64 % 32);
                            [0] format!("bits_ = this->top->output___05F[{}];", size_u64 / 32);
                            [0] format!("ss << bits_;")
                        }
                    }
                    else {
                        code!{}
                    };
                [0] (0..(size / 32u32).to_u64().unwrap())
                    .rev()
                    .map(|i| {
                        code! {
                            [0] format!("bits = this->top->output___05F[{i}];");
                            [0] format!("ss << bits;")
                        }.to_string()
                    })
                    .join("\n");
                [0] "return ss.str();";
            }
        };

        let output_string_fn = code! {
            [0] "std::string output_string_fn() {";
            [0]     output_string_generator;
            [0] "}";
        };

        let (input_pre, input_impl) = self.input_wrapper(&class_name);
        let class = code! {
            [0] "#include <sstream>";
            [0] "#include <bitset>";
            [0] format!("#if __has_include(<V{name}.h>)");
            [0] format!(r#"#include <V{name}.h>"#);
            [0] format!("class {class_name};");
            [0] input_pre;
            [0] output_declaration;
            [0] format!("class {class_name} {{");
            [1]     "public:";
            [2]         constructor;
            [2]         format!("{class_name}_i* i;");
            [2]         if has_output {
                            format!("{class_name}_o* o;")
                        } else {
                            String::new()
                        };
            [2]         "rust::Box<spade::SimulationExt> s_ext;";
            [2]         format!("V{name}* top;");
            [2]         output_string_fn;
            [0] "};";
            [0] input_impl;
            [0] output_impl;
            [0] "#endif";
        };

        Some(class.to_string())
    }
}

pub fn verilator_wrappers(entities: &[&Entity]) -> String {
    let inner = entities
        .iter()
        .filter_map(|e| Entity::verilator_wrapper(e))
        .collect::<Vec<_>>();

    code! {
        [0] "#pragma once";
        [0] "#include <string>";
        [0] inner
    }
    .to_string()
}
