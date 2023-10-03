//! This module generates wrappers around verilator modules which are used
//! with spade-cxx to feed values to and from verilated units

use itertools::Itertools;
use nesty::{code, Code};
use num::ToPrimitive;
use spade_common::num_ext::InfallibleToBigUint;

use crate::{codegen::mangle_input, unit_name::UnitNameKind, Entity};

impl Entity {
    fn input_wrapper(&self, parent_class_name: &str) -> (String, String) {
        let class_name = format!("{parent_class_name}_i");

        let (constructor_calls, fields_in_parent, field_classes): (Vec<_>, Vec<_>, Vec<_>) = self
            .inputs
            .iter()
            .map(|f| {
                let field_name = &f.name;
                let field_name_mangled = mangle_input(&f.no_mangle, &f.name);
                let field_class_name = format!("{class_name}_{field_name}");

                let assignment = if f.ty.size() <= 64u32.to_biguint() {
                    format!("parent.top->{field_name_mangled} = value->as_u64();")
                } else {
                    code! {
                        [0] "auto value_split = value->as_u32_chunks();";
                        [0] (0..(f.ty.size() / 32u32).to_u64().unwrap())
                            .map(|i| format!("parent.top->{field_name_mangled}[{i}] = value_split[{i}];"))
                            .join("\n");
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

        let constructor = code! {
            [0] format!("{class_name}(std::string spade_state, std::string spade_top, V{name}* top)");
            [1]     ": s_ext(spade::setup_spade(spade_top, spade_state))";
            [1]     ", top(top)";
            [1]     format!(", i(init_{class_name}_i(*this))");
            [0]  "{";
            [0] "}";
        };

        let (input_pre, input_impl) = self.input_wrapper(&class_name);
        let class = code! {
            [0] format!("#if __has_include(<V{name}.h>)");
            [0] format!(r#"#include <V{name}.h>"#);
            [0] format!("class {class_name};");
            [0] input_pre;
            [0] format!("class {class_name} {{");
            [1]     "public:";
            [2]         constructor;
            [2]         format!("{class_name}_i* i;");
            [2]         "rust::Box<spade::SimulationExt> s_ext;";
            [2]         format!("V{name}* top;");
            [0] "};";
            [0] input_impl;
            [0] "#endif";
        };

        Some(class.to_string())
    }
}

pub fn verilator_wrappers(entities: &[&Entity]) -> String {
    let inner = entities
        .into_iter()
        .filter_map(|e| Entity::verilator_wrapper(e))
        .collect::<Vec<_>>();

    code! {
        [0] "#pragma once";
        [0] "#include <string>";
        [0] inner
    }
    .to_string()
}
