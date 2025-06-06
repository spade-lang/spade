use std::collections::HashMap;

use colored::Colorize;
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use tap::prelude::*;
use tracing::trace;

use spade_common::id_tracker::NameIdTracker;
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::{Identifier, NameID, Path};
use spade_diagnostics::diagnostic::Diagnostic;
use spade_types::meta_types::MetaType;

use crate::{
    FunctionKind, ParameterList, TraitSpec, TypeExpression, TypeParam, TypeSpec, UnitHead, UnitKind,
};

#[derive(Debug, Clone, PartialEq)]
pub enum LookupError {
    NoSuchSymbol(Loc<Path>),
    NotAThing(Loc<Path>),
    NotATypeSymbol(Loc<Path>, Thing),
    NotAVariable(Loc<Path>, Thing),
    NotAUnit(Loc<Path>, Thing),
    NotAnEnumVariant(Loc<Path>, Thing),
    NotAPatternableType(Loc<Path>, Thing),
    NotAStruct(Loc<Path>, Thing),
    NotAValue(Loc<Path>, Thing),
    NotAComptimeValue(Loc<Path>, Thing),
    NotATrait(Loc<Path>, Thing),
    IsAType(Loc<Path>),
    BarrierError(Diagnostic),
}

impl From<LookupError> for Diagnostic {
    fn from(lookup_error: LookupError) -> Diagnostic {
        match &lookup_error {
            LookupError::NoSuchSymbol(path) => {
                Diagnostic::error(path, format!("Use of undeclared name {path}"))
                    .primary_label("Undeclared name")
            }
            LookupError::NotAThing(path) => {
                Diagnostic::error(path, format!("Use of {path} before it was decleared"))
                    .primary_label("Undeclared name")
            }
            LookupError::IsAType(path) => {
                Diagnostic::error(path, format!("Unexpected type {path}"))
                    .primary_label("Unexpected type")
            }
            LookupError::BarrierError(diag) => diag.clone(),
            LookupError::NotATypeSymbol(path, got)
            | LookupError::NotAVariable(path, got)
            | LookupError::NotAUnit(path, got)
            | LookupError::NotAnEnumVariant(path, got)
            | LookupError::NotAPatternableType(path, got)
            | LookupError::NotAStruct(path, got)
            | LookupError::NotAValue(path, got)
            | LookupError::NotATrait(path, got)
            | LookupError::NotAComptimeValue(path, got) => {
                let expected = match lookup_error {
                    LookupError::NotATypeSymbol(_, _) => "a type",
                    LookupError::NotAVariable(_, _) => "a variable",
                    LookupError::NotAUnit(_, _) => "a unit",
                    LookupError::NotAnEnumVariant(_, _) => "an enum variant",
                    LookupError::NotAPatternableType(_, _) => "a patternable type",
                    LookupError::NotAStruct(_, _) => "a struct",
                    LookupError::NotAValue(_, _) => "a value",
                    LookupError::NotAComptimeValue(_, _) => "a compile time value",
                    LookupError::NotATrait(_, _) => "a trait",
                    LookupError::NoSuchSymbol(_)
                    | LookupError::IsAType(_)
                    | LookupError::BarrierError(_)
                    | LookupError::NotAThing(_) => unreachable!(),
                };

                // an entity can be instantiated, ...
                let hint = match lookup_error {
                    LookupError::NotAComptimeValue(_, _) => {
                        Some("compile time values can be defined with $config <name> = value")
                    }
                    _ => None,
                };
                let mut diagnostic =
                    Diagnostic::error(path, format!("Expected {path} to be {expected}"))
                        .primary_label(format!("Expected {expected}"))
                        .secondary_label(got.loc(), format!("{path} is a {}", got.kind_string()));

                if let Some(hint) = hint {
                    diagnostic.add_help(hint);
                }

                match lookup_error {
                    LookupError::NotAValue(path, Thing::EnumVariant(v)) => diagnostic
                        .span_suggest_insert_after(
                            "Consider specifying the arguments to the variant",
                            path,
                            format!(
                                "({})",
                                v.inner
                                    .params
                                    .0
                                    .iter()
                                    .map(|a| format!("/* {} */", a.name))
                                    .join(", ")
                            ),
                        ),
                    LookupError::NotAValue(path, Thing::Struct(v)) => diagnostic
                        .span_suggest_insert_after(
                            "Consider specifying the struct parameters",
                            path,
                            format!(
                                "({})",
                                v.inner
                                    .params
                                    .0
                                    .iter()
                                    .map(|a| format!("/*{}*/", a.name))
                                    .join(", ")
                            ),
                        ),
                    _ => diagnostic,
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum UniqueNameError {
    MultipleDefinitions { new: Loc<Path>, prev: Loc<()> },
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct EnumVariant {
    pub name: Loc<Identifier>,
    pub output_type: Loc<TypeSpec>,
    pub option: usize,
    pub params: Loc<ParameterList>,
    pub type_params: Vec<Loc<TypeParam>>,
    pub documentation: String,
}
impl WithLocation for EnumVariant {}

impl EnumVariant {
    pub fn as_unit_head(&self) -> UnitHead {
        UnitHead {
            name: self.name.clone(),
            inputs: self.params.clone(),
            output_type: Some(self.output_type.clone()),
            unit_type_params: self.type_params.clone(),
            scope_type_params: self.type_params.clone(),
            unit_kind: UnitKind::Function(FunctionKind::Enum).at_loc(&self.name),
            where_clauses: vec![],
            documentation: String::new(),
        }
    }
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct StructCallable {
    pub name: Loc<Identifier>,
    pub self_type: Loc<TypeSpec>,
    pub params: Loc<ParameterList>,
    pub type_params: Vec<Loc<TypeParam>>,
}
impl WithLocation for StructCallable {}
impl StructCallable {
    pub fn as_unit_head(&self) -> UnitHead {
        UnitHead {
            name: self.name.clone(),
            inputs: self.params.clone(),
            output_type: Some(self.self_type.clone()),
            unit_type_params: self.type_params.clone(),
            scope_type_params: vec![],
            unit_kind: UnitKind::Function(FunctionKind::Struct).at_loc(&self.name),
            where_clauses: vec![],
            documentation: String::new(),
        }
    }
}

/// Any named thing in the language which is not a type. Structs are here for instantiation
/// under the same NameID as the type
#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum Thing {
    /// Definition of a named type
    Struct(Loc<StructCallable>),
    EnumVariant(Loc<EnumVariant>),
    Unit(Loc<UnitHead>),
    Variable(Loc<Identifier>),
    Alias {
        path: Loc<Path>,
        in_namespace: Path,
    },
    PipelineStage(Loc<Identifier>),
    Module(Loc<Identifier>),
    /// Actual trait definition is present in the item list. This is only a marker
    /// for there being a trait with the item name.
    Trait(Loc<Identifier>),
}

impl Thing {
    pub fn kind_string(&self) -> &'static str {
        match self {
            Thing::Struct(_) => "struct",
            Thing::Unit(_) => "unit",
            Thing::Variable(_) => "variable",
            Thing::EnumVariant(_) => "enum variant",
            Thing::Alias { .. } => "alias",
            Thing::PipelineStage(_) => "pipeline stage",
            Thing::Trait(_) => "trait",
            Thing::Module(_) => "module",
        }
    }

    /// The Loc of the entire Thing.
    pub fn loc(&self) -> Loc<()> {
        match self {
            Thing::Struct(i) => i.loc(),
            Thing::Variable(i) => i.loc(),
            Thing::Unit(i) => i.loc(),
            Thing::EnumVariant(i) => i.loc(),
            Thing::Alias {
                path,
                in_namespace: _,
            } => path.loc(),
            Thing::PipelineStage(i) => i.loc(),
            Thing::Trait(loc) => loc.loc(),
            Thing::Module(loc) => loc.loc(),
        }
    }

    /// The Loc where the name of the thing is defined.
    pub fn name_loc(&self) -> Loc<()> {
        match self {
            Thing::Struct(s) => s.name.loc(),
            Thing::EnumVariant(v) => v.name.loc(),
            Thing::Unit(f) => f.name.loc(),
            Thing::Variable(v) => v.loc(),
            Thing::Alias {
                path,
                in_namespace: _,
            } => path.loc(),
            Thing::PipelineStage(_) => todo!(),
            Thing::Trait(loc) => loc.loc(),
            Thing::Module(loc) => loc.loc(),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum PatternableKind {
    Struct,
    Enum,
}
#[derive(PartialEq, Debug, Clone)]
pub struct Patternable {
    pub kind: PatternableKind,
    pub params: Loc<ParameterList>,
}
impl WithLocation for Patternable {}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum GenericArg {
    TypeName {
        name: Identifier,
        traits: Vec<Loc<TraitSpec>>,
    },
    TypeWithMeta {
        name: Identifier,
        meta: MetaType,
    },
}

impl GenericArg {
    pub fn uint(name: Identifier) -> Self {
        GenericArg::TypeWithMeta {
            name,
            meta: MetaType::Uint,
        }
    }
}
impl WithLocation for GenericArg {}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum TypeDeclKind {
    Struct { is_port: bool },
    Enum,
    Primitive { is_port: bool },
}

impl TypeDeclKind {
    pub fn normal_struct() -> Self {
        TypeDeclKind::Struct { is_port: false }
    }
    pub fn struct_port() -> Self {
        TypeDeclKind::Struct { is_port: true }
    }

    pub fn name(&self) -> String {
        match self {
            TypeDeclKind::Struct { is_port } => {
                format!("struct{}", if *is_port { " port" } else { "" })
            }
            TypeDeclKind::Enum => "enum".to_string(),
            TypeDeclKind::Primitive { .. } => "primitive".to_string(),
        }
    }
}

/// A previously declared type symbol
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum TypeSymbol {
    /// A fixed type that has been declared, like a typedef, enum or struct with the
    /// specified generic arguments
    Declared(Vec<Loc<GenericArg>>, TypeDeclKind),
    /// A generic type present in the current scope
    GenericArg {
        traits: Vec<Loc<TraitSpec>>,
    },
    GenericMeta(MetaType),
    /// A type alias. This is lowered during initial AST lowering, so subsequent compilation
    /// stages can bail on finding this
    Alias(Loc<TypeExpression>),
}
impl WithLocation for TypeSymbol {}

/// The declaration/definition status of a variable
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum DeclarationState {
    /// This variable has been defined by a `decl` statement
    Undefined(NameID),
    /// There is a pipeline reference to this variable, but no definition or declaration (yet)
    Undecleared(NameID),
    /// This variable has been defined (and assigned) with a let binding.
    /// All variables must be in the declared state before the end of the scope
    Defined(Loc<()>),
}
impl WithLocation for DeclarationState {}

pub type ScopeBarrier =
    dyn Fn(&Loc<Path>, &Loc<NameID>, &Thing) -> Result<(), Diagnostic> + Send + Sync;

#[derive(Serialize, Deserialize)]
pub struct Scope {
    vars: HashMap<Path, NameID>,
    #[serde(skip)]
    lookup_barrier: Option<Box<ScopeBarrier>>,
}
impl std::fmt::Debug for Scope {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            vars,
            lookup_barrier: _,
        } = self;
        write!(f, "Scope({vars:?})")
    }
}

/// A table of the symbols known to the program in the current scope. Names
/// are mapped to IDs which are then mapped to the actual things
///
/// Modules are managed by a special variable in the symtab. All names in the
/// symtab are absolute paths, that is `X` in `mod A{mod B {fn X}}` will only be
/// stored as `A::B::X`. All variables inside X will also have the full path
/// appended to them. This should however be invisible to the user.
#[derive(Debug, Serialize, Deserialize)]
pub struct SymbolTable {
    /// Each outer vec is a scope, inner vecs are symbols in that scope
    pub symbols: Vec<Scope>,
    pub declarations: Vec<HashMap<Loc<Identifier>, DeclarationState>>,
    id_tracker: NameIdTracker,
    pub types: HashMap<NameID, Loc<TypeSymbol>>,
    pub things: HashMap<NameID, Thing>,
    /// The namespace which we are currently in. When looking up and adding symbols, this namespace
    /// is added to the start of the path, thus ensuring all paths are absolute. If a path is not
    /// found that path is also looked up in the global namespace
    namespace: Path,
    /// The namespace which `lib` refers to currently.
    base_namespace: Path,
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            symbols: vec![Scope {
                vars: HashMap::new(),
                lookup_barrier: None,
            }],
            declarations: vec![HashMap::new()],
            id_tracker: NameIdTracker::new(),
            types: HashMap::new(),
            things: HashMap::new(),
            namespace: Path(vec![]),
            base_namespace: Path(vec![]),
        }
    }
    #[tracing::instrument(skip_all)]
    pub fn new_scope(&mut self) {
        self.symbols.push(Scope {
            vars: HashMap::new(),
            lookup_barrier: None,
        });
        self.declarations.push(HashMap::new());
    }

    pub fn new_scope_with_barrier(&mut self, barrier: Box<ScopeBarrier>) {
        self.symbols.push(Scope {
            vars: HashMap::new(),
            lookup_barrier: Some(barrier),
        });
        self.declarations.push(HashMap::new());
    }

    #[tracing::instrument(skip_all)]
    pub fn close_scope(&mut self) {
        self.symbols.pop();
        self.declarations.pop();
    }

    pub fn current_scope(&self) -> usize {
        self.symbols.len() - 1
    }

    /// Push an identifier onto the current namespace
    #[tracing::instrument(skip_all, fields(%new_ident))]
    pub fn push_namespace(&mut self, new_ident: Loc<Identifier>) {
        self.namespace = self.namespace.push_ident(new_ident.clone());
    }

    #[tracing::instrument(skip_all)]
    pub fn pop_namespace(&mut self) {
        self.namespace = self.namespace.pop();
    }

    pub fn current_namespace(&self) -> &Path {
        &self.namespace
    }

    pub fn set_base_namespace(&mut self, base_namespace: Path) {
        self.base_namespace = base_namespace
    }

    /// Adds a thing to the scope at `current_scope - offset`. Panics if there is no such scope
    pub fn add_thing_with_id_at_offset(
        &mut self,
        offset: usize,
        id: u64,
        name: Path,
        item: Thing,
    ) -> NameID {
        let full_name = self.namespace.join(name);

        let name_id = NameID(id, full_name.clone());
        if self.things.contains_key(&name_id) {
            panic!("Duplicate nameID inserted, {}", id);
        }
        self.things.insert(name_id.clone(), item);

        if offset > self.symbols.len() {
            panic!("Not enough scopes to add symbol at offset {}", offset);
        }

        let index = self.symbols.len() - 1 - offset;
        self.symbols[index].vars.insert(full_name, name_id.clone());

        name_id
    }

    /// Add a thing to the symtab with the specified NameID. The NameID must already be in
    /// the symtab when calling this function
    pub fn add_thing_with_name_id(&mut self, name_id: NameID, item: Thing) {
        self.things.insert(name_id, item);
    }

    pub fn add_thing_with_id(&mut self, id: u64, name: Path, item: Thing) -> NameID {
        self.add_thing_with_id_at_offset(0, id, name, item)
    }

    #[tracing::instrument(skip_all, fields(?name))]
    pub fn add_unique_thing(&mut self, name: Loc<Path>, item: Thing) -> Result<NameID, Diagnostic> {
        self.ensure_is_unique(&name)?;
        Ok(self.add_thing(name.inner, item))
    }

    pub fn add_thing(&mut self, name: Path, item: Thing) -> NameID {
        let id = self.id_tracker.next();
        self.add_thing_with_id(id, name, item)
    }

    pub fn re_add_type(&mut self, name: Loc<Identifier>, name_id: NameID) {
        assert!(self.types.contains_key(&name_id));
        self.symbols
            .last_mut()
            .unwrap()
            .vars
            .insert(self.namespace.join(Path::ident(name)), name_id);
    }

    pub fn add_type_with_id(&mut self, id: u64, name: Path, t: Loc<TypeSymbol>) -> NameID {
        let full_name = self.namespace.join(name);
        let name_id = NameID(id, full_name.clone());
        if self.types.contains_key(&name_id) {
            panic!("Duplicate nameID for types, {}", id)
        }
        self.types.insert(name_id.clone(), t);
        self.symbols
            .last_mut()
            .unwrap()
            .vars
            .insert(full_name, name_id.clone());
        name_id
    }

    pub fn add_type(&mut self, name: Path, t: Loc<TypeSymbol>) -> NameID {
        let id = self.id_tracker.next();
        self.add_type_with_id(id, name, t)
    }

    pub fn add_traits_to_generic(
        &mut self,
        name_id: &NameID,
        traits: Vec<Loc<TraitSpec>>,
    ) -> Result<(), Diagnostic> {
        assert!(self.types.contains_key(&name_id));
        match &mut self.types.get_mut(name_id).unwrap().inner {
            TypeSymbol::GenericArg { traits: existing } => {
                existing.extend(traits);
                Ok(())
            }
            _ => Err(Diagnostic::bug(
                self.type_symbol_by_id(name_id).loc(),
                "Attempted to add trait bounds to a non-generic type",
            )),
        }
    }

    pub fn add_unique_type(
        &mut self,
        name: Loc<Path>,
        t: Loc<TypeSymbol>,
    ) -> Result<NameID, Diagnostic> {
        self.ensure_is_unique(&name)?;

        Ok(self.add_type(name.inner, t))
    }

    #[tracing::instrument(skip_all, fields(?name, ?target))]
    pub fn add_alias(&mut self, name: Loc<Path>, target: Loc<Path>) -> Result<NameID, Diagnostic> {
        self.ensure_is_unique(&name)?;
        let absolute_path = if let Some(lib_relative) = target.inner.lib_relative() {
            self.base_namespace.join(lib_relative)
        } else {
            target.inner.clone()
        };
        let path = absolute_path.between(name.file_id, &name, &target);
        Ok(self.add_thing(
            name.inner,
            Thing::Alias {
                path,
                in_namespace: self.current_namespace().clone(),
            },
        ))
    }

    /// Adds a thing to the scope at `current_scope - offset`. Panics if there is no such scope
    pub fn add_thing_at_offset(&mut self, offset: usize, name: Path, item: Thing) -> NameID {
        let id = self.id_tracker.next();
        self.add_thing_with_id_at_offset(offset, id, name, item)
    }

    pub fn freeze(self) -> FrozenSymtab {
        let id_tracker = self.id_tracker.make_clone();
        FrozenSymtab {
            inner: self,
            id_tracker,
        }
    }

    pub fn add_local_variable(&mut self, name: Loc<Identifier>) -> NameID {
        let path = Path(vec![name.clone()]);
        self.add_thing(path, Thing::Variable(name))
    }
    pub fn add_local_variable_at_offset(&mut self, offset: usize, name: Loc<Identifier>) -> NameID {
        let path = Path(vec![name.clone()]);
        self.add_thing_at_offset(offset, path, Thing::Variable(name))
    }

    pub fn add_declaration(&mut self, ident: Loc<Identifier>) -> Result<NameID, Diagnostic> {
        let declared_more_than_once = |new, old| {
            Diagnostic::error(new, "Variable declared more than once")
                .primary_label("This variable has been declared more than once")
                .secondary_label(old, "Previously declared here")
        };
        // Check if a variable with this name already exists
        if let Some(id) = self.try_lookup_id(&Path(vec![ident.clone()]).at_loc(&ident), &[]) {
            if let Some(Thing::Variable(prev)) = self.things.get(&id) {
                return Err(declared_more_than_once(ident, prev));
            }
        }

        if let Some((old, _)) = self.declarations.last().unwrap().get_key_value(&ident) {
            Err(declared_more_than_once(ident, old))
        } else {
            let name_id = self.add_local_variable(ident.clone());
            self.declarations
                .last_mut()
                .unwrap()
                .insert(ident, DeclarationState::Undefined(name_id.clone()));
            Ok(name_id)
        }
    }

    pub fn add_undecleared_at_offset(&mut self, offset: usize, name: Loc<Identifier>) -> NameID {
        let path = Path(vec![name.clone()]);

        let name_id = NameID(self.id_tracker.next(), path.clone());
        let full_name = self.namespace.join(path);

        let index = self.symbols.len() - 1 - offset;
        if index > self.symbols.len() {
            panic!("Not enough scopes to add symbol at offset {}", offset);
        }
        self.symbols[index].vars.insert(full_name, name_id.clone());
        self.declarations[index].insert(name, DeclarationState::Undecleared(name_id.clone()));

        name_id
    }

    pub fn get_declaration(&mut self, ident: &Loc<Identifier>) -> Option<Loc<DeclarationState>> {
        self.declarations
            .last()
            .unwrap()
            .get_key_value(ident)
            .map(|(k, v)| v.clone().at_loc(k))
    }

    pub fn mark_declaration_defined(&mut self, ident: Loc<Identifier>, definition_point: Loc<()>) {
        *self
            .declarations
            .last_mut()
            .unwrap()
            .get_mut(&ident)
            .unwrap() = DeclarationState::Defined(definition_point)
    }

    pub fn get_undefined_declarations(&self) -> Vec<(Loc<Identifier>, DeclarationState)> {
        self.declarations
            .last()
            .unwrap()
            .iter()
            .filter_map(|(ident, state)| match state {
                DeclarationState::Undefined(_) => Some((ident.clone(), state.clone())),
                DeclarationState::Undecleared(_) => Some((ident.clone(), state.clone())),
                DeclarationState::Defined(_) => None,
            })
            .collect()
    }
}
macro_rules! thing_accessors {
    (
        $(
            $by_id_name:ident,
            $lookup_name:ident,
            $result:path,
            $err:ident $(,)?
            {$($thing:pat => $conversion:expr),*$(,)?}
        ),*
    ) => {
        $(
            /// Look up an item and panic if the item is not in the symtab or if it is the wrong
            /// type
            pub fn $by_id_name(&self, id: &NameID) -> Loc<$result> {
                match self.things.get(&id) {
                    $(
                        Some($thing) => {$conversion}
                    )*,
                    Some(other) => panic!("attempted to look up {} but it was {:?}", stringify!($result), other),
                    None => panic!("No thing entry found for {:?}", id)
                }
            }

            /// Look up an item, with errors if the item is not currently in scope, or is not
            /// convertible to the return type.
            #[tracing::instrument(level = "trace", skip_all, fields(%name.inner, %name.span, %name.file_id))]
            pub fn $lookup_name(&self, name: &Loc<Path>) -> Result<(NameID, Loc<$result>), LookupError> {
                let id = self.lookup_final_id(name, &[]).tap(|id| trace!(?id))?;

                match self.things.get(&id).tap(|thing| trace!(?thing)) {
                    $(
                        Some($thing) => {Ok((id, $conversion))}
                    )*,
                    Some(other) => Err(LookupError::$err(name.clone(), other.clone())),
                    None => {
                        match self.types.get(&id) {
                            Some(_) => Err(LookupError::IsAType(name.clone())),
                            None => Err(LookupError::NotAThing(name.clone()))
                        }
                    }
                }
            }
        )*
    }
}

impl SymbolTable {
    // Define accessors for accessing items. *_by_id looks up things under the
    // assumption that the name is in the symtab, and that it is the specified type.
    // If this is not true, it panics.
    //
    // lookup_* looks up items by path, and returns the NameID and item if successful.
    // If the path is not in scope, or the item is not the right kind, returns an error.
    thing_accessors! {
        unit_by_id, lookup_unit, UnitHead, NotAUnit {
            Thing::Unit(head) => head.clone(),
            Thing::EnumVariant(variant) => variant.as_unit_head().at_loc(variant),
            Thing::Struct(s) => s.as_unit_head().at_loc(s),
        },
        enum_variant_by_id, lookup_enum_variant, EnumVariant, NotAnEnumVariant {
            Thing::EnumVariant(variant) => variant.clone()
        },
        patternable_type_by_id, lookup_patternable_type, Patternable, NotAPatternableType {
            Thing::EnumVariant(variant) => Patternable{
                kind: PatternableKind::Enum,
                params: variant.params.clone()
            }.at_loc(variant),
            Thing::Struct(variant) => Patternable {
                kind: PatternableKind::Struct,
                params: variant.params.clone()
            }.at_loc(variant),
        },
        struct_by_id, lookup_struct, StructCallable, NotAStruct {
            Thing::Struct(s) => s.clone()
        },
        trait_by_id, lookup_trait, Identifier, NotATrait {
            Thing::Trait(t) => t.clone()
        }
    }

    pub fn type_symbol_by_id(&self, id: &NameID) -> Loc<TypeSymbol> {
        match self.types.get(id) {
            Some(inner) => inner.clone(),
            None => panic!("No thing entry found for {:?}", id),
        }
    }

    pub fn lookup_type_symbol(
        &self,
        name: &Loc<Path>,
    ) -> Result<(NameID, Loc<TypeSymbol>), LookupError> {
        let id = self.lookup_final_id(name, &[])?;

        match self.types.get(&id) {
            Some(tsym) => Ok((id, tsym.clone())),
            None => match self.things.get(&id) {
                Some(thing) => Err(LookupError::NotATypeSymbol(name.clone(), thing.clone())),
                None => panic!("{:?} was in symtab but is neither a type nor a thing", id),
            },
        }
    }

    pub fn has_symbol(&self, name: Path) -> bool {
        match self.lookup_id(&name.nowhere(), &[]) {
            Ok(_) => true,
            Err(LookupError::NoSuchSymbol(_)) => false,
            Err(LookupError::BarrierError(_)) => unreachable!(),
            Err(LookupError::NotATypeSymbol(_, _)) => unreachable!(),
            Err(LookupError::NotAVariable(_, _)) => unreachable!(),
            Err(LookupError::NotAUnit(_, _)) => unreachable!(),
            Err(LookupError::NotAPatternableType(_, _)) => unreachable!(),
            Err(LookupError::NotAnEnumVariant(_, _)) => unreachable!(),
            Err(LookupError::NotAStruct(_, _)) => unreachable!(),
            Err(LookupError::NotAValue(_, _)) => unreachable!(),
            Err(LookupError::NotAComptimeValue(_, _)) => unreachable!(),
            Err(LookupError::NotATrait(_, _)) => unreachable!(),
            Err(LookupError::IsAType(_)) => unreachable!(),
            Err(LookupError::NotAThing(_)) => unreachable!(),
        }
    }

    /// Look up the previous definition of `name` returning a "Multiple items with the same name" error if
    /// such definition already exists. Only an absolute path in the root name space is checked
    /// as this is intended to be used for item definitions
    pub fn ensure_is_unique(&self, name: &Loc<Path>) -> Result<(), Diagnostic> {
        let full_path = self.current_namespace().join(name.inner.clone());

        let prev = self
            .symbols
            .first()
            .unwrap()
            .vars
            .get(&full_path)
            .and_then(|id| {
                self.things
                    .get(id)
                    .map(|thing| thing.name_loc())
                    .or_else(|| self.types.get(id).map(|t| t.loc()))
            });

        match prev {
            Some(prev) => Err(Diagnostic::error(name, "Multiple items with the same name")
                .primary_label(format!("{} is defined multiple times", name))
                .secondary_label(prev, "Previous definition here")),
            None => Ok(()),
        }
    }

    pub fn lookup_variable(&self, name: &Loc<Path>) -> Result<NameID, LookupError> {
        let id = self.lookup_final_id(name, &[])?;

        match self.things.get(&id) {
            Some(Thing::Variable(_)) => Ok(id),
            Some(other) => Err(LookupError::NotAVariable(name.clone(), other.clone())),
            None => match self.types.get(&id) {
                Some(_) => Err(LookupError::IsAType(name.clone())),
                None => Err(LookupError::NotAThing(name.clone())),
            },
        }
    }

    /// Look up `name`. If it is defined and a variable, return that name. If it is defined
    /// but not a variable, return an error. If it is undefined, return None
    ///
    /// Intended for use if undefined variables should be declared
    pub fn try_lookup_variable(&self, name: &Loc<Path>) -> Result<Option<NameID>, LookupError> {
        let id = self.try_lookup_final_id(name, &[]);
        match id {
            Some(id) => match self.things.get(&id) {
                Some(Thing::Variable(_)) => Ok(Some(id)),
                Some(other) => Err(LookupError::NotAVariable(name.clone(), other.clone())),
                None => match self.types.get(&id) {
                    Some(_) => Err(LookupError::IsAType(name.clone())),
                    None => Ok(None),
                },
            },
            None => Ok(None),
        }
    }

    pub fn try_lookup_final_id(&self, name: &Loc<Path>, forbidden: &[NameID]) -> Option<NameID> {
        match self.lookup_final_id(name, forbidden) {
            Ok(id) => Some(id),
            Err(LookupError::NoSuchSymbol(_)) => None,
            Err(_) => unreachable!(),
        }
    }

    /// Returns the name ID of the provided path if that path exists and resolving
    /// all aliases along the way.
    pub fn lookup_final_id(
        &self,
        name: &Loc<Path>,
        forbidden: &[NameID],
    ) -> Result<NameID, LookupError> {
        let mut forbidden = forbidden.to_vec();
        let mut namespace = &self.namespace;
        let mut name = name.clone();

        loop {
            let id = self.lookup_id_in_namespace(&name, &forbidden, namespace)?;
            match self.things.get(&id) {
                Some(Thing::Alias {
                    path: alias,
                    in_namespace,
                }) => {
                    forbidden.push(id);
                    name = alias.clone();
                    namespace = in_namespace;
                }
                _ => return Ok(id),
            }
        }
    }

    pub fn try_lookup_id(&self, name: &Loc<Path>, forbidden: &[NameID]) -> Option<NameID> {
        match self.lookup_id(name, forbidden) {
            Ok(id) => Some(id),
            Err(LookupError::NoSuchSymbol(_)) => None,
            Err(_) => unreachable!(),
        }
    }

    /// Resolves a given relative path to the next thing.
    ///
    /// That thing might also be an alias.
    /// When you want to also resolve aliases, look at [`Self::try_lookup_final_id`] instead.
    ///
    /// ## Warning
    /// For `use A;` where the path is only one segment wide, it will return itself.
    /// This might end in an infinite lookup. Forbid already looked up nameids or use [`Self::try_lookup_final_id`] instead.
    #[tracing::instrument(level = "trace", skip(self))]
    #[inline]
    pub fn lookup_id(&self, name: &Loc<Path>, forbidden: &[NameID]) -> Result<NameID, LookupError> {
        self.lookup_id_in_namespace(name, forbidden, &self.namespace)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    fn lookup_id_in_namespace(
        &self,
        name: &Loc<Path>,
        forbidden: &[NameID],
        namespace: &Path,
    ) -> Result<NameID, LookupError> {
        // The behaviour depends on whether or not the path is a library relative path (starting
        // with `lib`) or not. If it is, an absolute lookup of the path obtained by
        // substituting `lib` for the current `base_path` should be performed.
        //
        // If not, three lookups should be performed
        //  - The path in the root namespace
        //  - The path in the current namespace
        //  - The path in other use statements. For example, with
        //      ```
        //      use a::b;
        //
        //      b::c();
        //      ```
        //      A lookup for `b` is performed which returns an alias (a::b). From that, another
        //      lookup for a::b::c is performed.
        let absolute_path = if let Some(lib_relative) = name.lib_relative() {
            self.base_namespace.join(lib_relative).at_loc(name)
        } else {
            let local_path = namespace.join(name.inner.clone());
            let mut barriers: Vec<&Box<ScopeBarrier>> = vec![];
            for tab in self.symbols.iter().rev() {
                if let Some(id) = tab.vars.get(&local_path) {
                    if forbidden.iter().contains(id) {
                        continue;
                    }
                    for barrier in barriers {
                        self.things
                            .get(id)
                            .map(|thing| {
                                (barrier)(name, &id.clone().at_loc(&thing.name_loc()), thing)
                                    .map_err(LookupError::BarrierError)
                            })
                            .unwrap_or(Ok(()))?;
                    }
                    return Ok(id.clone());
                }
                if let Some(barrier) = &tab.lookup_barrier {
                    barriers.push(barrier);
                }
            }

            if name.inner.0.len() > 1 {
                let base_name = name.inner.0.first().unwrap();

                let alias_id =
                    self.lookup_id(&Path(vec![base_name.clone()]).at_loc(base_name), forbidden)?;

                // Extend forbidden slice with newly used alias
                let mut forbidden = forbidden.to_vec();
                forbidden.push(alias_id.clone());

                match self.things.get(&alias_id) {
                    Some(Thing::Alias {
                        path: alias_path,
                        in_namespace,
                    }) => {
                        let alias_result =
                            self.lookup_id_in_namespace(alias_path, &forbidden, in_namespace)?;

                        // Pop the aliased bit of the path
                        let rest_path = Path(name.inner.0[1..].into());

                        alias_result.1.join(rest_path).at_loc(name)
                    }
                    _ => name.clone(),
                }
            } else {
                name.clone()
            }
        };

        // Then look up things in the absolute namespace. This is only needed at the
        // top scope as that's where all top level will be defined
        if let Some(id) = self.symbols.first().unwrap().vars.get(&absolute_path) {
            if !forbidden.contains(id) {
                return Ok(id.clone());
            }
        }

        // ERROR: Symbol couldn't be found
        // Look recursively which path segment can not be found
        // This is a check that there are at least 2 path segments and we also grab one.
        if let [_first, .., tail] = absolute_path.0.as_slice() {
            let prelude = &absolute_path.0[..absolute_path.0.len() - 1];
            let _ = self.lookup_id_in_namespace(
                &Path(prelude.to_vec()).nowhere(),
                forbidden,
                namespace,
            )?;
            Err(LookupError::NoSuchSymbol(
                absolute_path.inner.clone().at_loc(tail),
            ))
        } else {
            Err(LookupError::NoSuchSymbol(name.clone()))
        }
    }

    pub fn print_symbols(&self) {
        println!("=============================================================");
        println!("                      Symtab dump");
        println!("=============================================================");
        println!("Current namespace is `{}`", self.namespace);
        println!("Current base_namespace is `{}`", self.base_namespace);
        for (level, scope) in self.symbols.iter().enumerate() {
            let indent = (1..level + 1).map(|_| "\t").collect::<Vec<_>>().join("");
            println!(">>> new_scope",);

            for (path, name) in &scope.vars {
                println!(
                    "{indent}{path} => {name}",
                    path = format!("{path}").cyan(),
                    name = format!("{name:?}").yellow()
                );
            }
        }

        println!("Things:");
        for (name, thing) in &self.things {
            print!("{}: ", format!("{name:?}").purple());
            match thing {
                Thing::Struct(_) => println!("struct"),
                Thing::EnumVariant(_) => println!("enum variant"),
                Thing::Unit(_) => println!("unit"),
                Thing::Variable(_) => println!("variable"),
                Thing::Alias { path, in_namespace } => {
                    println!("{}", format!("alias => {path} in {in_namespace}").green())
                }
                Thing::PipelineStage(stage) => println!("'{stage}"),
                Thing::Trait(name) => println!("trait {}", name),
                Thing::Module(name) => println!("mod {name}"),
            }
        }

        println!("Types:");
        for name in self.types.keys() {
            print!("{}: ", format!("{name:?}").purple());
            println!("type");
        }
    }
}

/// A symbol table that cannot have any new symbols added to it. The ID tracker can be used to
/// generate new names for for intermediate variables during codegen.
///
/// Mutable references to `SymbolTable` are never given out, ensuring that nothing can be added to
/// the symtab, thus avoiding collisions with things added using the Id tracker.
#[derive(Serialize, Deserialize)]
pub struct FrozenSymtab {
    inner: SymbolTable,
    pub id_tracker: NameIdTracker,
}

impl FrozenSymtab {
    pub fn symtab(&self) -> &SymbolTable {
        &self.inner
    }

    pub fn new_name(&mut self, description: Path) -> NameID {
        NameID(self.id_tracker.next(), description)
    }

    /// Unfreeze the symtab, removing access to the underlying id_tracker and
    /// giving ownership of the symtab again
    pub fn unfreeze(self) -> SymbolTable {
        // Ensure that we will not generate any conflicting IDs by re combining
        // this with the new ID trakcer by ensuring that the new ID tracker is further
        // along than the symtabs
        SymbolTable {
            id_tracker: self.id_tracker,
            ..self.inner
        }
    }
}
