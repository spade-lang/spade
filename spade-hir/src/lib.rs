pub mod expression;
pub mod param_util;
pub mod symbol_table;
pub mod testutil;

use std::collections::{BTreeMap, HashMap};
use std::fmt::Formatter;

pub use expression::{Argument, ArgumentKind, ArgumentList, ExprKind, Expression};
use itertools::Itertools;
use num::BigInt;
use serde::{Deserialize, Serialize};
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, NameID, Path},
    num_ext::InfallibleToBigInt,
};
use spade_diagnostics::Diagnostic;
use spade_types::{meta_types::MetaType, PrimitiveType};

/**
  Representation of the language with most language constructs still present, with
  more correctness guaranatees than the AST, such as types actually existing.
*/

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct Block {
    pub statements: Vec<Loc<Statement>>,
    pub result: Option<Loc<Expression>>,
}
impl WithLocation for Block {}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct PatternArgument {
    pub target: Loc<Identifier>,
    pub value: Loc<Pattern>,
    pub kind: ArgumentKind,
}
impl WithLocation for PatternArgument {}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum PatternKind {
    Integer(BigInt),
    Bool(bool),
    Name {
        name: Loc<NameID>,
        pre_declared: bool,
    },
    Tuple(Vec<Loc<Pattern>>),
    Array(Vec<Loc<Pattern>>),
    /// Instantiation of an entity. While the argument contains information about
    /// argument names, for codegen purposes, the arguments must be ordered in
    /// the target order. I.e. they should all act as positioanl arguments
    Type(Loc<NameID>, Vec<PatternArgument>),
}
impl PatternKind {
    pub fn name(name: Loc<NameID>) -> Self {
        PatternKind::Name {
            name,
            pre_declared: false,
        }
    }

    pub fn integer(val: i32) -> Self {
        Self::Integer(val.to_bigint())
    }
}
impl PatternKind {
    pub fn with_id(self, id: u64) -> Pattern {
        Pattern { id, kind: self }
    }

    pub fn idless(self) -> Pattern {
        Pattern { id: 0, kind: self }
    }
}
impl std::fmt::Display for PatternKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PatternKind::Integer(val) => write!(f, "{val}"),
            PatternKind::Bool(val) => write!(f, "{val}"),
            PatternKind::Name { name, .. } => write!(f, "{name}"),
            PatternKind::Tuple(members) => {
                write!(
                    f,
                    "({})",
                    members.iter().map(|m| format!("{}", m.kind)).join(", ")
                )
            }
            PatternKind::Array(members) => {
                write!(
                    f,
                    "[{}]",
                    members.iter().map(|m| format!("{}", m.kind)).join(", ")
                )
            }
            PatternKind::Type(name, _) => write!(f, "{name}(..)"),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Pattern {
    // Unique ID of the pattern for use in type inference. Shared with expressions
    // meaning there are no expression/pattern id collisions
    pub id: u64,
    pub kind: PatternKind,
}
impl WithLocation for Pattern {}

impl Pattern {
    pub fn get_names(&self) -> Vec<Loc<NameID>> {
        match &self.kind {
            PatternKind::Integer(_) => vec![],
            PatternKind::Bool(_) => vec![],
            PatternKind::Name {
                name,
                pre_declared: _,
            } => vec![name.clone()],
            PatternKind::Tuple(inner) => inner.iter().flat_map(|i| i.get_names()).collect(),
            PatternKind::Type(_, args) => {
                args.iter().flat_map(|arg| arg.value.get_names()).collect()
            }
            PatternKind::Array(inner) => inner.iter().flat_map(|i| i.get_names()).collect(),
        }
    }
}

impl PartialEq for Pattern {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct WalTrace {
    pub clk: Option<Loc<Expression>>,
    pub rst: Option<Loc<Expression>>,
}
impl WithLocation for WalTrace {}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct Binding {
    pub pattern: Loc<Pattern>,
    pub ty: Option<Loc<TypeSpec>>,
    pub value: Loc<Expression>,
    // Specifies if a wal_trace mir node should be emitted for this struct. If this
    // is present, the type is traceable
    pub wal_trace: Option<Loc<WalTrace>>,
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum PipelineRegMarkerExtra {
    Condition(Loc<Expression>),
    Count {
        count: Loc<TypeExpression>,
        count_typeexpr_id: u64,
    },
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum Statement {
    Binding(Binding),
    Register(Register),
    Declaration(Vec<Loc<NameID>>),
    PipelineRegMarker(Option<PipelineRegMarkerExtra>),
    Label(Loc<NameID>),
    Assert(Loc<Expression>),
    Set {
        target: Loc<Expression>,
        value: Loc<Expression>,
    },
    WalSuffixed {
        suffix: Identifier,
        target: Loc<NameID>,
    },
}
impl WithLocation for Statement {}

impl Statement {
    /// NOTE: For use in tests
    pub fn named_let(pattern_id: u64, name_id: Loc<NameID>, val: Expression) -> Self {
        Self::Binding(Binding {
            pattern: PatternKind::name(name_id).with_id(pattern_id).nowhere(),
            ty: None,
            value: val.nowhere(),
            wal_trace: None,
        })
    }

    pub fn binding(
        pattern: Loc<Pattern>,
        ty: Option<Loc<TypeSpec>>,
        value: Loc<Expression>,
    ) -> Statement {
        Statement::Binding(Binding {
            pattern,
            ty,
            value,
            wal_trace: None,
        })
    }
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct Register {
    pub pattern: Loc<Pattern>,
    pub clock: Loc<Expression>,
    pub reset: Option<(Loc<Expression>, Loc<Expression>)>,
    pub initial: Option<Loc<Expression>>,
    pub value: Loc<Expression>,
    pub value_type: Option<Loc<TypeSpec>>,
    pub attributes: AttributeList,
}
impl WithLocation for Register {}

#[derive(PartialEq, Debug, Clone, PartialOrd, Eq, Ord, Serialize, Deserialize)]
pub struct Module {
    pub name: Loc<NameID>,
}

/// Type params have both an identifier and a NameID since they go through the
/// ast lowering process in a few separate steps, and the identifier needs to be
/// re-added to the symtab multiple times
#[derive(PartialEq, Debug, Clone, Hash, Eq, Serialize, Deserialize)]
pub struct TypeParam {
    pub ident: Loc<Identifier>,
    pub name_id: NameID,
    pub trait_bounds: Vec<Loc<TraitSpec>>,
    pub meta: MetaType,
}
impl WithLocation for TypeParam {}
impl TypeParam {
    pub fn name_id(&self) -> NameID {
        self.name_id.clone()
    }
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize, Hash, Eq)]
pub enum TypeExpression {
    /// An integer value
    Integer(BigInt),
    /// Another type
    TypeSpec(TypeSpec),
    ConstGeneric(Loc<ConstGeneric>),
}
impl WithLocation for TypeExpression {}

impl std::fmt::Display for TypeExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeExpression::Integer(val) => write!(f, "{val}"),
            TypeExpression::TypeSpec(val) => write!(f, "{val}"),
            TypeExpression::ConstGeneric(val) => write!(f, "{val}"),
        }
    }
}

/// A specification of a type to be used. For example, the types of input/output arguments the type
/// of fields in a struct etc.
#[derive(PartialEq, Debug, Clone, Serialize, Deserialize, Hash, Eq)]
pub enum TypeSpec {
    /// The type is a declared type (struct, enum, typedef etc.) with n arguments
    Declared(Loc<NameID>, Vec<Loc<TypeExpression>>),
    /// The type is a generic argument visible in the current scope
    Generic(Loc<NameID>),
    /// The type is a tuple of other variables
    Tuple(Vec<Loc<TypeSpec>>),
    Array {
        inner: Box<Loc<TypeSpec>>,
        size: Box<Loc<TypeExpression>>,
    },
    Unit(Loc<()>),
    Inverted(Box<Loc<TypeSpec>>),
    Wire(Box<Loc<TypeSpec>>),
    /// The type of the `self` parameter in a trait method spec. Should not
    /// occur in non-traits. The Loc is only used for diag_bails, so an approximate
    /// reference is fine.
    TraitSelf(Loc<()>),
    /// A wildcard, cannot occur everywhere, but ast lowering enusres that wildcards are valid,
    /// i.e. it is safe to emit a Diagnostic::bug if this is encountered where it is invalid
    Wildcard,
}
impl WithLocation for TypeSpec {}

// Quick functions for creating types without typing so much
impl TypeSpec {
    pub fn unit() -> Self {
        TypeSpec::Unit(().nowhere())
    }
}

impl std::fmt::Display for TypeSpec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            TypeSpec::Declared(name, params) => {
                let type_params = if params.is_empty() {
                    String::from("")
                } else {
                    format!(
                        "<{}>",
                        params
                            .iter()
                            .map(|g| format!("{g}"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                };
                format!("{name}{type_params}")
            }
            TypeSpec::Generic(name) => format!("{name}"),
            TypeSpec::Tuple(members) => {
                format!(
                    "({})",
                    members
                        .iter()
                        .map(|m| format!("{m}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            TypeSpec::Array { inner, size } => format!("[{inner}; {size}]"),
            TypeSpec::Unit(_) => "()".into(),
            TypeSpec::Inverted(inner) => format!("~{inner}"),
            TypeSpec::Wire(inner) => format!("&{inner}"),
            TypeSpec::TraitSelf(_) => "Self".into(),
            TypeSpec::Wildcard => "_".into(),
        };
        write!(f, "{str}")
    }
}

/// A specification of a trait with type parameters
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, Hash, Eq)]
pub struct TraitSpec {
    pub name: TraitName,
    pub type_params: Option<Loc<Vec<Loc<TypeExpression>>>>,
}
impl WithLocation for TraitSpec {}

/// Declaration of an enum
#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct Enum {
    pub options: Vec<(Loc<NameID>, Loc<ParameterList>)>,
}
impl WithLocation for Enum {}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct WalTraceable {
    pub suffix: Path,
    pub uses_clk: bool,
    pub uses_rst: bool,
}
impl WithLocation for WalTraceable {}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct Struct {
    pub members: Loc<ParameterList>,
    pub is_port: bool,
    pub attributes: AttributeList,
    pub wal_traceable: Option<Loc<WalTraceable>>,
}
impl WithLocation for Struct {}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum TypeDeclKind {
    Enum(Loc<Enum>),
    Primitive(PrimitiveType),
    Struct(Loc<Struct>),
}
impl TypeDeclKind {
    pub fn name(&self) -> &str {
        match self {
            TypeDeclKind::Enum(_) => "enum",
            TypeDeclKind::Primitive(_) => "primitive",
            TypeDeclKind::Struct(_) => "struct",
        }
    }
}

/// A declaration of a new type
#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct TypeDeclaration {
    pub name: Loc<NameID>,
    pub kind: TypeDeclKind,
    pub generic_args: Vec<Loc<TypeParam>>,
}
impl WithLocation for TypeDeclaration {}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize, Hash, Eq)]
pub enum ConstGeneric {
    Name(Loc<NameID>),
    Const(BigInt),
    Add(Box<Loc<ConstGeneric>>, Box<Loc<ConstGeneric>>),
    Sub(Box<Loc<ConstGeneric>>, Box<Loc<ConstGeneric>>),
    Mul(Box<Loc<ConstGeneric>>, Box<Loc<ConstGeneric>>),
    UintBitsToFit(Box<Loc<ConstGeneric>>),
}
impl WithLocation for ConstGeneric {}

impl ConstGeneric {
    pub fn with_id(self, id: u64) -> ConstGenericWithId {
        ConstGenericWithId { id, inner: self }
    }
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct ConstGenericWithId {
    pub id: u64,
    pub inner: ConstGeneric,
}
impl WithLocation for ConstGenericWithId {}

impl std::fmt::Display for ConstGeneric {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstGeneric::Name(n) => write!(f, "{n}"),
            ConstGeneric::Const(val) => write!(f, "{val}"),
            ConstGeneric::Add(l, r) => write!(f, "({l} + {r})"),
            ConstGeneric::Sub(l, r) => write!(f, "({l} - {r})"),
            ConstGeneric::Mul(l, r) => write!(f, "({l} * {r})"),
            ConstGeneric::UintBitsToFit(a) => write!(f, "uint_bits_to_fit({a})"),
        }
    }
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize, Hash, Eq)]
pub enum WhereClause {
    Int {
        target: Loc<NameID>,
        constraint: Loc<ConstGeneric>,
    },
    Type {
        target: Loc<NameID>,
        traits: Vec<Loc<TraitSpec>>,
    },
}
impl WithLocation for WhereClause {}

impl std::fmt::Display for WhereClause {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            WhereClause::Int { target, constraint } => {
                format!("{target}: {{ {constraint} }}")
            }
            WhereClause::Type { target, traits } => {
                format!(
                    "{target}: {}",
                    traits.iter().map(|trait_spec| &trait_spec.name).join(" + ")
                )
            }
        };
        write!(f, "{}", str)
    }
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize, Hash, Eq)]
pub enum UnitName {
    /// The name will be mangled down to contain the NameID in order to ensure
    /// uniqueness. Emitted by generic functions
    WithID(Loc<NameID>),
    /// The name will contain the full path to the name but the ID section of the
    /// nameID will not be included. Used by non-generic functions
    FullPath(Loc<NameID>),
    /// The name will not be mangled. In the output code it will appear as String
    /// but the compiler will still refer to it by the NameID
    Unmangled(String, Loc<NameID>),
}

impl UnitName {
    pub fn name_id(&self) -> &Loc<NameID> {
        match self {
            UnitName::WithID(name) => name,
            UnitName::FullPath(name) => name,
            UnitName::Unmangled(_, name) => name,
        }
    }
}

impl std::fmt::Display for UnitName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnitName::WithID(name) | UnitName::FullPath(name) | UnitName::Unmangled(_, name) => {
                write!(f, "{name}")
            }
        }
    }
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct Unit {
    pub name: UnitName,
    pub head: UnitHead,
    pub attributes: AttributeList,
    // This is needed here because the head does not have NameIDs
    pub inputs: Vec<(Loc<NameID>, Loc<TypeSpec>)>,
    pub body: Loc<Expression>,
}
impl WithLocation for Unit {}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct Parameter {
    /// If the #[no_mangle] attribute is present, this field is set
    /// with the Loc pointing to the attribute
    pub no_mangle: Option<Loc<()>>,
    pub name: Loc<Identifier>,
    pub ty: Loc<TypeSpec>,
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct ParameterList(pub Vec<Parameter>);
impl WithLocation for ParameterList {}

impl ParameterList {
    pub fn argument_num(&self) -> usize {
        self.0.len()
    }

    /// Look up the type of an argument. Panics if no such argument exists
    pub fn arg_type(&self, name: &Identifier) -> &TypeSpec {
        if let Some(result) = self.try_get_arg_type(name) {
            result
        } else {
            panic!(
                "Tried to get type of an argument which is not part of the parameter list. {}",
                name
            )
        }
    }

    /// Look up the type of an argument, returning None if no such argument exists
    pub fn try_get_arg_type(&self, name: &Identifier) -> Option<&Loc<TypeSpec>> {
        for Parameter {
            name: arg,
            ty,
            no_mangle: _,
        } in &self.0
        {
            if &arg.inner == name {
                return Some(ty);
            }
        }
        None
    }

    pub fn arg_index(&self, target: &Identifier) -> Option<usize> {
        let indices = self
            .0
            .iter()
            .enumerate()
            .filter_map(
                |(
                    i,
                    Parameter {
                        name,
                        ty: _,
                        no_mangle: _,
                    },
                )| {
                    if &name.inner == target {
                        Some(i)
                    } else {
                        None
                    }
                },
            )
            .collect::<Vec<_>>();

        if indices.len() > 1 {
            panic!("Duplicate arguments with the same name")
        } else {
            indices.first().cloned()
        }
    }
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum FunctionKind {
    Fn,
    Struct,
    Enum,
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum UnitKind {
    Function(FunctionKind),
    Entity,
    Pipeline {
        depth: Loc<TypeExpression>,
        depth_typeexpr_id: u64,
    },
}
impl WithLocation for UnitKind {}

impl UnitKind {
    pub fn name(&self) -> &'static str {
        match self {
            UnitKind::Function(FunctionKind::Fn) => "function",
            UnitKind::Function(FunctionKind::Struct) => "struct",
            UnitKind::Function(FunctionKind::Enum) => "enum variant",
            UnitKind::Entity => "entity",
            UnitKind::Pipeline { .. } => "pipeline",
        }
    }

    pub fn is_pipeline(&self) -> bool {
        matches!(self, UnitKind::Pipeline { .. })
    }
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct UnitHead {
    pub name: Loc<Identifier>,
    pub inputs: Loc<ParameterList>,
    pub output_type: Option<Loc<TypeSpec>>,
    pub unit_type_params: Vec<Loc<TypeParam>>,
    pub scope_type_params: Vec<Loc<TypeParam>>,
    pub unit_kind: Loc<UnitKind>,
    pub where_clauses: Vec<Loc<WhereClause>>,
}
impl WithLocation for UnitHead {}

impl UnitHead {
    pub fn output_type(&self) -> Loc<TypeSpec> {
        match &self.output_type {
            Some(t) => t.clone(),
            None => {
                // FIXME: We should point to the end of the argument list here
                TypeSpec::Unit(self.name.loc()).at_loc(&self.name.loc())
            }
        }
    }
    pub fn get_type_params(&self) -> Vec<Loc<TypeParam>> {
        self.unit_type_params
            .iter()
            .chain(self.scope_type_params.iter())
            .cloned()
            .collect_vec()
    }
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum Item {
    Unit(Loc<Unit>),
    Builtin(UnitName, Loc<UnitHead>),
}

impl Item {
    pub fn assume_unit(&self) -> &Unit {
        match self {
            Item::Unit(u) => &u.inner,
            Item::Builtin(_, _) => panic!("Expected unit, got builtin"),
        }
    }
}

/// Items which have associated code that can be executed. This is different from
/// type declarations which are items, but which do not have code on their own
#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum ExecutableItem {
    EnumInstance { base_enum: NameID, variant: usize },
    StructInstance,
    Unit(Loc<Unit>),
    BuiltinUnit(UnitName, Loc<UnitHead>),
}
impl WithLocation for ExecutableItem {}

pub type TypeList = HashMap<NameID, Loc<TypeDeclaration>>;

#[derive(Serialize, Deserialize, PartialEq, Eq, Hash, Debug, Clone, PartialOrd, Ord)]
pub enum TraitName {
    Named(Loc<NameID>),
    Anonymous(u64),
}

impl TraitName {
    pub fn is_anonymous(&self) -> bool {
        matches!(self, Self::Anonymous(_))
    }

    /// Returns the loc of the name of this trait, if it exists. None otherwise
    pub fn name_loc(&self) -> Option<Loc<NameID>> {
        match self {
            TraitName::Named(n) => Some(n.clone()),
            TraitName::Anonymous(_) => None,
        }
    }
}

impl std::fmt::Display for TraitName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TraitName::Named(n) => write!(f, "{n}"),
            TraitName::Anonymous(id) => write!(f, "Anonymous({id})"),
        }
    }
}

/// Attributes that are still present as attributes in the HIR. Not all AST
/// attributes are in this list, as some are consumed and inlined into the corresponding
/// ast node
#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum Attribute {
    Optimize { passes: Vec<Loc<String>> },
    Fsm { state: NameID },
    WalTraceable { suffix: Identifier },
}
impl Attribute {
    pub fn name(&self) -> &str {
        match self {
            Attribute::Optimize { passes: _ } => "optimize",
            Attribute::Fsm { state: _ } => "fsm",
            Attribute::WalTraceable { suffix: _ } => "suffix",
        }
    }
}
impl WithLocation for Attribute {}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct AttributeList(pub Vec<Loc<Attribute>>);

impl AttributeList {
    pub fn empty() -> Self {
        Self(vec![])
    }
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct ImplBlock {
    /// Mapping of identifiers to the NameID of the entity which is the implementation
    /// for the specified function
    pub fns: HashMap<Identifier, (NameID, Loc<()>)>,
    pub type_params: Vec<Loc<TypeParam>>,
    pub target: Loc<TypeSpec>,
    pub id: u64,
}
impl WithLocation for ImplBlock {}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct TraitDef {
    pub type_params: Option<Loc<Vec<Loc<TypeParam>>>>,
    pub fns: HashMap<Identifier, UnitHead>,
}
impl WithLocation for TraitDef {}

#[derive(PartialEq, Hash, Eq, Debug, Clone, Serialize, Deserialize)]
pub enum ImplTarget {
    Array,
    Inverted,
    Wire,
    Named(NameID),
}

impl ImplTarget {
    pub fn display(&self, args: &[TypeExpression]) -> String {
        match self {
            ImplTarget::Array => {
                format!(
                    "[{}; {}]",
                    args.get(0)
                        .map(|a| format!("{}", a))
                        .unwrap_or_else(|| "<(bug) Missing param 0>".to_string()),
                    args.get(1)
                        .map(|a| format!("{}", a))
                        .unwrap_or_else(|| "<(bug) Missing param 1>".to_string())
                )
            }
            ImplTarget::Wire => {
                format!(
                    "&{}",
                    args.get(0)
                        .map(|a| format!("{}", a))
                        .unwrap_or_else(|| "<(bug) Missing param 0>".to_string()),
                )
            }
            ImplTarget::Inverted => {
                format!(
                    "inv {}",
                    args.get(0)
                        .map(|a| format!("{}", a))
                        .unwrap_or_else(|| "<(bug) Missing param 0>".to_string()),
                )
            }
            ImplTarget::Named(name) => {
                format!(
                    "{}{}",
                    name,
                    if args.is_empty() {
                        format!("")
                    } else {
                        format!("<{}>", args.iter().map(|arg| format!("{}", arg)).join(", "))
                    }
                )
            }
        }
    }
}

/// A list of all the items present in the whole AST, flattened to remove module
/// hierarchies.
///
/// That is, `mod a { mod b{ entity X {} } } will result in members containing `a::b::X`, but the
/// module hierarchy no longer has to be traversed.
///
/// The modules themselves however still exist in the `modules` set.
#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct ItemList {
    pub executables: BTreeMap<NameID, ExecutableItem>,
    pub types: TypeList,
    /// All modules, including empty ones.
    pub modules: BTreeMap<NameID, Module>,
    // FIXME: Support entities and pipelines as trait members.
    /// All traits in the compilation unit. Traits consist of a list of functions
    /// by name. Anonymous impl blocks are also members here, but their name is never
    /// visible to the user.
    pub traits: HashMap<TraitName, TraitDef>,
    pub impls: HashMap<ImplTarget, HashMap<(TraitName, Vec<TypeExpression>), Loc<ImplBlock>>>,
}

impl Default for ItemList {
    fn default() -> Self {
        Self::new()
    }
}

impl ItemList {
    pub fn new() -> Self {
        Self {
            executables: BTreeMap::new(),
            types: TypeList::new(),
            modules: BTreeMap::new(),
            traits: HashMap::new(),
            impls: HashMap::new(),
        }
    }

    pub fn add_executable(
        &mut self,
        name: Loc<NameID>,
        item: ExecutableItem,
    ) -> Result<(), Diagnostic> {
        if let Some(_) = self.executables.get_key_value(&name) {
            Err(
                Diagnostic::error(&name, format!("Multiple definitions of thing {name}"))
                    .primary_label("New definition"),
            )
        } else {
            self.executables.insert(name.inner, item);
            Ok(())
        }
    }

    pub fn add_trait(
        &mut self,
        name: TraitName,
        type_params: Option<Loc<Vec<Loc<TypeParam>>>>,
        members: Vec<(Identifier, UnitHead)>,
    ) -> Result<(), Diagnostic> {
        if let Some((prev, _)) = self.traits.get_key_value(&name) {
            Err(
                // NOTE: unwrap here is safe *unless* we have got duplicate trait IDs which
                // means we have bigger problems
                Diagnostic::error(
                    name.name_loc().unwrap(),
                    format!("Multiple definitions of trait {name}"),
                )
                .primary_label("New definition")
                .secondary_label(prev.name_loc().unwrap(), "Previous definition"),
            )
        } else {
            self.traits.insert(
                name,
                TraitDef {
                    type_params,
                    fns: members.into_iter().collect(),
                },
            );
            Ok(())
        }
    }

    pub fn get_trait(&self, name: &TraitName) -> Option<&TraitDef> {
        self.traits.get(name)
    }

    pub fn traits(&self) -> &HashMap<TraitName, TraitDef> {
        &self.traits
    }
}
