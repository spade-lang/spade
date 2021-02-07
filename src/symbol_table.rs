use crate::location_info::Loc;
use crate::{
    ast::{Identifier, Path},
    hir::{EntityHead, NameID, TypeParam},
    id_tracker::IdTracker,
    location_info::WithLocation,
    types::Type,
};
use std::collections::HashMap;
use thiserror::Error;

#[derive(Error, Debug, Clone, PartialEq)]
pub enum Error {
    #[error("No such symbol")]
    NoSuchSymbol(Loc<Path>),
    #[error("Not a type symbol")]
    NotATypeSymbol(Loc<Path>, Thing),
    #[error("Not a variable")]
    NotAVariable(Loc<Path>, Thing),
}

#[derive(PartialEq, Debug, Clone)]
pub struct FunctionDecl {
    pub name: Loc<Identifier>,
    pub self_arg: Option<Loc<()>>,
    pub inputs: Vec<(Loc<Identifier>, Loc<Type>)>,
    pub output_type: Loc<Type>,
}
impl WithLocation for FunctionDecl {}

#[derive(PartialEq, Debug, Clone)]
pub struct TraitDef {
    pub functions: Vec<Loc<FunctionDecl>>,
}
impl WithLocation for TraitDef {}

/// Any named thing in the language
#[derive(PartialEq, Debug, Clone)]
pub enum Thing {
    /// Defintion of a named type
    Type(TypeSymbol),
    TraitDef(Loc<TraitDef>),
    Entity(Loc<EntityHead>),
    Variable(Loc<Identifier>),
}

impl Thing {
    pub fn kind_string(&self) -> &'static str {
        match self {
            Thing::Type(_) => "type",
            Thing::TraitDef(_) => "trait definition",
            Thing::Entity(_) => "entity",
            Thing::Variable(_) => "variable",
        }
    }

    pub fn loc(&self) -> Loc<()> {
        match self {
            Thing::Type(TypeSymbol::Alias(i)) => i.loc(),
            Thing::Type(TypeSymbol::Param(i)) => i.loc(),
            Thing::TraitDef(i) => i.loc(),
            Thing::Entity(i) => i.loc(),
            Thing::Variable(i) => i.loc(),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum TypeSymbol {
    Alias(Loc<Type>),
    Param(Loc<TypeParam>),
}

/// A table of the symbols known to the program in the current scope. Names
/// are mapped to IDs which are then mapped to the actual things
pub struct SymbolTable {
    /// Each outer vec is a scope, inner vecs are symbols in that scope
    symbols: Vec<HashMap<Path, NameID>>,
    id_tracker: IdTracker,
    items: HashMap<NameID, Thing>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            symbols: vec![HashMap::new()],
            id_tracker: IdTracker::new(),
            items: HashMap::new(),
        }
    }
    pub fn new_scope(&mut self) {
        self.symbols.push(HashMap::new())
    }

    pub fn close_scope(&mut self) {
        self.symbols.pop();
    }

    pub fn add_thing(&mut self, name: Path, item: Thing) -> NameID {
        let id = self.id_tracker.next();
        // TODO (performance): we might want to not make this a hash map since it will require
        // a whole bunch of hashing
        let name_id = NameID(id, name.clone());
        self.items.insert(name_id.clone(), item);

        self.symbols
            .last_mut()
            .expect("At least one scope must be present to add a symbol")
            .insert(name, name_id.clone());

        name_id
    }

    pub fn lookup_id(&self, name: &Loc<Path>) -> Result<NameID, Error> {
        for tab in self.symbols.iter().rev() {
            if let Some(id) = tab.get(&name) {
                return Ok(id.clone());
            }
        }
        Err(Error::NoSuchSymbol(name.clone()))
    }

    pub fn lookyp_type_symbol(&self, name: &Loc<Path>) -> Result<(NameID, &TypeSymbol), Error> {
        let id = self.lookup_id(name)?;

        match self.items.get(&id).unwrap() {
            Thing::Type(t) => Ok((id, t)),
            other => Err(Error::NotATypeSymbol(name.clone(), other.clone())),
        }
    }

    pub fn lookup_variable(&self, name: &Loc<Path>) -> Result<NameID, Error> {
        let id = self.lookup_id(name)?;

        match self.items.get(&id).unwrap() {
            Thing::Variable(t) => Ok(id),
            other => Err(Error::NotAVariable(name.clone(), other.clone())),
        }
    }
}
