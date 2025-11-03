use spade_common::name::NameID;
use spade_hir::{Module, TraitDef, TypeDeclaration, UnitHead};

use crate::html::ItemKind;

#[derive(Debug)]
pub enum Item {
    Unit(UnitHead, bool),
    Type(TypeDeclaration),
    Module(Module),
    Trait(NameID, TraitDef),
}

impl Item {
    pub fn documentation(&self) -> &str {
        match self {
            Item::Unit(unit, _) => &unit.documentation,
            Item::Type(ty) => match &ty.kind {
                spade_hir::TypeDeclKind::Struct(st) => &st.documentation,
                spade_hir::TypeDeclKind::Enum(en) => &en.documentation,
                spade_hir::TypeDeclKind::Primitive(_) => "",
            },
            Item::Module(module) => &module.documentation,
            Item::Trait(_, _) => "",
        }
    }

    pub fn kind(&self) -> ItemKind {
        match self {
            Item::Unit(unit, _) => match unit.unit_kind.inner {
                spade_hir::UnitKind::Function(_) => ItemKind::Function,
                spade_hir::UnitKind::Entity => ItemKind::Entity,
                spade_hir::UnitKind::Pipeline { .. } => ItemKind::Pipeline,
            },
            Item::Type(ty) => match &ty.kind {
                spade_hir::TypeDeclKind::Struct(_) => ItemKind::Struct,
                spade_hir::TypeDeclKind::Enum(_) => ItemKind::Enum,
                spade_hir::TypeDeclKind::Primitive(_) => ItemKind::Primitive,
            },
            Item::Module(_) => ItemKind::Module,
            Item::Trait(_, _) => ItemKind::Trait,
        }
    }
}
