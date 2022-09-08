use spade_ast as ast;
use spade_common::{
    location_info::Loc,
    name::{Identifier, Path},
};
use spade_hir as hir;
use thiserror::Error;

pub enum ItemKind {
    Pipeline,
    Entity,
}

#[derive(Error, Debug, PartialEq, Clone)]
pub enum Error {
    #[error("Lookup error")]
    LookupError(#[from] spade_hir::symbol_table::LookupError),
    #[error("Declaration error")]
    DeclarationError(#[from] spade_hir::symbol_table::DeclarationError),
    #[error("Uniqueness error")]
    UniquenessError(#[from] spade_hir::symbol_table::UniqueNameError),
    #[error("Argument error")]
    ArgumentError(#[from] spade_hir::param_util::ArgumentError),
    #[error("Duplicate argument")]
    DuplicateArgument {
        new: Loc<Identifier>,
        prev: Loc<Identifier>,
    },
    #[error("Duplicate type variable")]
    DuplicateTypeVariable {
        found: Loc<Identifier>,
        previously: Loc<Identifier>,
    },
    #[error("Duplicate enum option")]
    DuplicateEnumOption {
        new: Loc<Identifier>,
        prev: Loc<Identifier>,
    },
    #[error("Non-port in port struct")]
    NonPortInPortStruct {
        type_spec: Loc<()>,
        port_keyword: Loc<()>,
        field: Loc<Identifier>,
    },
    #[error("Non-port in port struct")]
    PortInNonPortStruct {
        struct_name: Loc<Identifier>,
        type_spec: Loc<()>,
    },
    #[error("Port in enum")]
    PortInEnum {
        enum_name: Loc<Identifier>,
        type_spec: Loc<()>,
    },
    #[error("Non port in port tuple")]
    NonPortInPortTuple {
        offending_type: Loc<()>,
        port_witness: Loc<()>,
    },
    #[error("Aire of port")]
    WireOfPort {
        full_type: Loc<()>,
        inner_type: Loc<()>,
    },
    #[error("Pattern list length mismatch, expected {expected} arguments, got {got}")]
    PatternListLengthMismatch {
        expected: usize,
        got: usize,
        at: Loc<()>,
    },
    #[error("Incorrect stage count")]
    IncorrectStageCount {
        got: usize,
        expected: Loc<u128>,
        pipeline: Loc<ast::Pipeline>,
    },
    #[error("Early pipeline return")]
    EarlyPipelineReturn { expression: Loc<hir::Expression> },
    #[error("Pipeline depth mismatch")]
    PipelineDepthMismatch { expected: usize, got: Loc<u128> },
    #[error("Pipeline missing clock")]
    MissingPipelineClock { at_loc: Loc<()> },
    #[error("Referencing negative pipeline stage")]
    NegativePipelineReference {
        at_loc: Loc<()>,
        absolute_stage: i64,
    },
    #[error("Referencing out of bounds pipeline stage")]
    PipelineStageOOB {
        at_loc: Loc<()>,
        absolute_stage: usize,
        num_stages: usize,
    },
    #[error("Undefined pipeline stage")]
    UndefinedPipelineStage { stage: Loc<Identifier> },
    #[error("Duplicate pipeline stage")]
    DuplicatePipelineStage {
        stage: Loc<Identifier>,
        previous: Loc<Identifier>,
    },
    #[error("Multiple labels for same stage")]
    MultipleStageLabels {
        new: Loc<Identifier>,
        previous: Loc<Identifier>,
    },

    #[error("Declarations can only be defined by registers")]
    DeclarationOfNonReg {
        at: Loc<Identifier>,
        declaration_location: Loc<()>,
    },

    #[error("Variable declared but not defined")]
    UndefinedDeclaration(Loc<Identifier>),

    #[error("Redefinition of declaration")]
    RedefinitionOfDeclaration {
        at: Loc<Identifier>,
        previous: Loc<()>,
    },

    #[error("Unrecognised attribute")]
    UnrecognisedAttribute { attribute: Loc<Identifier> },

    #[error("Nomangle on generic")]
    NoMangleGeneric {
        attribute: Loc<Identifier>,
        generic_list: Loc<()>,
    },

    #[error("Match block has no arms")]
    NoMatchArms { body: Loc<()> },

    // Type related errors
    #[error("Generic parameters for generic name")]
    GenericsGivenForGeneric {
        at_loc: Loc<()>,
        for_type: Loc<Path>,
    },
}

pub type Result<T> = std::result::Result<T, Error>;
