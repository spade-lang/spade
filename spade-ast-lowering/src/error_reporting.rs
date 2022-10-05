use crate::Error;
use codespan_reporting::diagnostic::{Diagnostic, Suggestion, SuggestionPart};
use codespan_reporting::term::{self, termcolor::Buffer};
use spade_common::error_reporting::{codespan_config, AsLabel, CodeBundle, CompilationError};
use spade_hir::symbol_table::{DeclarationError, UniqueNameError};

impl CompilationError for Error {
    fn report(&self, buffer: &mut Buffer, code: &CodeBundle) {
        match self {
            Error::ArgumentError(e) => {
                e.report(buffer, code);
                return;
            }
            Error::LookupError(e) => {
                e.report(buffer, code);
                return;
            }
            _ => {}
        }
        let diag = match self {
            Error::ArgumentError(_) | Error::LookupError(_) => unreachable!("Already handled"),
            Error::DuplicateTypeVariable { found, previously } => Diagnostic::error()
                .with_message(format!("Duplicate typename: `{}`", found.inner))
                .with_labels(vec![
                    found.primary_label().with_message("Duplicate typename"),
                    previously
                        .secondary_label()
                        .with_message("Previously used here"),
                ]),
            Error::DeclarationError(DeclarationError::DuplicateDeclaration { old, new }) => {
                Diagnostic::error()
                    .with_message(format!("A previous declaration of {} exists", new))
                    .with_labels(vec![
                        new.primary_label()
                            .with_message(format!("{} was declared more than once", new)),
                        old.primary_label()
                            .with_message(format!("Previously declared here")),
                    ])
            }
            Error::UniquenessError(UniqueNameError::MultipleDefinitions { new, prev }) => {
                Diagnostic::error()
                    .with_message(format!("Multiple definitions of {new}"))
                    .with_labels(vec![
                        new.primary_label()
                            .with_message(format!("Multiple items named {new}")),
                        prev.secondary_label()
                            .with_message(format!("Previous definition here")),
                    ])
            }
            Self::DuplicateArgument { new, prev } => Diagnostic::error()
                .with_message(format!("Multiple arguments called {}", new))
                .with_labels(vec![
                    new.primary_label()
                        .with_message(format!("{} is an argument more than once", new)),
                    prev.secondary_label()
                        .with_message(format!("Previously declared here")),
                ]),
            Error::DuplicateEnumOption { new, prev } => Diagnostic::error()
                .with_message(format!("Multiple options called {}", new))
                .with_labels(vec![
                    new.primary_label()
                        .with_message(format!("{} is an option more than once", new)),
                    prev.secondary_label()
                        .with_message(format!("Previously declared here")),
                ]),
            Error::PatternListLengthMismatch { expected, got, at } => Diagnostic::error()
                .with_message(format!("Expected {} arguments, got {}", expected, got))
                .with_labels(vec![at
                    .primary_label()
                    .with_message(format!("Expected {} arguments", expected))]),
            Error::NonPortInPortStruct {
                type_spec,
                port_keyword,
                field,
            } => Diagnostic::error()
                .with_message(format!("Non-port in port struct"))
                .with_labels(vec![
                    type_spec
                        .primary_label()
                        .with_message("This is not a port type"),
                    port_keyword
                        .secondary_label()
                        .with_message("All members of a port must be ports"),
                ])
                .with_suggestions(vec![Suggestion {
                    file_id: port_keyword.file_id,
                    message: format!("Consider making {field} a wire"),
                    parts: vec![SuggestionPart {
                        range: type_spec.span().start..type_spec.span().start,
                        replacement: format!("&"),
                    }],
                }]),
            Error::PortInNonPortStruct {
                struct_name,
                type_spec,
            } => Diagnostic::error()
                .with_message(format!("Port in non-port struct"))
                .with_labels(vec![type_spec
                    .primary_label()
                    .with_message("This is a port")])
                .with_suggestions(vec![Suggestion {
                    file_id: struct_name.file_id,
                    message: format!("Consider making {struct_name} a port"),
                    parts: vec![SuggestionPart {
                        range: struct_name.span().start..struct_name.span().start,
                        replacement: format!("port "),
                    }],
                }]),
            Error::PortInEnum {
                enum_name,
                type_spec,
            } => Diagnostic::error()
                .with_message(format!("Port in enum"))
                .with_labels(vec![
                    type_spec.primary_label().with_message("This is a port"),
                    enum_name.secondary_label().with_message("This is an enum"),
                ]),
            Error::NonPortInPortTuple {
                offending_type,
                port_witness,
            } => Diagnostic::error()
                .with_message(format!("Can not mix ports and non-ports in a tuple"))
                .with_labels(vec![
                    offending_type
                        .primary_label()
                        .with_message("This is not a port"),
                    port_witness
                        .secondary_label()
                        .with_message("This is a port"),
                ])
                .with_notes(vec![format!(
                    "A tuple must either be all ports or no ports"
                )]),
            Error::WireOfPort {
                full_type,
                inner_type,
            } => Diagnostic::error()
                .with_message(format!("Can not create a wire of ports"))
                .with_labels(vec![
                    full_type
                        .primary_label()
                        .with_message("This can not be a wire"),
                    inner_type.secondary_label().with_message("This is a port"),
                ]),
            Error::IncorrectStageCount {
                got,
                expected,
                pipeline,
            } => Diagnostic::error()
                .with_message(format!("Expected {} pipeline stages", expected))
                .with_labels(vec![
                    pipeline
                        .primary_label()
                        .with_message(format!("Found {} stages", got)),
                    expected
                        .secondary_label()
                        .with_message(format!("{} specified here", expected)),
                ]),
            Error::EarlyPipelineReturn { expression } => Diagnostic::error()
                .with_message(format!("Unexpected return expression"))
                .with_labels(vec![expression
                    .primary_label()
                    .with_message(format!("Did not expect an value in this stage"))])
                .with_notes(vec![format!(
                    "Only the last stage of a pipeline can return values"
                )]),
            Error::PipelineDepthMismatch { expected, got } => Diagnostic::error()
                .with_message(format!(
                    "Pipeline depth mismatch. Expected {} got {}",
                    expected, got
                ))
                .with_labels(vec![got
                    .primary_label()
                    .with_message(format!("Expected {}", expected))]),
            Error::MissingPipelineClock { at_loc } => Diagnostic::error()
                .with_message(format!("Missing clock argument."))
                .with_labels(vec![at_loc
                    .primary_label()
                    .with_message(format!("Expected clock argument"))])
                .with_notes(vec![format!("All pipelines take a clock as an argument")]),
            Error::NegativePipelineReference {
                at_loc,
                absolute_stage,
            } => Diagnostic::error()
                .with_message("Reference to negative pipeline stage")
                .with_labels(vec![at_loc.primary_label().with_message(format!(
                    "Reference to absolute stage {absolute_stage}"
                ))])
                .with_notes(vec![format!("Pipeline stages start at 0")]),
            Error::PipelineStageOOB {
                at_loc,
                num_stages,
                absolute_stage,
            } => Diagnostic::error()
                .with_message(format!("Pipeline does not have stage {absolute_stage}"))
                .with_labels(vec![at_loc
                    .primary_label()
                    .with_message(format!("Reference to stage {absolute_stage}"))])
                .with_notes(vec![format!("The pipeline only has {num_stages} stages")]),
            Error::UndefinedPipelineStage { stage } => Diagnostic::error()
                .with_message(format!("Undefined pipeline stage '{stage}'"))
                .with_labels(vec![stage
                    .primary_label()
                    .with_message(format!("Not a stage in this pipeline"))]),
            Error::DuplicatePipelineStage { stage, previous } => Diagnostic::error()
                .with_message(format!("Stage {stage} was already defined"))
                .with_labels(vec![
                    stage
                        .primary_label()
                        .with_message(format!("duplicate pipeline stage")),
                    previous
                        .secondary_label()
                        .with_message("Previous definition"),
                ]),
            Error::MultipleStageLabels { new, previous } => Diagnostic::error()
                .with_message(format!("Stage already has label {previous}"))
                .with_labels(vec![
                    new.primary_label().with_message(format!("Duplicate label")),
                    previous
                        .secondary_label()
                        .with_message(format!("Previously labeled here")),
                ]),
            Error::GenericsGivenForGeneric { at_loc, for_type } => Diagnostic::error()
                .with_message("Generic arguments given for a generic type")
                .with_labels(vec![at_loc
                    .primary_label()
                    .with_message(format!("{} is a generic type", for_type))])
                .with_notes(vec![format!(
                    "A generic argument can not have generic types"
                )]),
            Error::DeclarationOfNonReg {
                at,
                declaration_location,
            } => Diagnostic::error()
                .with_message("Declared variables can only be defined by registers")
                .with_labels(vec![
                    at.primary_label().with_message(format!("Not a register")),
                    declaration_location
                        .secondary_label()
                        .with_message(format!("{} declared here", at)),
                ]),
            Error::RedefinitionOfDeclaration { at, previous } => Diagnostic::error()
                .with_message(format!("{} was already defined", at))
                .with_labels(vec![
                    at.primary_label()
                        .with_message(format!("{} was defined previously", at)),
                    previous
                        .secondary_label()
                        .with_message(format!("previous definition")),
                ])
                .with_notes(vec![format!("Declared variables can only be defined once")]),
            Error::UndefinedDeclaration(name) => Diagnostic::error()
                .with_message(format!("{name} is declared but not defined"))
                .with_labels(vec![name
                    .primary_label()
                    .with_message("declaration without definition")])
                .with_notes(vec![format!(
                    "Consider defining {name} with a let or reg binding"
                )]),
            Error::UnrecognisedAttribute { attribute } => Diagnostic::error()
                .with_message("Unrecognised attribute")
                .with_labels(vec![attribute
                    .primary_label()
                    .with_message("Unrecognised attribute")]),
            Error::NoMangleGeneric {
                attribute,
                generic_list,
            } => Diagnostic::error()
                .with_message("no_mangle is not allowed on generic units")
                .with_labels(vec![
                    attribute.primary_label().with_message("Not allowed here"),
                    generic_list
                        .secondary_label()
                        .with_message("Because this unit is generic"),
                ]),
            Error::NoMatchArms { body } => Diagnostic::error()
                .with_message("Match body has no arms")
                .with_labels(vec![body.primary_label().with_message("Empty match body")]),
        };

        term::emit(buffer, &codespan_config(), &code.files, &diag).unwrap();
    }
}
