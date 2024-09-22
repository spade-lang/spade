# Changelog

All notable changes to this project will be documented in this file.

Spade is currently unstable and all 0.x releases are expected to contain
breaking changes. Releases are mainly symbolic and are done on a six-week
release cycle. Every six weeks, the current master branch is tagged and
released as a new version.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- [!346][!346] The parser can now recover from errors in statements and items
- [!346][!346] Add some additional diagnostics to missing `;`

### Changed

- [!346][!346] *Breaking change* Removed the `$comptime` system

### Fixed

[!346]: https://gitlab.com/spade-lang/spade/-/merge_requests/346

## [0.10.0] - 2024-09-19

### Added

- [!325][!325] Add `to_uint`, `bits` and `to_int` methods to `int` and `uint`.
- [!326][!326] Add pattern matching for arrays
- [!329][!329] Add turbofish (`::<>`) to methods
- [!335][!335] Add array shorthand literal syntax (`[0x10; 24]`)
- [!339][!339] Allow wildcards (`_`) in turbofish and type specifications on bindings
- [!339][!339] Allow const generics (`{a + b}` etc.) in turbofish and type specifications on bindings
- [!339][!339] Add `-`, `*`, and `uint_bits_to_fit` as type expressions
- [!334][!334] Add `to_be_bytes` and `to_le_bytes` to `uint<16>`, `uint<24>` and `uint<32>`
- [!334][!334] Add `std::conv::concat_arrays`
- [!334][!334] Add `std::conv::concat_arrays`, `std::ports::new_mut_wire` and `std::ports::read_mut_wire` to the prelude
- [!345][!345] Add trait bounds (`T: Trait<T>`), these can be used in generic type definitions and `where` clauses
- [!345][!345] Allow `where` clauses with trait bounds or const generics on impl blocks

### Changed

- [!324][!324] Move `stdlib` and `prelude` directories to `spade-compiler`
- [!331][!331] Allow multiple same-named methods on the same type with different generic parameters
- [!343][!343] **Breaking change** Changed the syntax for integer type parameters to `#uint X` instead of `#X`
- [!343][!343] Add meta-types which differentiate between types, type level integers and type level unsigneds
- [!335][!335] Move pipeline depth computation into the types system to allow generically depthed pipelines
- [!345][!345] **Breaking change** Changed the syntax for generic integer constraints to `N: { M + 2 }` instead of `N: M + 2`

### Fixed

- [!338][!338] Fix panics in generic impl blocks
- [!342][!342] Fix negative integer literals on negative bound (`let a: int<3> = -4`)

[!324]: https://gitlab.com/spade-lang/spade/-/merge_requests/324
[!325]: https://gitlab.com/spade-lang/spade/-/merge_requests/325
[!326]: https://gitlab.com/spade-lang/spade/-/merge_requests/326
[!329]: https://gitlab.com/spade-lang/spade/-/merge_requests/329
[!331]: https://gitlab.com/spade-lang/spade/-/merge_requests/331
[!334]: https://gitlab.com/spade-lang/spade/-/merge_requests/334
[!335]: https://gitlab.com/spade-lang/spade/-/merge_requests/335
[!338]: https://gitlab.com/spade-lang/spade/-/merge_requests/338
[!339]: https://gitlab.com/spade-lang/spade/-/merge_requests/339
[!342]: https://gitlab.com/spade-lang/spade/-/merge_requests/342
[!343]: https://gitlab.com/spade-lang/spade/-/merge_requests/343
[!345]: https://gitlab.com/spade-lang/spade/-/merge_requests/345

## [0.9.0] - 2024-07-04

### Added

- [!304][!304] Allow specifying the bit width of integer literals as `512u32` or `123i64`
- [!307][!307] Allow specifying command line arguments via a json file
- [!308][!308] Add `/` and `%` for power of 2 operands, as well as `comb_div` and `comb_mod` for all operands
- [!309][!309] Add named argument turbofishes (`::$<>`)
- [!312][!312] Include a map of modules in `ItemList`
- [!271][!271] Add automatic clock gating of the `Option`-type
- [!319][!319] Add `where` clauses to allow specifying constraints on generic parameters
- [!322][!322] Add `==` operator to outputs in cocotb
- [!322][!322] Allow raw integers, booleans, and lists to be passed to inputs and outputs in cocotb.
- [!318][!318] Add generic traits, generic impls, `Option<T>::is_some()` and `Option<T>::is_none()`

### Changed

- [!314][!314] Cleanup `ItemList` merge and make trait impls inside modules work

### Fixed

- [!321][!321] Fix codegen for enums with a single variant

### Removed

[!271]: https://gitlab.com/spade-lang/spade/-/merge_requests/271
[!304]: https://gitlab.com/spade-lang/spade/-/merge_requests/304
[!307]: https://gitlab.com/spade-lang/spade/-/merge_requests/307
[!308]: https://gitlab.com/spade-lang/spade/-/merge_requests/308
[!309]: https://gitlab.com/spade-lang/spade/-/merge_requests/309
[!312]: https://gitlab.com/spade-lang/spade/-/merge_requests/312
[!314]: https://gitlab.com/spade-lang/spade/-/merge_requests/314
[!318]: https://gitlab.com/spade-lang/spade/-/merge_requests/318
[!319]: https://gitlab.com/spade-lang/spade/-/merge_requests/319
[!321]: https://gitlab.com/spade-lang/spade/-/merge_requests/321
[!322]: https://gitlab.com/spade-lang/spade/-/merge_requests/322

## [0.8.0] - 2024-05-14

### Added

- [!288][!288] Implement binary reduction operations in std::ops
- [!290][!290] Add higher level memory primitives to `std::mem`
- [!290][!290] Add clock domain crossing primitives to `std::cdc`
- [!293][!293] Add `inout<T>` for mapping to Verilog `inout` ports
- [!294][!294] Add `.spade_repr()` to output fields in Verilator
- [!303][!303] Add `Self` type in traits and impl blocks

### Changed

- [!244][!244] spade-python now supports units which return `void`

### Fixed

- [!291][!291] Fix long runtime of pattern refutability checks for large arrays and tuples
- [!297][!297] Fix panic when passing modules with reserved keywords as name (it is still a normal error)
- [!300][!300] Fix expected `stage.ready` or `stage.valid` diagnostic
- [!299][!299] Pipeline References now work in blocks
- [!299][!299] Prevent Pipeline references from laundering variables before they were declared

[!244]: https://gitlab.com/spade-lang/spade/-/merge_requests/244
[!288]: https://gitlab.com/spade-lang/spade/-/merge_requests/288
[!290]: https://gitlab.com/spade-lang/spade/-/merge_requests/290
[!291]: https://gitlab.com/spade-lang/spade/-/merge_requests/291
[!293]: https://gitlab.com/spade-lang/spade/-/merge_requests/293
[!294]: https://gitlab.com/spade-lang/spade/-/merge_requests/294
[!297]: https://gitlab.com/spade-lang/spade/-/merge_requests/297
[!299]: https://gitlab.com/spade-lang/spade/-/merge_requests/299
[!300]: https://gitlab.com/spade-lang/spade/-/merge_requests/300
[!303]: https://gitlab.com/spade-lang/spade/-/merge_requests/303

## [0.7.0] - 2024-03-21

### Added

- [!266][!266] Provide more information when type inference fails during monomorphisation
- [!276][!276] Allow using the values of generic number parameters as expressions
- [!285][!285] Add `std::ops::gray_to_bin` and `std::ops::bin_to_gray`

### Changed

- [!281][!281] Moved parser diagnostics to new diagnostics system

### Fixed

- [!272][!272] Parentheses can now be omitted on aliased enum variants like `None`
- [!273][!273] Allow bitwise negation (~) of unsigned integers
- [!277][!277] Passing too many types to a turbofish operator now produces an error instead of panicking
- [!275][!275] Fix parsing of subtraction without spaces, like `1-2`
- [!278][!278] Confirm correct number of generic parameters

### Removed

[!266]: https://gitlab.com/spade-lang/spade/-/merge_requests/266
[!272]: https://gitlab.com/spade-lang/spade/-/merge_requests/272
[!273]: https://gitlab.com/spade-lang/spade/-/merge_requests/273
[!275]: https://gitlab.com/spade-lang/spade/-/merge_requests/275
[!276]: https://gitlab.com/spade-lang/spade/-/merge_requests/276
[!278]: https://gitlab.com/spade-lang/spade/-/merge_requests/278
[!281]: https://gitlab.com/spade-lang/spade/-/merge_requests/281
[!285]: https://gitlab.com/spade-lang/spade/-/merge_requests/285
[!277]: https://gitlab.com/spade-lang/spade/-/merge_requests/277

## [0.6.0] - 2024-01-03

### Added

- [!251][!251] Allow instantiating single variant enums without `()`
- [!252][!252] Added block comments delimited by `/*` `*/`
- [!254][!254] Added `std::conv::unsafe::unsafe_cast` for converting between types. Also added `std::conv::int_to_bits`, `std::conv::bits_to_int` for safe conversions.
- [!254][!254] Added `std::conv::flip_array`
- [!255][!255] Add range indexing to arrays. You can now access parts of arrays using `a[start:end]`
- [!262][!262] Add `uint<#N>` for unsigned integers. Adjusted stdlib accordingly
- [!263][!263] Allow specifying type parameters for Units using turbofish (`::<>`) syntax. For example `trunc::<10, 5>(x)`

### Changed

- [!260][!260] Instantiation parameters are now passed by name, which makes interaction with external verilog easier.
- [!262][!262] **Breaking change**: Integers with `u` suffixes now have no effect, use unsigned types instead.

[!251]: https://gitlab.com/spade-lang/spade/-/merge_requests/251
[!252]: https://gitlab.com/spade-lang/spade/-/merge_requests/252
[!254]: https://gitlab.com/spade-lang/spade/-/merge_requests/254
[!255]: https://gitlab.com/spade-lang/spade/-/merge_requests/255
[!260]: https://gitlab.com/spade-lang/spade/-/merge_requests/260
[!262]: https://gitlab.com/spade-lang/spade/-/merge_requests/262
[!263]: https://gitlab.com/spade-lang/spade/-/merge_requests/263

## [0.5.0] - 2023-11-17

### Added

- [!232][!232] Support for implementing traits
- Started adding a language reference documentation section where all language
  features will be described.
  <https://docs.spade-lang.org/language_reference/index.html>

### Fixed

- [!224][!224] `stage.valid` now does what it is supposed to
- [!235][!235] Workaround for vivado not supporting escaped identifiers called `new`
- [!239][!239] Codegen: Don't generate a source reference attribute for non-existent void values
- [!241][!241] Fix panic on zero-sized-type in pipeline

### Changed

- [!224][!224] Name de-aliasing now only de-aliases anonymous names
- [!232][!232] **Breaking change** Bump minimum rust version to 1.70

[!232]: https://gitlab.com/spade-lang/spade/-/merge_requests/232
[!224]: https://gitlab.com/spade-lang/spade/-/merge_requests/224
[!235]: https://gitlab.com/spade-lang/spade/-/merge_requests/235
[!239]: https://gitlab.com/spade-lang/spade/-/merge_requests/239
[!241]: https://gitlab.com/spade-lang/spade/-/merge_requests/241

## [0.4.0] - 2023-08-24

### Added

- [!216][!216] Support initial values for registers
- [!217][!217] Allow writing units that don't return a value.

### Fixed

- [!202][!202] Re-add missing requirement for the first argument of a pipeline to be a clock
- [!205][!205] Fix panic on method calls in let bindings
- [!206][!206] Re-add working VCD translation. It now also translates more values
- [!215][!215] Make generated code compile out of the box with verilator
- [!221][!221] Fix code generation bug when matching two variant enums

### Changed

- [!207][!207] Rename `wal_suffix` attribute to `wal_traceable`. It now defaults to the struct name as a suffix, but can override that using the `suffix` parameter to the attribute.
- [!209][!209] Add a new `#[wal_suffix]` attribute which emits a copy of the marked signal with a specific suffix. Can also be applied to units to add `#[wal_suffix]` to all inputs.
- [!214][!214] Improve the error messages for positional arguments

### Removed

- [!206][!206] Remove type dump file. This information was redundant and can be recovered from `CompilerState` instead

[Associated Swim release](https://gitlab.com/spade-lang/swim/-/tree/v0.4.0)

[!202]: https://gitlab.com/spade-lang/spade/-/merge_requests/202
[!205]: https://gitlab.com/spade-lang/spade/-/merge_requests/205
[!206]: https://gitlab.com/spade-lang/spade/-/merge_requests/206
[!207]: https://gitlab.com/spade-lang/spade/-/merge_requests/207
[!209]: https://gitlab.com/spade-lang/spade/-/merge_requests/209
[!214]: https://gitlab.com/spade-lang/spade/-/merge_requests/214
[!215]: https://gitlab.com/spade-lang/spade/-/merge_requests/215
[!216]: https://gitlab.com/spade-lang/spade/-/merge_requests/216
[!217]: https://gitlab.com/spade-lang/spade/-/merge_requests/217
[!221]: https://gitlab.com/spade-lang/spade/-/merge_requests/221

## [0.3.0] - 2023-06-01

### Added

- [!168][!168] Add an inverted port type `~T`. [Documentation][doc_inverted_ports]
- [!168][!168] Add `port` expression for creating a `(T, ~T)`. [Documentation][doc_inverted_ports]
- [!189][!189] Add `#[no_mangle]` attribute to unit parameters to avoid appending `_i` or `_o`
- [!191][!191] Add `translate_value` method to spade-python
- [!200][!200] Add more sophisticated and experimental wordlength inference logic that can be activated with the flag `--infer-method` or the environment variable `SPADE_INFER_METHOD`.
- [!167][!167] Add support for ready and valid signaling in the pipelines. [Documentation](https://docs.spade-lang.org/language_reference/dynamic_pipelines.html)

### Fixed

- [!178][!178] `sext` and `zext` now error when trying to reduce the width
- [!188][!188] Fix codegen bug when indexing structs or tuples which are 1 bit wide.
- [!201][!201] Stop producing `spade.sv` when monomorphisation fails

### Internal

- [!187][!187] Change naming scheme of Verilog variables to make names more predictable. [Documentation](https://docs.spade-lang.org/internal/naming.html)
- [!184][!184] The CI system now builds both Linux and macOS-AArch64.
- [!195][!195] Logos and Clap have had their respective versions bumped.

[!167]: https://gitlab.com/spade-lang/spade/-/merge_requests/167
[!168]: https://gitlab.com/spade-lang/spade/-/merge_requests/168
[!178]: https://gitlab.com/spade-lang/spade/-/merge_requests/178
[!184]: https://gitlab.com/spade-lang/spade/-/merge_requests/184
[!187]: https://gitlab.com/spade-lang/spade/-/merge_requests/187
[!188]: https://gitlab.com/spade-lang/spade/-/merge_requests/188
[!189]: https://gitlab.com/spade-lang/spade/-/merge_requests/189
[!191]: https://gitlab.com/spade-lang/spade/-/merge_requests/191
[!195]: https://gitlab.com/spade-lang/spade/-/merge_requests/195
[!200]: https://gitlab.com/spade-lang/spade/-/merge_requests/200
[!201]: https://gitlab.com/spade-lang/spade/-/merge_requests/201
[doc_inverted_ports]: https://docs.spade-lang.org/language_reference/type_system/inverted_ports.html

## [0.2.0] - 2023-04-20

### Added

- [!155][!155] Support for specifying initial content of memories.
- [!154][!154] Add unsigned literals, for example `let x: int<8> 255u` as a
  stop gap solution until proper unsigned types are implemented
- [!169][!169] Add `!=` operator
- [!185][!185] `max`, `min`, and `order` operation added to `std::ops`

### Fixed

- [!156][!156] Report an internal error when inferring negative widths instead of panicking

### Changed

- [!165][!165] Standard library is now included by the compiler instead of Swim.

### Internal

- [!154][!154] Rewrote compiler to use arbitrary width integers internally.

[!154]: https://gitlab.com/spade-lang/spade/-/merge_requests/154
[!155]: https://gitlab.com/spade-lang/spade/-/merge_requests/155
[!156]: https://gitlab.com/spade-lang/spade/-/merge_requests/156
[!165]: https://gitlab.com/spade-lang/spade/-/merge_requests/165
[!169]: https://gitlab.com/spade-lang/spade/-/merge_requests/169
[!185]: https://gitlab.com/spade-lang/spade/-/merge_requests/185

## [0.1.0] - 2023-03-07

Initial numbered version

[Associated Swim release](https://gitlab.com/spade-lang/swim/-/tree/v0.1.0)

[Unreleased]: https://gitlab.com/spade-lang/spade/-/compare/v0.10.0...main
[0.10.0]: https://gitlab.com/spade-lang/spade/-/compare/v0.10.0...v0.9.0
[0.9.0]: https://gitlab.com/spade-lang/spade/-/compare/v0.9.0...v0.8.0
[0.8.0]: https://gitlab.com/spade-lang/spade/-/compare/v0.8.0...v0.7.0
[0.7.0]: https://gitlab.com/spade-lang/spade/-/compare/v0.7.0...v0.6.0
[0.6.0]: https://gitlab.com/spade-lang/spade/-/compare/v0.5.0...v0.6.0
[0.5.0]: https://gitlab.com/spade-lang/spade/-/compare/v0.4.0...v0.5.0
[0.4.0]: https://gitlab.com/spade-lang/spade/-/compare/v0.3.0...v0.4.0
[0.3.0]: https://gitlab.com/spade-lang/spade/-/compare/v0.2.0...v0.3.0
[0.2.0]: https://gitlab.com/spade-lang/spade/-/compare/v0.1.0...v0.2.0
[0.1.0]: https://gitlab.com/spade-lang/spade/-/tree/v0.1.0
