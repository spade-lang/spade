# Changelog

All notable changes to this project will be documented in this file.

Spade is currently unstable and all 0.x releases are expected to contain
breaking changes. Releases are mainly symbolic and are done on a six-week
release cycle. Every six weeks, the current master branch is tagged and
released as a new version.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- [!155][!155] Support for specifying initial content of memories.
- [!154](!154) Add unsigned literals, for example `let x: int<8> 255u` as a
  stop gap solution until proper unsigned types are implemented

### Fixed

- [!156][!156] Report an internal error when inferring negative widths instead of panicking

### Changed

### Removed

### Internal

- [!154](!154) Rewrote compiler to use arbitrary width integers internally.

[!154]: https://gitlab.com/spade-lang/spade/-/merge_requests/154
[!155]: https://gitlab.com/spade-lang/spade/-/merge_requests/155
[!156]: https://gitlab.com/spade-lang/spade/-/merge_requests/155


## [0.1.0] - 2023-03-07

Initial numbered version

[Associated Swim release](https://gitlab.com/spade-lang/swim/-/tree/v0.1.0)

[0.1.0]: https://gitlab.com/spade-lang/spade/-/tree/v0.1.0
