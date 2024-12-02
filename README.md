<img src="misc/spadefish.svg" />

[![Gitlab pipeline status](https://img.shields.io/gitlab/pipeline-status/spade-lang/spade?branch=master)](https://img.shields.io/gitlab/pipeline-status/spade-lang/spade?branch=master)
[![Gitlab code coverage](https://img.shields.io/gitlab/pipeline-coverage/spade-lang/spade?branch=master)](https://img.shields.io/gitlab/pipeline-coverage/spade-lang/spade?branch=master)
[![GitLab tag (latest by date)](https://img.shields.io/gitlab/v/tag/spade-lang/spade)](https://img.shields.io/gitlab/v/tag/spade-lang/spade)
[![GitLab last commit](https://img.shields.io/gitlab/last-commit/spade-lang/spade)](https://img.shields.io/gitlab/last-commit/spade-lang/spade)
[![GitLab contributors](https://img.shields.io/gitlab/contributors/spade-lang/spade)](https://img.shields.io/gitlab/contributors/spade-lang/spade)
[![GitLab language count](https://img.shields.io/gitlab/languages/count/spade-lang/spade)](https://img.shields.io/gitlab/languages/count/spade-lang/spade)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.7713114.svg)](https://doi.org/10.5281/zenodo.7713114)

# Spade

A work in progress HDL that doesn't make you want to pull your hair out. Taking
inspiration from rust and clash, the goal is to make a safer more expressive
language than Verilog and VHDL but without sacrificing the ability for low
level control of the hardware.

To learn more about the Spade language, see the website at
[https://spade-lang.org](https://spade-lang.org) or the language documentation
at [https://docs.spade-lang.org](https://docs.spade-lang.org)

## Getting started

To get started with Spade, see
[https://docs.spade-lang.org/introduction.html](https://docs.spade-lang.org/introduction.html)

## Editor integration

There are editor plugins for syntax highlighting available for some editors

 - vim: if you're using neovim with [lazy.nvim](https://github.com/folke/lazy.nvim), you can install https://github.com/ethanuppal/spade.nvim; otherwise, use https://gitlab.com/spade-lang/spade-vim, which requires a bit of manual setup
 - vscode: https://git.sr.ht/~acqrel/spade-vscode
 - emacs: https://git.sr.ht/~lucasklemmer/spade-mode

Note that most of these are maintained by third parties and may be out of date.
If you make a plugin for your favourite editor, feel free to add it to the
list!

## Development and Community

If you are interested in using or contributing to Spade, feel free to join our
[discord group](https://discord.gg/YtXbeamxEX).

If you want to understand the compiler, the [ARCHITECTURE.md](ARCHITECTURE.md) document is a good place to start. It gives
a high level overview of the inner workings of the compiler.

Spade is currently being developed as an Open Source project at the Department
of Electrical Engineering at Linköping university.

## License

The spade compiler is licensed under the [EUPL-1.2 license](LICENSE-EUPL-1.2.txt).

The spade standard library (all files located in the stdlib directory) is licensed under
the terms of both the [MIT license](MIT License) and the [Apache
License](LICENSE-APACHE2.0.txt).
