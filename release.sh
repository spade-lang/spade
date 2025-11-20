#!/bin/env sh

cargo publish --workspace --exclude vcd-translate --exclude spade-python --exclude spade-simulation-ext --exclude spade-cxx --exclude spade-wordlength-inference --exclude spade-tests --exclude spade-language-server --exclude spade-surfer-plugin --exclude spadedoc
