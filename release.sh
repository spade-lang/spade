#!/bin/env sh

cargo release --exclude vcd-translate --exclude spade-python --exclude spade-simulation-ext --exclude spade-cxx --exclude spade-wordlength-inference --exclude spade-tests --no-tag --no-push $@
