#!/bin/bash

cargo build --release --target wasm32-unknown-unknown && cp ../target/wasm32-unknown-unknown/release/spade_surfer_plugin.wasm ~/.local/share/surfer/translators
