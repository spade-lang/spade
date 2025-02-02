#!/bin/sh -ex

cd ../ && cargo build --release --target wasm32-wasip1 --bin spade
