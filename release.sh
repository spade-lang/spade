#!/bin/env sh

# cargo release --exclude vcd-translate --exclude spade-python --exclude spade-simulation-ext --exclude spade-cxx --exclude spade-wordlength-inference --exclude spade-tests --no-tag --no-push $@

set -e pipefail

cd spade-common && cargo publish && cd ..
cd spade-macros && cargo publish && cd ..
cd spade-diagnostics && cargo publish && cd ..
cd spade-ast && cargo publish && cd ..
cd spade-types && cargo publish && cd ..
cd spade-hir && cargo publish && cd ..
cd spade-mir && cargo publish && cd ..
cd spade-parser && cargo publish && cd ..
cd spade-ast-lowering && cargo publish && cd ..
cd spade-typeinference && cargo publish && cd ..
cd spade-hir-lowering && cargo publish && cd ..
cd spade-compiler && cargo publish && cd ..

# cd spade-language-server && cargo publish && cd ..
# cd spade-python && cargo publish && cd ..

# cd swim_test_errors && cargo publish && cd ..
# cd swim_tests && cargo publish && cd ..
# cd spade-cxx && cargo publish && cd ..
# cd spade-tests && cargo publish && cd ..
# cd spade-simulation-ext && cargo publish && cd ..
# cd spade-surfer-plugin && cargo publish && cd ..
