SHELL=/bin/bash -o pipefail
$(if $(shell cd .. && cargo build --workspace --exclude spade-cxx --exclude spade-language-server && echo "ok"), , $(error cargo build failed))
BUILD_DIR=build

IVERILOG_FLAGS=-g2012

SPADEC=../target/debug/spade

TEST_DIRS=$(wildcard test/*)
TEST_TARGETS=$(patsubst test/%, test/%/build/code.v.vcd, $(TEST_DIRS))

# Main rule
all: ${TEST_TARGETS} .PHONY

test/%/build/code.v: test/%/code.spade $(SPADEC) .PHONY
	@mkdir -p ${@D}
	@echo -e "[\033[0;34m${SPADEC}\033[0m] building $@"
	${SPADEC} $(wildcard ${<D}/*.spade) -o $@ 

# Build a test binary
test/%/build/code.v.out: test/%/build/code.v
	@echo -e "[\033[0;34miverilog\033[0m] building $@"
	@iverilog \
		-o ${@} \
		${IVERILOG_FLAGS} \
		-DVCD_OUTPUT=\"test/$*/build/${<F}.vcd\" \
		$< ${@D}/../testbench.v

# Simulate the test binary
test/%/build/code.v.vcd: test/%/build/code.v.out .PHONY
	@mkdir -p output
	@echo -e "[\033[0;34mvvp\033[0m] simulating $@"
	@vvp $< | grep -v dumpfile


build_compiler:
	cd .. && cargo build



clean:
	rm -rf $(patsubst %, %/build, ${TEST_DIRS})


.SECONDARY: $(patsubst %, %/build/code.v, ${TEST_DIRS})
.PHONY:

# Builds an iverlog command file with all build options that can be passed to linters
iverilog_commandfile: build_hs
	@echo -e $(patsubst %, '-l %\n', ${non_test_verilogs}) > .verilog_config
