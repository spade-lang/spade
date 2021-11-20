$(shell cd .. && cargo build)
BUILD_DIR=build

# APIO stuff
APIO_BUILD_DIR=apio_build
APIO_FILES=apio.ini pins.pcf

IVERILOG_FLAGS=-g2012

SPADEC=../../target/debug/spade

VCDS=$(wildcard test/*)

SPADE_SOURCES=$(wildcard src/*.spade) $(wildcard ../../stdlib/*.spade)

# Main rule
all: build/main.v.vcd

# Build verilog from the spade code
build/main.v: $(SPADE_SOURCES) $(SPADEC) Makefile
	@mkdir -p ${@D}
	@echo -e "[\033[0;34m${SPADEC}\033[0m] building $@"
	${SPADEC} $(SPADE_SOURCES) -o $@

# Build a test binary
build/main.v.out: build/main.v src/testbench.v
	@echo -e "[\033[0;34miverilog\033[0m] building $@"
	@iverilog \
		-o ${@} \
		${IVERILOG_FLAGS} \
		-DVCD_OUTPUT=\"build/${<F}.vcd\" \
		$< src/testbench.v

# Simulate the test binary
build/main.v.vcd: build/main.v.out
	@mkdir -p output
	@echo -e "[\033[0;34mvvp\033[0m] simulating $@"
	@vvp $< | grep -v dumpfile


# ECPIX5 stuff
IDCODE ?= 0x81112043 # 12f

ecp5.json: top.v build/main.v ecpix5.lpf Makefile
	yosys \
		-p "read_verilog -sv build/main.v; synth_ecp5 -json $@" \
		-E .$(basename $@).d \
		top.v

ecp5.config: ecp5.json ecpix5.lpf
	nextpnr-ecp5 \
		--json $< \
		--textcfg $@ \
		--lpf ecpix5.lpf \
		--um5g-45k \
		--package CABGA554

ecp5.bit: ecp5.config ecpix5.lpf
	ecppack --idcode $(IDCODE) $< $@

ecp5.svf: ecp5.config ecpix5.lpf
	ecppack --idcode $(IDCODE) --input $< --svf $@

upload: ecp5.svf .PHONY
	openocd -f openocd-ecpix5.cfg -c "init" -c "svf -quiet ecp5.svf" -c "exit"

clean:
	rm -rf build/


.SECONDARY: $(patsubst %, build/main.v, ${TEST_DIRS})
.PHONY: build/main.v.vcd build_compiler all

# Builds an iverlog command file with all build options that can be passed to linters
iverilog_commandfile: build_hs
	@echo -e $(patsubst %, '-l %\n', ${non_test_verilogs}) > .verilog_config
