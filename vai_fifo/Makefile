DUT := vai_fifo
SRC := ../fifo/fifo.vhd ${DUT}.vhd

.PHONY: cover bmc prove synth all clean

all: cover bmc prove

cover bmc prove: ${DUT}.vhd symbiyosys.sby
	sby --yosys "yosys -m ghdl" -f -d work/${DUT}-$@ symbiyosys.sby $@

${DUT}_synth.vhd: ${DUT}.vhd
	ghdl --synth --std=08 --no-formal -gDepth=16 -gWidth=16 ${SRC} -e ${DUT} > $@

synth: ${DUT}.json
${DUT}.json: ${DUT}_synth.vhd
	yosys -m ghdl -p 'ghdl --std=08 --no-formal -gDepth=16 -gWidth=16 ${SRC} -e ${DUT}; synth_ice40 -top ${DUT} -json $@'

clean:
	rm -rf work ${DUT}.json ${DUT}_synth.vhd
