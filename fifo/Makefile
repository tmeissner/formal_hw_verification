DUT := fifo

.PHONY: cover bmc prove synth all clean

all: cover bmc prove

cover bmc prove: ${DUT}.vhd symbiyosys.sby
	sby --yosys "yosys -m ghdl" -f -d work/${DUT}-$@ symbiyosys.sby $@

$(DUT)_synth.vhd: ${DUT}.vhd
	ghdl --synth --std=08 --no-formal -gDepth=16 -gWidth=16 $(DUT).vhd -e $(DUT) > $(DUT)_synth.vhd

synth: fifo.json
fifo.json: $(DUT)_synth.vhd
	yosys -m ghdl -p 'ghdl --std=08 --no-formal -gDepth=16 -gWidth=16 $(DUT).vhd -e $(DUT); synth_ice40 -json $@'

clean:
	rm -rf work $(DUT).json $(DUT)_synth.vhd
