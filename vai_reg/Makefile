DUT := vai_reg

.PHONY: cover prove all clean

all: cover bmc prove

cover: ${DUT}.vhd symbiyosys.sby
	sby --yosys "yosys -m ghdl" -f -d work/${DUT}-$@ symbiyosys.sby $@

bmc: ${DUT}.vhd symbiyosys.sby
	sby --yosys "yosys -m ghdl" -f -d work/${DUT}-$@ symbiyosys.sby $@

prove: ${DUT}.vhd symbiyosys.sby
	sby --yosys "yosys -m ghdl" -f -d work/${DUT}-$@ symbiyosys.sby $@

clean:
	rm -rf work
