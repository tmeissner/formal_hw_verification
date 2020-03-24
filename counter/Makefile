DUT := counter

.PHONY: cover bmc prove all clean

all: cover bmc prove

cover bmc prove: ${DUT}.vhd symbiyosys.sby
	sby --yosys "yosys -m ghdl" -f -d work/${DUT}-$@ symbiyosys.sby $@

clean:
	rm -rf work
