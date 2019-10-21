.PHONY: cover prove all clean

all: cover bmc prove

cover: vai_reg.vhd symbiyosys.sby
	sby --yosys "yosys -m ghdl" -f -d work/vai_reg-$@ symbiyosys.sby $@

bmc: vai_reg.vhd symbiyosys.sby
	sby --yosys "yosys -m ghdl" -f -d work/vai_reg-$@ symbiyosys.sby $@

prove: vai_reg.vhd symbiyosys.sby
	sby --yosys "yosys -m ghdl" -f -d work/vai_reg-$@ symbiyosys.sby $@

clean:
	rm -rf work
