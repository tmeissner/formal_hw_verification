# formal_verification

Tests and examples of using formal verification to check correctness of digital hardware designs. All tests are done with SymbiYosys, a front-end for formal verification flows based on [Yosys](https://github.com/YosysHQ). Some examples use the VHDL/SystemVerilog parser plugin by Verific which isn't free SW and not included in the free Yosys version. See on the [Symbiotic EDA website](https://www.symbioticeda.com) for more information. 

### alu
A simple ALU design in VHDL, together with a formal testbench written in SystemVerilog. The testbench contains various simple SVA properties used by assert & cover directives which are proved with the SymbiYosys tool.
