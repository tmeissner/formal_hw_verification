The original repository is located on my own git-server at [https://git.goodcleanfun.de/tmeissner/formal_verification](https://git.goodcleanfun.de/tmeissner/formal_verification)
It is mirrored to github with every push, so both should be in sync.


# formal_verification

Tests and examples of using formal verification to check correctness of digital hardware designs. All tests are done with SymbiYosys, a front-end for formal verification flows based on [Yosys](https://github.com/YosysHQ). Some examples use the VHDL/SystemVerilog parser plugin by Verific which isn't free SW and not included in the free Yosys version. See on the [Symbiotic EDA website](https://www.symbioticeda.com) for more information. 

### alu
A simple ALU design in VHDL, together with a formal testbench written in SystemVerilog. The testbench contains various simple SVA properties used by assert & cover directives which are proved with the SymbiYosys tool.


### counter
A simple counter design in VHDL, together with a formal testbench written in SystemVerilog. The testbench contains various simple SVA properties used by assert & cover directives which are proved with the SymbiYosys tool.

### dlatch
A simple test design which generates the `Unsupported cell type $dlatchsr` error using with Verific plugin.
