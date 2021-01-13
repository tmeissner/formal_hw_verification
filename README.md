[![](https://img.shields.io/github/workflow/status/tmeissner/formal_hw_verification/Test/main?longCache=true&style=flat-square&label=Test&logo=GitHub%20Actions&logoColor=fff)](https://github.com/tmeissner/formal_hw_verification/actions?query=workflow%3ATest)

The original repository is located on my own git-server at [https://git.goodcleanfun.de/tmeissner/formal_hw_verification](https://git.goodcleanfun.de/tmeissner/formal_hw_verification)

It is mirrored to github with every push, so both should be in sync.


# formal_hw_verification

Tests and examples of using formal verification to check correctness of digital hardware designs. All tests are done with [SymbiYosys](https://github.com/YosysHQ/SymbiYosys), a front-end for formal verification flows based on [Yosys](https://github.com/YosysHQ/yosys).

All stuff in the master branch uses [ghdl-yosys-plugin](https://github.com/ghdl/ghdl-yosys-plugin) and [GHDL](https://github.com/ghdl/ghdl) as VHDL front-end plugin for (Symbi)Yosys. Using GHDL as synthesis frontend allows using PSL as verification language. The alu, counter & vai_reg designs can be verified with that combination at the moment.

Some examples in the [verific branch](https://github.com/tmeissner/formal_hw_verification/tree/verific) use the commercial VHDL/SystemVerilog frontend plugin by Verific which isn't free SW and not included in the free Yosys version. See on the [Symbiotic EDA website](https://www.symbioticeda.com) for more information.

### alu
A simple ALU design in VHDL. The formal checks contain various simple properties used by assert & cover directives which are proved with the SymbiYosys tool.

### counter
A simple counter design in VHDL. The testbench contains various simple properties used by assert & cover directives which are proved with the SymbiYosys tool.

### fifo
A simple synchronous FIFO with various checks for write/read pointers, data and flags.

### vai_fifo
A simple FIFO with valid-accept-interface. Consists of fifo as sub-unit and some glue logic doing fifo<->vai interface conversion. This design serves as an example how to verify designs with sub-units containing formal checks.

### vai_reg
A simple register file with VAI (valid-accept-interface) which serves as test design to try formal verification of FSMs.
