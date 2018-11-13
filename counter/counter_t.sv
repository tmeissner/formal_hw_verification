module counter_t (
    input         Reset_n_i,
    input         Clk_i,
    output [31:0] Data_o
);


  `define INIT_VALUE 8


  counter #(.Init(`INIT_VALUE)) counter_i (
    .Reset_n_i(Reset_n_i),
    .Clk_i(Clk_i),
    .Data_o(Data_o)
  );


  reg init_state = 1;

  always @(*)
    if (init_state) assume (!Reset_n_i);

  always @(posedge Clk_i)
    init_state = 0;


/*
  // Don't works with Verific at the moment
  initial begin
    assume (!Reset_n_i);
  end
*/


  // Proves fail, counterexample hasn't initial reset active
  assert property (@(posedge Clk_i) Data_o >= `INIT_VALUE && Data_o <= 64);
  assert property (@(posedge Clk_i) disable iff (!Reset_n_i) Data_o < 64 |=> Data_o == $past(Data_o) + 1);


endmodule

