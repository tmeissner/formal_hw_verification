module dlatch_t (
    input         Reset_n_i,
    input         Clk_i,
    input         Wen_i,
    input  [15:0] Data_i,
    output [31:0] Data_o
);


  `define INIT_VALUE 32'hDEADBEEF


  dlatch #(.Init(`INIT_VALUE)) dlatch_i (
    .Reset_n_i(Reset_n_i),
    .Clk_i(Clk_i),
    .Wen_i(Wen_i),
    .Data_i(Data_i),
    .Data_o(Data_o)
  );


  reg init_state = 1;

  always @(*)
    if (init_state) assume (!Reset_n_i);

  always @(posedge Clk_i)
    init_state = 0;


  always @(*)
    if (!Reset_n_i) assert (Data_o == `INIT_VALUE);


endmodule

