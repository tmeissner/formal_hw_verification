module counter_t (
    input         Reset_n_i,
    input         Clk_i,
    output [31:0] Data_o
);


  `define INITVAL 8
  `define ENDVAL  64


  counter #(
    .InitVal(`INITVAL),
    .EndVal(`ENDVAL)
  ) counter_i (
    .Reset_n_i(Reset_n_i),
    .Clk_i(Clk_i),
    .Data_o(Data_o)
  );


             reg  init_state = 1;
  (* gclk *) wire gbl_clk;

  // Initial reset
  always @(*) begin
    if (init_state) assume (!Reset_n_i);
    if (!init_state) assume (Reset_n_i);
  end

  always @(posedge Clk_i)
    init_state = 0;

  // Generate global clock
  global clocking
    @(posedge gbl_clk);
  endclocking

  // Use global clock to constrain the DUT clock
  always @($global_clock) begin
    assume(Clk_i != $past(Clk_i));
  end

  // Immediate assertions
  always @(*)
    if (!Reset_n_i) assert (Data_o == `INITVAL);

  // Fails with unbounded prove using SMTBMC, maybe
  // the assumptions/assertions have to be more strict.
  // With abc pdr this can be successfully proved.
  assert property (@(posedge Clk_i) disable iff (!Reset_n_i) Data_o <  `ENDVAL |=> Data_o == $past(Data_o) + 1);
  assert property (@(posedge Clk_i) disable iff (!Reset_n_i) Data_o == `ENDVAL |=> $stable(Data_o));
  assert property (@(posedge Clk_i) Data_o >= `INITVAL && Data_o <= `ENDVAL);


endmodule

