`define WIDTH 8


module alu_t (
    input               Reset_n_i,
    input               Clk_i,
    input  [1:0]        Opc_i,
    input  [`WIDTH-1:0] DinA_i,
    input  [`WIDTH-1:0] DinB_i,
    output [`WIDTH-1:0] Dout_o,
    output              OverFlow_o
);



  `define OPC_ADD 0
  `define OPC_SUB 1
  `define OPC_AND 2
  `define OPC_OR  3


  alu #(.Width(`WIDTH)) alu_i (
    .Reset_n_i(Reset_n_i),
    .Clk_i(Clk_i),
    .Opc_i(Opc_i),
    .DinA_i(DinA_i[`WIDTH-1:0]),
    .DinB_i(DinB_i[`WIDTH-1:0]),
    .Dout_o(Dout_o[`WIDTH-1:0]),
    .OverFlow_o(OverFlow_o)
  );


  reg init_state = 1;

  // Initial reset
  always @(*) begin
    if (init_state) assume (!Reset_n_i);
    if (!init_state) assume (Reset_n_i);
  end

  always @(posedge Clk_i)
    init_state = 0;

  default clocking
    @(posedge Clk_i);
  endclocking

  default disable iff (!Reset_n_i);


  bit unsigned [`WIDTH:0] dina, dinb;

  assign dina = DinA_i;
  assign dinb = DinB_i;

  assert property (Opc_i == `OPC_ADD |=> Dout_o == ($past(DinA_i) + $past(DinB_i)));
  assert property (Opc_i == `OPC_ADD && (dina + dinb) > 2**`WIDTH-1 |=> OverFlow_o);
  assert property (Opc_i == `OPC_SUB |=> Dout_o == ($past(DinA_i) - $past(DinB_i)));
  assert property (Opc_i == `OPC_SUB && (dina - dinb) > 2**`WIDTH-1 |=> OverFlow_o);
  assert property (Opc_i == `OPC_AND |=> Dout_o == ($past(DinA_i) & $past(DinB_i)));
  assert property (Opc_i == `OPC_OR |=> Dout_o == ($past(DinA_i) | $past(DinB_i)));



  property cover_opc (opc);
    Opc_i == opc;
  endproperty

  cover property (cover_opc(`OPC_ADD));
  cover property (cover_opc(`OPC_SUB));
  cover property (cover_opc(`OPC_AND));
  cover property (cover_opc(`OPC_OR));


endmodule

