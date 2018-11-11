module alu_t (
    inout        Reset_n_i,
    input        Clk_i,
    input  [1:0] Opc_i,
    input  [31:0] DinA_i,
    input  [31:0] DinB_i,
    output [31:0] Dout_o,
    output       OverFlow_o
);


  alu alu_i (
    .Reset_n_i(Reset_n_i),
    .Clk_i(Clk_i),
    .Opc_i(Opc_i),
    .DinA_i(DinA_i),
    .DinB_i(DinB_i),
    .Dout_o(Dout_o),
    .OverFlow_o(OverFlow_o)
  );

  const logic [1:0] OPC_ADD = 0;
  const logic [1:0] OPC_SUB = 1;
  const logic [1:0] OPC_AND = 2;
  const logic [1:0] OPC_OR  = 3;

  initial begin
    assume (!Reset_n_i);
  end

  bit unsigned [32:0] dina, dinb;

  assign dina = DinA_i;
  assign dinb = DinB_i;

  assert property (@(posedge Clk_i) disable iff (!Reset_n_i) Opc_i == OPC_ADD |=> Dout_o == ($past(DinA_i) + $past(DinB_i)));
  assert property (@(posedge Clk_i) disable iff (!Reset_n_i) Opc_i == OPC_ADD && (dina + dinb) > 2**32-1 |=> OverFlow_o);
  assert property (@(posedge Clk_i) disable iff (!Reset_n_i) Opc_i == OPC_SUB |=> Dout_o == ($past(DinA_i) - $past(DinB_i)));
  assert property (@(posedge Clk_i) disable iff (!Reset_n_i) Opc_i == OPC_SUB && (dina - dinb) > 2**32-1 |=> OverFlow_o);
  assert property (@(posedge Clk_i) disable iff (!Reset_n_i) Opc_i == OPC_AND |=> Dout_o == ($past(DinA_i) & $past(DinB_i)));
  assert property (@(posedge Clk_i) disable iff (!Reset_n_i) Opc_i == OPC_OR |=> Dout_o == ($past(DinA_i) | $past(DinB_i)));

  assert property (@(posedge Clk_i or negedge Clk_i) !Reset_n_i |-> Dout_o == 0);

  property cover_opc (opc);
    @(posedge Clk_i)
      disable iff (!Reset_n_i) Opc_i == opc;
  endproperty

  cover property (cover_opc(OPC_ADD));
  cover property (cover_opc(OPC_SUB));
  cover property (cover_opc(OPC_AND));
  cover property (cover_opc(OPC_OR));


endmodule

