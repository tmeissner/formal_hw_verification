module properties (
    input       Reset_n_i,
    input       Clk_i,
    input [7:0] Din_i,
    input       DinValid_i,
    input       DinStart_i,
    input       DinStop_i,
    input       DinAccept_o,
    input [7:0] Dout_o,
    input       DoutValid_o,
    input       DoutStart_o,
    input       DoutStop_o,
    input       DoutAccept_i,
    // Internals
    input [2:0] s_fsm_state,
    input [7:0] s_header
);



  `define READ 0
  `define WRITE 1


  reg init_state = 1;

  // Initial reset
  always @(*) begin
    if (init_state) assume (!Reset_n_i);
    if (!init_state) assume (Reset_n_i);
  end

  always @(posedge Clk_i)
    init_state = 0;


  // Constraints

  assume property (@(posedge Clk_i)
    DinValid_i && !DinAccept_o |=>
    $stable(Din_i)
  );

  assume property (@(posedge Clk_i)
    DinValid_i && !DinAccept_o |=>
    $stable(DinStart_i)
  );

  assume property (@(posedge Clk_i)
    DinValid_i && !DinAccept_o |=>
    $stable(DinStop_i)
  );


  // Asserts

  assert property (@(posedge Clk_i)
    s_fsm_state >= 0 && s_fsm_state <= 6
  );

  assert property (@(posedge Clk_i)
    DoutStart_o |->
    DoutValid_o
  );

  assert property (@(posedge Clk_i)
    DoutStart_o && DoutAccept_i |=>
    !DoutStart_o
  );

  assert property (@(posedge Clk_i)
    DoutStop_o |->
    DoutValid_o
  );

  assert property (@(posedge Clk_i)
    DoutStop_o && DoutAccept_i |=>
    !DoutStop_o
  );

  assert property (@(posedge Clk_i)
    s_fsm_state == 1 && DinValid_i && DinStart_i && DinAccept_o |=>
    s_header == $past(Din_i)
  );


  // State changes

  assert property (@(posedge Clk_i) disable iff (!Reset_n_i)
    s_fsm_state == 0 |=> s_fsm_state == 1
  );

  assert property (@(posedge Clk_i) disable iff (!Reset_n_i)
    s_fsm_state == 1 && DinValid_i && DinStart_i && DinStop_i && Din_i[3:0] == `READ |=>
    s_fsm_state == 2
  );

  assert property (@(posedge Clk_i) disable iff (!Reset_n_i)
    s_fsm_state == 1 && DinValid_i && DinStart_i && !DinStop_i && Din_i[3:0] == `WRITE |=>
    s_fsm_state == 3
  );

  assert property (@(posedge Clk_i) disable iff (!Reset_n_i)
    s_fsm_state == 2 |=> s_fsm_state == 4
  );

  assert property (@(posedge Clk_i) disable iff (!Reset_n_i)
    s_fsm_state == 4 && DoutValid_o && DoutAccept_i && s_header[3:0] == `READ |=> s_fsm_state == 5
  );

  assert property (@(posedge Clk_i) disable iff (!Reset_n_i)
    s_fsm_state == 4 && DoutValid_o && DoutAccept_i && s_header[3:0] != `READ |=> s_fsm_state == 6
  );

  assert property (@(posedge Clk_i) disable iff (!Reset_n_i)
    s_fsm_state == 6 && DoutValid_o && DoutAccept_i |=> s_fsm_state == 0
  );


  // Protocol checks

  assert property (@(posedge Clk_i)
    s_fsm_state > 1 |->
    s_header[3:0] == `READ || s_header[3:0] == `WRITE
  );

  assert property (@(posedge Clk_i)
    DoutStart_o && DoutValid_o |->
    Dout_o[3:0] == s_header[3:0]
  );

  assert property (@(posedge Clk_i)
    DoutValid_o && !DoutAccept_i |=>
    $stable(Dout_o)
  );

  assert property (@(posedge Clk_i)
    DoutValid_o && !DoutAccept_i |=>
    $stable(DoutStart_o)
  );

  assert property (@(posedge Clk_i)
    DoutValid_o && !DoutAccept_i |=>
    $stable(DoutStop_o)
  );

  assert property (@(posedge Clk_i)
    DoutValid_o |-> !(DoutStart_o && DoutStop_o)
  );

  assert property (@(posedge Clk_i)
    DoutStart_o |-> s_fsm_state == 4
  );

  assert property (@(posedge Clk_i)
    DoutStop_o |-> s_fsm_state == 6
  );

  assert property (@(posedge Clk_i)
    DoutValid_o |-> s_fsm_state >= 4 && s_fsm_state <= 6
  );


endmodule


bind vai_reg properties properties (.*);
