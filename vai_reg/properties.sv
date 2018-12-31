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
    input [7:0] s_header,
    input       s_error,
    input [7:0] s_register [0:7]
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

  // Default clocking & reset

  default clocking
    @(posedge Clk_i);
  endclocking

  default disable iff (!Reset_n_i);


  // Constraints

  assume property (
    DinValid_i && !DinAccept_o |=>
    $stable(DinValid_i)
  );

  assume property (
    DinValid_i && !DinAccept_o |=>
    $stable(Din_i)
  );

  assume property (
    DinValid_i && !DinAccept_o |=>
    $stable(DinStart_i)
  );

  assume property (
    DinValid_i && !DinAccept_o |=>
    $stable(DinStop_i)
  );


  // Asserts

  assert property (
    s_fsm_state >= 0 && s_fsm_state <= 6
  );

  assert property (
    DoutStart_o |->
    DoutValid_o
  );

  assert property (
    DoutStart_o && DoutAccept_i |=>
    !DoutStart_o
  );

  assert property (
    DoutStop_o |->
    DoutValid_o
  );

  assert property (
    DoutStop_o && DoutAccept_i |=>
    !DoutStop_o
  );

  assert property (
    s_fsm_state == 1 && DinValid_i && DinStart_i && DinAccept_o |=>
    s_header == $past(Din_i)
  );


  // State changes

  assert property (
    s_fsm_state == 0 |=> s_fsm_state == 1
  );

  assert property (
    s_fsm_state == 1 && DinValid_i && DinStart_i && DinStop_i && Din_i[3:0] == `READ |=>
    s_fsm_state == 2
  );

  assert property (
    s_fsm_state == 1 && DinValid_i && DinStart_i && !DinStop_i && Din_i[3:0] == `WRITE |=>
    s_fsm_state == 3
  );

  assert property (
    s_fsm_state == 2 |=> s_fsm_state == 4
  );

  assert property (
    s_fsm_state == 4 && DoutValid_o && DoutAccept_i && s_header[3:0] == `READ |=> s_fsm_state == 5
  );

  assert property (
    s_fsm_state == 4 && DoutValid_o && DoutAccept_i && s_header[3:0] != `READ |=> s_fsm_state == 6
  );

  assert property (
    s_fsm_state == 6 && DoutValid_o && DoutAccept_i |=> s_fsm_state == 0
  );


  // Protocol checks

  assert property (
    s_fsm_state > 1 |->
    s_header[3:0] inside {`READ, `WRITE}
  );

  assert property (
    s_fsm_state > 1 |=>
    $stable(s_header)
  );

  assert property (
    DoutStart_o && DoutValid_o |->
    Dout_o[3:0] == s_header[3:0]
  );

  assert property (
    s_fsm_state inside {1, 2, 3} |->
    !s_error
  );

  assert property (
    s_fsm_state >= 4 |->
    s_error == !(s_header[7:4] <= 7)
  );

  assert property (
    DoutStop_o && DoutValid_o |->
    Dout_o == s_error
  );

  assert property (
    DoutValid_o && !DoutAccept_i |=>
    $stable(Dout_o)
  );

  assert property (
    DoutValid_o && !DoutAccept_i |=>
    $stable(DoutStart_o)
  );

  assert property (
    DoutValid_o && !DoutAccept_i |=>
    $stable(DoutStop_o)
  );

  assert property (
    DoutValid_o |-> !(DoutStart_o && DoutStop_o)
  );

  assert property (
    DoutStart_o |-> s_fsm_state == 4
  );

  assert property (
    DoutStop_o |-> s_fsm_state == 6
  );

  assert property (
    DoutValid_o |-> s_fsm_state >= 4 && s_fsm_state <= 6
  );

  // Write ack frame
  assert property (
    DoutValid_o && DoutStart_o && DoutAccept_i && Dout_o[3:0] == `WRITE |=>
    !DoutValid_o ##1
    DoutValid_o && DoutStop_o
  );

  // Read ack frame
  assert property (
    DoutValid_o && DoutStart_o && DoutAccept_i && Dout_o[3:0] == `READ |=>
    !DoutValid_o ##1
    DoutValid_o && !DoutStart_o && !DoutStop_o && !DoutAccept_i [*] ##1
    DoutValid_o && !DoutStart_o && !DoutStop_o && DoutAccept_i ##1
    !DoutValid_o ##1
    DoutValid_o && DoutStop_o
  );

  // Can only be proven with abc at the moment
  // smtbmc fails with unbounded proof
  assert property (
    s_fsm_state == 1 && DinValid_i && DinStart_i && !DinStop_i && DinAccept_o && Din_i[3:0] == `WRITE && Din_i[7:4] <= 7 ##1
    !DinValid_i [*] ##1
    s_fsm_state == 3 && DinValid_i && DinAccept_o && DinStop_i  |=>
    s_register[s_header[7:4]] == $past(Din_i)
  );


endmodule


bind vai_reg properties properties (.*);
