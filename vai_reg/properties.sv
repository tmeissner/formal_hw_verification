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
    input [7:0] s_data,
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

  fsm_state_valid_a : assert property (
    s_fsm_state >= 0 && s_fsm_state <= 6
  );

  valid_when_start_a : assert property (
    DoutStart_o |->
    DoutValid_o
  );

  start_off_when_acked_a : assert property (
    DoutStart_o && DoutAccept_i |=>
    !DoutStart_o
  );

  valid_when_stop_a : assert property (
    DoutStop_o |->
    DoutValid_o
  );

  stop_off_when_acked_a : assert property (
    DoutStop_o && DoutAccept_i |=>
    !DoutStop_o
  );

  store_header_a : assert property (
    s_fsm_state == 1 && DinValid_i && DinStart_i && DinAccept_o |=>
    s_header == $past(Din_i)
  );


  // State changes

  // IDLE -> GET_HEADER
  fsm_idle_to_get_header_a : assert property (
    s_fsm_state == 0 |=> s_fsm_state == 1
  );

  // GET_HEADER -> GET_DATA
  fsm_get_header_to_get_data_a : assert property (
    s_fsm_state == 1 && DinValid_i && DinStart_i && DinStop_i && Din_i[3:0] == `READ |=>
    s_fsm_state == 2
  );

  // GET_HEADER -> SET_DATA
  fsm_get_header_to_set_data_a : assert property (
    s_fsm_state == 1 && DinValid_i && DinStart_i && !DinStop_i && Din_i[3:0] == `WRITE |=>
    s_fsm_state == 3
  );

  // GET_DATA -> SEND_HEADER
  fsm_get_data_to_send_header_a : assert property (
    s_fsm_state == 2 |=> s_fsm_state == 4
  );

  // SET_DATA -> IDLE
  fsm_set_data_to_idle_a : assert property (
    s_fsm_state == 3 && DinValid_i && !DinStop_i |=> s_fsm_state == 0
  );

  // SET_DATA -> SEND_HEADER
  fsm_set_data_to_send_header_a : assert property (
    s_fsm_state == 3 && DinValid_i && DinStop_i |=> s_fsm_state == 4
  );

  // SEND_HEADER -> SEND_DATA
  fsm_send_header_to_send_data_a : assert property (
    s_fsm_state == 4 && DoutValid_o && DoutAccept_i && s_header[3:0] == `READ |=> s_fsm_state == 5
  );

  // SEND_HEADER -> SEND_FOOTER
  fsm_send_header_to_send_footer_a : assert property (
    s_fsm_state == 4 && DoutValid_o && DoutAccept_i && s_header[3:0] == `WRITE |=> s_fsm_state == 6
  );

  // SEND_DATA -> SEND_FOOTER
  fsm_send_data_to_send_footer_a : assert property (
    s_fsm_state == 5 && DoutValid_o && DoutAccept_i |=> s_fsm_state == 6
  );

  // SEND_FOOTER -> IDLE
  fsm_send_footer_to_idle_a : assert property (
    s_fsm_state == 6 && DoutValid_o && DoutAccept_i |=> s_fsm_state == 0
  );


  // Protocol checks

  header_in_valid_range_a : assert property (
    s_fsm_state > 1 |->
    s_header[3:0] inside {`READ, `WRITE}
  );

  header_stable_a : assert property (
    s_fsm_state > 1 |=>
    $stable(s_header)
  );

  header_dout_valid_a : assert property (
    DoutStart_o && DoutValid_o |->
    Dout_o == s_header
  );

  error_flag_initial_false_a : assert property (
    s_fsm_state inside {1, 2, 3} |->
    !s_error
  );

  error_flag_set_invalid_addr_a : assert property (
    s_fsm_state >= 4 |->
    s_error == !(s_header[7:4] <= 7)
  );

  footer_dout_valid_a :assert property (
    DoutStop_o && DoutValid_o |->
    Dout_o == s_error
  );

  doutvalid_stable_until_acked_a : assert property (
    DoutValid_o && !DoutAccept_i |=>
    $stable(DoutValid_o)
  );

  dout_stable_until_acked_a : assert property (
    DoutValid_o && !DoutAccept_i |=>
    $stable(Dout_o)
  );

  doutstart_stable_until_acked_a : assert property (
    DoutValid_o && !DoutAccept_i |=>
    $stable(DoutStart_o)
  );

  doutstop_stable_until_acked_a : assert property (
    DoutValid_o && !DoutAccept_i |=>
    $stable(DoutStop_o)
  );

  onehot_doutstart_doutstop_a : assert property (
    DoutValid_o |-> $onehot0({DoutStart_o, DoutStop_o})
  );

  doutstart_in_valid_fsm_state_a : assert property (
    DoutStart_o |-> s_fsm_state == 4
  );

  doutstop_in_valid_fsm_state_a : assert property (
    DoutStop_o |-> s_fsm_state == 6
  );

  doutvalid_in_valid_fsm_states_a : assert property (
    DoutValid_o |-> s_fsm_state >= 4 && s_fsm_state <= 6
  );

  // Write ack frame
  write_frame_a : assert property (
    DoutValid_o && DoutStart_o && DoutAccept_i && Dout_o[3:0] == `WRITE |=>
    !DoutValid_o ##1
    DoutValid_o && DoutStop_o
  );

  // Read ack frame
  read_frame_a : assert property (
    DoutValid_o && DoutStart_o && DoutAccept_i && Dout_o[3:0] == `READ |=>
    !DoutValid_o ##1
    DoutValid_o && !DoutStart_o && !DoutStop_o && !DoutAccept_i [*] ##1
    DoutValid_o && !DoutStart_o && !DoutStop_o && DoutAccept_i ##1
    !DoutValid_o ##1
    DoutValid_o && DoutStop_o
  );

  // Register read in GET_DATA if valid adress was given
  get_data_valid_a : assert property (
    s_fsm_state > 2 && s_header[7:4] <= 7 && s_header[3:0] == `READ |->
    s_data == s_register[s_header[7:4]]
  );

  // Error flag set & no register read in GET_DATA if invalid adress was given
  get_data_invalid_a : assert property (
    s_fsm_state > 2 && s_header[7:4] > 7 && s_header[3:0] == `READ |=>
    s_data == 0 && s_error
  );

  // register stable if read request
  reg_stable_during_read_a : assert property (
    s_fsm_state > 1 && s_header[3:0] == `READ |=>
    $stable(s_register)
  );

  // Read ack data correct if address is valid
  read_ack_data_valid_a : assert property (
    DoutValid_o && DoutStart_o && DoutAccept_i && Dout_o[3:0] == `READ && s_header[7:4] <= 7 |=>
    !DoutValid_o ##1
    DoutValid_o && !DoutStart_o && !DoutStop_o && Dout_o == s_data
  );

  // Read ack data zero if address is invalid
  read_ack_data_invalid_a : assert property (
    DoutValid_o && DoutStart_o && DoutAccept_i && Dout_o[3:0] == `READ && s_header[7:4] > 7 |=>
    !DoutValid_o ##1
    DoutValid_o && !DoutStart_o && !DoutStop_o && Dout_o == 0
  );

  // Register write in SET_DATA if valid adress was given
  set_data_valid_a : assert property (
    s_fsm_state == 3 && DinValid_i && DinAccept_o && DinStop_i && s_header[7:4] <= 7 |=>
    s_register[s_header[7:4]] == $past(Din_i)
  );

  // Error flag set & no register write in SET_DATA if invalid adress was given
  set_data_invalid_a : assert property (
    s_fsm_state == 3 && DinValid_i && DinAccept_o && DinStop_i && s_header[7:4] > 7 |=>
    $stable(s_register) && s_error
  );

  // No register write in SET_DATA if stop don't active
  set_data_discard_a : assert property (
    s_fsm_state == 3 && DinValid_i && DinAccept_o && !DinStop_i |=>
    $stable(s_register)
  );

  fsm_read_req_when_get_data_a : assert property (
    s_fsm_state == 2 |-> s_header[3:0] == `READ
  );

  fsm_write_req_when_set_data_a : assert property (
    s_fsm_state == 3 |-> s_header[3:0] == `WRITE
  );


endmodule


bind vai_reg properties properties (.*);
