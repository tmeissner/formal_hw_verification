library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;



entity alu is
  generic (
    Width  : natural := 8;
    Formal : boolean := true
  );
  port (
    Reset_n_i  : in  std_logic;
    Clk_i      : in  std_logic;
    Opc_i      : in  std_logic_vector(1 downto 0);
    DinA_i     : in  std_logic_vector(Width-1 downto 0);
    DinB_i     : in  std_logic_vector(Width-1 downto 0);
    Dout_o     : out std_logic_vector(Width-1 downto 0);
    OverFlow_o : out std_logic
  );
end entity alu;



architecture rtl of alu is


  subtype t_opc is std_logic_vector(Opc_i'range);

  constant c_add : t_opc := "00";
  constant c_sub : t_opc := "01";
  constant c_and : t_opc := "10";
  constant c_or  : t_opc := "11";


begin


  process (Reset_n_i, Clk_i) is
    variable v_result : std_logic_vector(Width downto 0);
  begin
    if (Reset_n_i = '0') then
      v_result   := (others => '0');
      Dout_o     <= (others => '0');
      OverFlow_o <= '0';
    elsif (rising_edge(Clk_i)) then
      case Opc_i is
        when c_add =>
          v_result := std_logic_vector(unsigned('0' & DinA_i) +
                                       unsigned('0' & DinB_i));
        when c_sub =>
          v_result := std_logic_vector(unsigned('0' & DinA_i) -
                                       unsigned('0' & DinB_i));
        when c_and => v_result := DinA_i and DinB_i;
        when c_or  => v_result := DinA_i or  DinB_i;
        when others => null;
      end case;
      Dout_o     <= v_result(Width-1 downto 0);
      OverFlow_o <= v_result(Width);
    end if;
  end process;


  FormalG : if Formal generate

    signal s_dina : std_logic_vector(DinA_i'range);
    signal s_dinb : std_logic_vector(DinB_i'range);

    function max(a, b: std_logic_vector) return unsigned is
    begin
      if unsigned(a) > unsigned(b) then
        return unsigned(a);
      else
        return unsigned(b);
      end if;
    end function max;

  begin

    -- VHDL helper logic
    process is
    begin
      wait until rising_edge(Clk_i);
      s_dina <= DinA_i;
      s_dinb <= DinB_i;
    end process;


    default clock is rising_edge(Clk_i);

    AFTER_RESET : assert always
      not Reset_n_i -> Dout_o = (Dout_o'range => '0') and OverFlow_o = '0';

    ADD_OP : assert Reset_n_i and Opc_i = c_add ->
      next unsigned(Dout_o) = unsigned(s_dina) + unsigned(s_dinb) abort not Reset_n_i;

    SUB_OP : assert Reset_n_i and Opc_i = c_sub ->
      next unsigned(Dout_o) = unsigned(s_dina) - unsigned(s_dinb) abort not Reset_n_i;

    AND_OP : assert Reset_n_i and Opc_i = c_and ->
      next Dout_o = (s_dina and s_dinb) abort not Reset_n_i;

    OR_OP :  assert Reset_n_i and Opc_i = c_or ->
      next Dout_o = (s_dina or s_dinb) abort not Reset_n_i;

    OVERFLOW_ADD : assert Reset_n_i and Opc_i = c_add and (unsigned(DinA_i) + unsigned(DinB_i)) < max(DinA_i, DinB_i) ->
      next OverFlow_o abort not Reset_n_i;

    NOT_OVERFLOW_ADD : assert Reset_n_i and Opc_i = c_add and (unsigned(DinA_i) + unsigned(DinB_i)) >= max(DinA_i, DinB_i) ->
      next not OverFlow_o abort not Reset_n_i;

    OVERFLOW_SUB : assert Reset_n_i and Opc_i = c_sub and (unsigned(DinA_i) - unsigned(DinB_i)) > unsigned(DinA_i) ->
      next OverFlow_o abort not Reset_n_i;

    NOT_OVERFLOW_SUB : assert Reset_n_i and Opc_i = c_sub and (unsigned(DinA_i) - unsigned(DinB_i)) <= unsigned(DinA_i) ->
      next not OverFlow_o abort not Reset_n_i;

  end generate FormalG;


end architecture rtl;
