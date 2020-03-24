library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;



entity counter is
  generic (
    InitVal : natural := 0;
    EndVal  : natural := 16;
    Formal  : boolean := true
  );
  port (
    Reset_n_i : in  std_logic;
    Clk_i     : in  std_logic;
    Data_o    : out std_logic_vector(31 downto 0)
  );
end entity counter;



architecture rtl of counter is


begin


  process (Reset_n_i, Clk_i) is
  begin
    if (Reset_n_i = '0') then
      Data_o <= std_logic_vector(to_unsigned(InitVal, Data_o'length));
    elsif (rising_edge(Clk_i)) then
      if (to_integer(unsigned(Data_o)) < EndVal) then
        Data_o <= std_logic_vector(unsigned(Data_o) + 1);
      end if;
    end if;
  end process;


  FormalG : if Formal generate

    signal s_data : unsigned(Data_o'range);

  begin

    -- VHDL helper logic
    process is
    begin
      wait until rising_edge(Clk_i);
      s_data <= unsigned(Data_o);
    end process;

    default clock is rising_edge(Clk_i);

    -- Initial reset
    INITIAL_RESET : restrict {Reset_n_i = '0'[*2]; Reset_n_i = '1'[+]}[*1];

    AFTER_RESET : assert always
      not Reset_n_i -> Data_o = (Data_o'range => '0');

    COUNT_UP : assert always
      Reset_n_i and unsigned(Data_o) < to_unsigned(EndVal, 32) -> next unsigned(Data_o) = s_data + 1;

    END_VALUE : assert always
      unsigned(Data_o) = to_unsigned(EndVal, 32) -> next unsigned(Data_o) = s_data;

    VALID_RANGE : assert always
      unsigned(Data_o) >= to_unsigned(InitVal, 32) and
      unsigned(Data_o) <= to_unsigned(EndVal, 32);

  end generate FormalG;


end architecture rtl;

