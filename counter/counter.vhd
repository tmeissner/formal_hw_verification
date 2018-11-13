library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;



entity counter is
  generic (
    Init : natural := 8
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
      Data_o <= std_logic_vector(to_unsigned(Init, Data_o'length));
    elsif (rising_edge(Clk_i)) then
      if (unsigned(Data_o) <= 64) then
        Data_o <= std_logic_vector(unsigned(Data_o) + 1);
      end if;
    end if;
  end process;


end architecture rtl;

