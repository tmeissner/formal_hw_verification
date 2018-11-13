library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;



entity dlatch is
  generic (
    Init : std_logic_vector(31 downto 0) := x"DEADBEEF"
  );
  port (
    Reset_n_i : in  std_logic;
    Clk_i     : in  std_logic;
    Wen_i     : in  std_logic;
    Data_i    : in  std_logic_vector(15 downto 0);
    Data_o    : out std_logic_vector(31 downto 0)
  );
end entity dlatch;



architecture rtl of dlatch is


begin


  process (Reset_n_i, Clk_i) is
  begin
    if (Reset_n_i = '0') then
      Data_o <= Init;
    elsif (rising_edge(Clk_i)) then
      if (Wen_i = '1') then
        Data_o(7 downto 0) <= Data_i(7 downto 0);
	Data_o(23 downto 16) <= Data_i(15 downto 8);
      end if;
    end if;
  end process;


end architecture rtl;

