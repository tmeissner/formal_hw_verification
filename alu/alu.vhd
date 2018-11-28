library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;



entity alu is
  generic (
    Width : natural := 8
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


  constant c_add : std_logic_vector(1 downto 0) := "00";
  constant c_sub : std_logic_vector(1 downto 0) := "01";
  constant c_and : std_logic_vector(1 downto 0) := "10";
  constant c_or  : std_logic_vector(1 downto 0) := "11";


begin


  process (Reset_n_i, Clk_i) is
  begin
    if (Reset_n_i = '0') then
      Dout_o <= (others => '0');
    elsif (rising_edge(Clk_i)) then
      case Opc_i is
        when c_add => (OverFlow_o, Dout_o) <=
	  std_logic_vector(resize(unsigned(DinA_i), Dout_o'length+1) +
	                   resize(unsigned(DinB_i), Dout_o'length+1));
        when c_sub => (OverFlow_o, Dout_o) <=
	  std_logic_vector(resize(unsigned(DinA_i), Dout_o'length+1) -
	                   resize(unsigned(DinB_i), Dout_o'length+1));
	when c_and => Dout_o <= DinA_i and DinB_i;
	when c_or  => Dout_o <= DinA_i or DinB_i;
	when others => null;
      end case;
    end if;
  end process;


end architecture rtl;

