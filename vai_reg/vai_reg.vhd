library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;



entity vai_reg is
  port (
    Reset_n_i    : in  std_logic;
    Clk_i        : in  std_logic;
    -- req
    Din_i        : in  std_logic_vector(7 downto 0);
    DinValid_i   : in  std_logic;
    DinStart_i   : in  std_logic;
    DinStop_i    : in  std_logic;
    DinAccept_o  : out std_logic;
    -- ack
    Dout_o       : out std_logic_vector(7 downto 0);
    DoutValid_o  : out std_logic;
    DoutStart_o  : out std_logic;
    DoutStop_o   : out std_logic;
    DoutAccept_i : in  std_logic
  );
end entity vai_reg;



architecture rtl of vai_reg is


  constant C_READ  : std_logic_vector(3 downto 0) := x"0";
  constant C_WRITE : std_logic_vector(3 downto 0) := x"1";

  type t_fsm_state is (IDLE, GET_HEADER, GET_DATA,
                       SET_DATA, SEND_HEADER, SEND_DATA, SEND_FOOTER);
  signal s_fsm_state : t_fsm_state;

  type t_register is array(0 to 7) of std_logic_vector(7 downto 0);
  signal s_register : t_register;

  signal s_header : std_logic_vector(7 downto 0);
  signal s_data   : std_logic_vector(7 downto 0);

  signal s_error : boolean;
  signal s_dout_accepted : boolean;

  alias a_addr : std_logic_vector(3 downto 0) is s_header(7 downto 4);


begin


  s_dout_accepted <= (DoutValid_o and DoutAccept_i) = '1';


  process (Reset_n_i, Clk_i) is
  begin
    if (Reset_n_i = '0') then
      DinAccept_o <= '0';
      DoutStart_o <= '0';
      DoutStop_o  <= '0';
      DoutValid_o <= '0';
      Dout_o      <= (others => '0');
      s_header    <= (others => '0');
      s_data      <= (others => '0');
      s_register  <= (others => (others => '0'));
      s_error     <= false;
      s_fsm_state <= IDLE;
    elsif (rising_edge(Clk_i)) then
      case s_fsm_state is

        when IDLE =>
          DinAccept_o <= '0';
          DoutStart_o <= '0';
          DoutStop_o  <= '0';
          DoutValid_o <= '0';
          Dout_o      <= (others => '0');
          s_header    <= (others => '0');
          s_data      <= (others => '0');
          s_error     <= false;
          DinAccept_o <= '1';
          s_fsm_state <= GET_HEADER;

        when GET_HEADER =>
          if (DinValid_i = '1' and DinStart_i = '1') then
            s_header    <= Din_i;
            if (Din_i(3 downto 0) = C_READ and DinStop_i = '1') then
              DinAccept_o <= '0';
              s_fsm_state <= GET_DATA;
            elsif (Din_i(3 downto 0) = C_WRITE and DinStop_i = '0') then
              s_fsm_state <= SET_DATA;
            else
              DinAccept_o <= '0';
              s_fsm_state <= IDLE;
            end if;
          end if;

        when GET_DATA =>
          if (unsigned(a_addr) <= 7) then
            s_data <= s_register(to_integer(unsigned(a_addr)));
          else
            s_error <= true;
            s_data  <= (others => '0');
          end if;
          s_fsm_state <= SEND_HEADER;

        when SET_DATA =>
          if (DinValid_i = '1') then
            DinAccept_o <= '0';
            if (DinStop_i = '1') then
              if (unsigned(a_addr) <= 7) then
                s_register(to_integer(unsigned(a_addr))) <= Din_i;
              else
                s_error <= true;
              end if;
              s_fsm_state <= SEND_HEADER;
            else
              s_fsm_state <= IDLE;
            end if;
          end if;

        when SEND_HEADER =>
          DoutValid_o <= '1';
          DoutStart_o <= '1';
          Dout_o      <= s_header;
          if (s_dout_accepted) then
            DoutValid_o <= '0';
            DoutStart_o <= '0';
            if (s_header(3 downto 0) = C_WRITE) then
              s_fsm_state <= SEND_FOOTER;
            else
              s_fsm_state <= SEND_DATA;
            end if;
          end if;

        when SEND_DATA =>
          DoutValid_o <= '1';
          Dout_o      <= s_data;
          if (s_dout_accepted) then
            DoutValid_o <= '0';
            s_fsm_state <= SEND_FOOTER;
          end if;

        when SEND_FOOTER =>
          DoutValid_o <= '1';
          DoutStop_o  <= '1';
          Dout_o      <= x"01" when s_error else x"00";
          if (s_dout_accepted) then
            Dout_o      <= (others => '0');
            DoutValid_o <= '0';
            DoutStop_o  <= '0';
            s_fsm_state <= IDLE;
          end if;

        when others => null;

      end case;
    end if;
  end process;


  -- psl default clock is rising_edge(Clk_i);

  -- psl restrict {Reset_n_i = '0'[*5]; Reset_n_i = '1'[+]}[*1];
  -- psl assert always unsigned(a_addr) < 8;


end architecture rtl;

