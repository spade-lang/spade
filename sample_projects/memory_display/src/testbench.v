`include "../../output_test/vatch/main.v"

module spi_tx_tb();
    reg clk;

    `SETUP_TEST

    initial begin
        $dumpfile(`VCD_OUTPUT);
        $dumpvars(0, spi_tx_tb);
        clk = 1;
        forever begin
            clk = ~clk;
            #1;
        end
    end


    reg rst;
    wire cs;
    wire mosi;
    wire sclk;
    wire busy;
    reg[8:0] to_transmit;

    integer i;

    initial begin
        rst = 1;
        #4
        rst = 0;

        #400000

        `END_TEST
    end

    main uut
        ( ._i_clk(clk)
        , ._i_rst(rst)
        , .__output({cs, mosi, sclk})
        );
endmodule
