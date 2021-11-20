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
    wire sclk;
    wire mosi;
    wire busy;
    reg[8:0] to_transmit;

    integer i;

    initial begin
        rst = 1;
        to_transmit <= 9'b100000000;
        #4
        rst = 0;

        repeat (2000) @(negedge clk);
        `ASSERT_EQ(busy, 0);
        `ASSERT_EQ(sclk, 1);

        to_transmit <= 9'b0_1011_0010;
        @(negedge clk)
        @(negedge clk)

        for (i = 0; i < 8; i = i + 1) begin
            // Clock should still be high and data set
            `ASSERT_EQ(sclk, 1);
            `ASSERT_EQ(mosi, to_transmit[i]);
            repeat(500) @(negedge clk);
            // Clock should have fallen
            `ASSERT_EQ(sclk, 0);
            repeat(500) @(negedge clk);
        end

        `ASSERT_EQ(sclk, 1);


        `ASSERT_EQ(busy, 0);

        #100

        `END_TEST
    end

    spi_tx uut
        ( ._i_clk(clk)
        , ._i_rst(rst)
        , ._i_to_transmit(to_transmit)
        , .__output({sclk, mosi, busy})
        );
endmodule
