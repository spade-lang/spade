`include "vatch/main.v"

module counter_tb();
    `SETUP_TEST

    reg clk;
    reg rst;

    initial begin
        $dumpfile(`VCD_OUTPUT);
        $dumpvars(0, counter_tb);
        clk = 1;
        forever begin
            clk = ~clk;
            #1;
        end
    end


    reg[7:0] variant;
    wire result;

    initial begin
        rst <= 1;
        #1;
        #1;
        #1;
        rst <= 0;

        `ASSERT_EQ(result, 0);

        #20

        `END_TEST
    end

    \spi_receiver uut
        ( .clk_i(clk)
        , .rst_i(rst)
        , .output__(result)
        );
endmodule
