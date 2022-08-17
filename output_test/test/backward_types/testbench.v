`include "vatch/main.v"

module counter_tb();
    `SETUP_TEST


    reg[9:0] val;
    wire[9:0] result;

    initial begin
        val <= 10;
        #1
        `ASSERT_EQ(result, 10);

        val <= 5;
        #1
        `ASSERT_EQ(result, 5);


        #20

        `END_TEST
    end

    e_assign_through_port counter
        ( .val_i(val)
        , .output__(result)
        );
endmodule
