// look in pins.pcf for all the pin names on the TinyFPGA BX board
module top (
    input clk,

    output[7:0] pmod7,
    input[3:0] pmod0,
    output[3:0] pmod0Lower
);
    wire rst;
    assign rst = pmod0[2];

    assign pmod0Lower = pmod0;

    main main
        ( ._i_clk(clk)
        , ._i_rst(rst)
        , ._i_sclk_unsync(pmod0[0])
        , ._i_mosi_unsync(pmod0[1])
        , .__output(pmod7)
        );
endmodule

