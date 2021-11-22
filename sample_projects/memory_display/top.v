// look in pins.pcf for all the pin names on the TinyFPGA BX board
module top (
    input clk,

    output[7:0] pmod7,
    output[3:0] pmod0,
    output[3:0] pmod0Lower
);
    // assign rst = pmod0[2];

    reg rst = 1;
    always @(posedge clk) begin
        rst <= 0;
    end

    assign pmod0Lower = pmod0;

    main main
        ( ._i_clk(clk)
        , ._i_rst(rst)
        , .__output({pmod0[2], pmod0[1], pmod0[0]})
        );
endmodule

