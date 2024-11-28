module add_constant #(parameter int N = 0, parameter int M = 0) (
    input[7:0] in, 
    output[7:0] out
);
    assign out = in + N + M;
endmodule
