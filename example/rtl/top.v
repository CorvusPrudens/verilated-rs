//  Copyright (C) 2018 Dan Glastonbury <dan.glastonbury@gmail.com>

module top(
    clk_i,
    rst_i,
    count_o,
    count_i
);

    input clk_i;
    input rst_i;
    output [127:0] count_o;
    input  [127:0] count_i;
   
    // 4-bit counter
    counter uut(
        .clk_i(clk_i),
        .rst_i(rst_i),
        .count_o(count_o)
    );
   
endmodule
