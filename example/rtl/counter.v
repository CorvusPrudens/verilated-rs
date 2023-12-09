//  Copyright (C) 2018 Dan Glastonbury <dan.glastonbury@gmail.com>

module counter(
    clk_i,
    rst_i,
    count_o
);

    input clk_i;
    input rst_i;

    output [127:0] count_o;
    reg [127:0]    count_o;
   
    always @(posedge clk_i)
      begin
        if (rst_i == 1'b1) begin
            count_o <= 128'b0;
        end
        else begin
            count_o <= count_o + 1;
        end
    end
   
endmodule
