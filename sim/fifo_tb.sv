`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08/28/2022 01:56:51 PM
// Design Name: 
// Module Name: fifo-generic
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

module fifo_tb ();
    
    // Declare signals 
    logic clk = 0;
    logic rst = 0;
    logic read = 0;
    logic write = 0;
    logic [31:0] write_data = 0;
    logic [31:0] read_data;
    logic full, empty;
    
    // DUT
    fifo_generic #(
        .DataWidth (32),
        .FifoDepth (8)
        ) 
        DUT (
        .clk          (clk),
        .i_rst        (rst),     
        .i_read       (read),
        .i_write      (write),
        .i_write_data (write_data),
        .o_read_data  (read_data),
        .o_full       (full),
        .o_empty      (empty)
    );
    
    // Do some tasks cause why not
    task automatic write_fifo (
        input [31:0] data,
        ref fifo_write,
        ref logic [31:0] fifo_write_data
        );
        begin
        write_data = data;
        fifo_write = 1'b1;
        #10
        fifo_write = 1'b0;  
        end  
    endtask
    
    task automatic read_fifo (
        ref fifo_read
        );
        fifo_read = 1'b1;
        #10
        fifo_read = 1'b0;
    endtask
    
    // Generate 100 MHz clock
    initial begin
        forever #5 clk = ~clk;
    end
        
    // Mediocre testbench bc I'm a dumb fuck
    initial begin
        rst = 1'b1;
        #20
        rst = 1'b0;
        #20
       // write_fifo(32'd3, write, write_data);
        
        //do 9 writes
        for (integer i = 0; i < 9; i++) begin
            write_fifo(i, write, write_data);
        end
        
        #20
        // do 5 reads
        for (integer i = 0; i < 5; i++) begin
            read_fifo(read);
        end
        
        // 4 writes
        for (integer i = 0; i < 4; i++) begin
            write_fifo(i, write, write_data);
        end
        #20
        
        // 4 reads
        for (integer i = 0; i < 4; i++) begin
            read_fifo(read);
        end
        $finish;
    end
    
endmodule




