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


module fifo_generic #(
    parameter DataWidth = 32, 
    parameter int unsigned FifoDepth = 1024 // power of 2 FIFO depths only
    ) (
    input logic                    clk,
    input logic                    i_rst,
    input logic                    i_read,
    input logic                    i_write,
    input logic  [DataWidth - 1:0] i_write_data,
    output logic [DataWidth - 1:0] o_read_data,
    output logic                   o_full,
    output logic                   o_empty
    );
    
    localparam mem_addr_width = $clog2(FifoDepth);
    
    // Variable declarations 
    logic [DataWidth - 1:0] fifo_mem[0: FifoDepth - 1]; // FIFO BRAM
    
    // FIFO pointers are one bit longer than required to address FIFO memory 
    // for full/empty differentiation
    logic [mem_addr_width:0] write_ptr;
    logic [mem_addr_width:0] read_ptr;
    
    // FIFO memory address inputs
    wire logic [mem_addr_width - 1:0] write_addr; // lower mem_addr_width bits of write_ptr
    wire logic [mem_addr_width - 1:0] read_addr; // lower mem_addr_width bits of read_ptr
    
    assign write_addr = write_ptr[mem_addr_width - 1:0];
    assign read_addr = read_ptr[mem_addr_width - 1:0];
    
    // FIFO internal signals
    logic read_en;
    logic write_en;
    wire logic addr_equal;
    wire logic ptr_msb_equal;
    
    assign read_en = (i_read && !o_empty) ? 1'b1 : 1'b0;
    assign write_en = (i_write && !o_full) ? 1'b1 : 1'b0;
    
    
    // FIFO read control  
    always_ff @(posedge clk) begin
        if (i_rst == 1'b1) begin 
            read_ptr <= 0; // reset read pointer
        end else if (read_en) begin
            read_ptr <= read_ptr + 1'b1;
        end
    end
    
    // FIFO read 
    always_ff @(posedge clk) begin
        if (read_en && !o_empty) begin
            o_read_data <= fifo_mem[read_addr];
        end
    end
   
    
    // FIFO write control 
    always_ff @(posedge clk) begin
        if (i_rst == 1'b1) begin
            write_ptr <= 0; // reset write pointer
        end else if (i_write && !o_full) begin
            write_ptr <= write_ptr + 1;
        end   
    end  
    
    // FIFO write
    always_ff @(posedge clk) begin
        if (write_en && !o_full) begin
            fifo_mem[write_addr] <= i_write_data;
        end 
    end 
    
    // compare read and write pointers
    assign addr_equal = (write_addr == read_addr) ? 1'b1 : 1'b0;
    assign ptr_msb_equal = (write_ptr[mem_addr_width] == read_ptr[mem_addr_width]) ? 1'b1 : 1'b0;
    
    assign o_empty = (addr_equal && ptr_msb_equal) ? 1'b1 : 1'b0; // empty if address equal and pointer MSB are equal
    assign o_full = (addr_equal && !ptr_msb_equal) ? 1'b1 : 1'b0; // full if address equal and pointer MSB not equal   
    

///// Formal Verification /////
`ifdef FORMAL

    logic past_valid;
    initial begin 
        past_valid = 0;
        i_rst = 1;
    end

    // Determine if the previous state is a valid one
    always_ff @(posedge clk) begin
        i_rst <= 0;
        if (!i_rst) past_valid <= 1;
    end

    // Require inputs to change on posedge clock
    
    integer count = 0;
    integer num_reads = 0;
    integer num_writes = 0;
    
    always @(posedge clk) begin
        if (past_valid && write_ptr != $past(write_ptr)) begin
            num_writes <= num_writes + 1'b1;
        end
        if (i_rst) num_writes <= 0;
        //$display("num_writes: %d", num_writes);
    end
    
    always @(posedge clk) begin
        if (past_valid && read_ptr != $past(read_ptr)) begin
            num_reads <= num_reads + 1'b1;
        end
        if (i_rst) num_reads <= 0; 
        //$display("num_reads: %d", num_reads);
    end
    
    // Assert that the number of writes never exceeds number of reads
    // or vice versa
    always_comb begin
        count = num_writes - num_reads;
        assert (count < FifoDepth || count == FifoDepth);
        assert (count > 0 || count == 0);
    end
    
    // Do some assertion checks
    // assert property (@(posedge clk) disable iff (i_rst) ($rose(i_write) |=> !o_empty)) $display("assertion passed");
    // else begin
    //     $display("assertion failed");
    // end

`endif
     
endmodule
