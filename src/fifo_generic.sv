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
    integer fifo_count = 0;
    logic [mem_addr_width : 0] pointer_diff;

    initial begin 
        past_valid = 0;
        i_rst = 1;
    end

    // Determine if the previous state is a valid one
    always_ff @(posedge clk) begin
        i_rst <= 0;
        if (!i_rst) past_valid <= 1;
    end

    // calculate number of items in FIFO by counting reads and writes
    always_ff @(posedge clk) begin
        if (i_rst) fifo_count <= 0;
        else if (write_en && !read_en && fifo_count < FifoDepth) begin
            fifo_count <= fifo_count + 1'b1;
        end
        else if (!write_en && read_en && fifo_count > 0) begin
            fifo_count <= fifo_count - 1'b1;
        end
    end

    // generate number of items in FIFO from pointer addresses
    always_comb begin
        if (read_ptr < write_ptr || read_ptr == write_ptr) pointer_diff <= write_ptr - read_ptr;
        else pointer_diff <= (2 * FifoDepth) + write_ptr - read_ptr;
    end

    // Test Cases
    always_ff @(posedge clk) begin

        if (past_valid) begin
            fifo_count_inc : assert(fifo_count == $past(fifo_count) + 1'b1 
                                    || fifo_count == $past(fifo_count) - 1'b1
                                    || fifo_count == $past(fifo_count)
                                    || fifo_count == 0);

            fifo_items: assert(fifo_count == pointer_diff);

            number_items: assert(fifo_count < FifoDepth || fifo_count == FifoDepth);

            read_ptr_inc: assert(read_ptr == $past(read_ptr)
                                || read_ptr == $past(read_ptr) + 1'b1);

            write_ptr_inc: assert(write_ptr == $past(write_ptr)
                                  || write_ptr == $past(write_ptr) + 1'b1);
            
            // Underflow proofs
            if (i_read && fifo_count == 0) underflow_read_en: assert(read_en == 1'b0);
            
            // Test that read pointer does not increment if a read
            // while FIFO is empty is attempted
            if ($past(i_read) && $past(fifo_count) == 0) begin
                underflow_read_ptr: assert(read_ptr == $past(read_ptr));
            end

            // Overflow proofs
            if (i_write && fifo_count == FifoDepth) begin
                overflow_write_en: assert(write_en == 1'b0);
            end

            if ($past(i_write) && $past(fifo_count) == FifoDepth) begin
                overflow_write_ptr: assert(write_ptr == $past(write_ptr));
            end

            cover_read_write: cover(i_write && i_read && fifo_count == FifoDepth);
            cover (o_empty == o_full);


            if (fifo_count == FifoDepth) full: assert(o_full == 1'b1);
            if (fifo_count == 0) empty: assert(o_empty == 1'b1);
        end
    end         
    
    // Do some assertion checks
    // assert property (@(posedge clk) disable iff (i_rst) ($rose(i_write) |=> !o_empty)) $display("assertion passed");
    // else begin
    //     $display("assertion failed");
    // end

`endif
     
endmodule
