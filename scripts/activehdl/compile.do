vlib work
vlib activehdl

vlib activehdl/xil_defaultlib

vmap xil_defaultlib activehdl/xil_defaultlib

vlog -work xil_defaultlib  -sv2k12 \
"../../src/fifo_generic.sv" \
"../../sim/fifo_tb.sv" \


vlog -work xil_defaultlib \
"glbl.v"

