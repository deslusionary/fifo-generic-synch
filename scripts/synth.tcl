###############################################
# Filename: synth.tcl
# Author: Christopher Tinker
# Date: 2022/09/27
#
# Description:
#   Generic TCL script for Vivado synthesis
#   Items to modify for new project:
#       - Set build output directory, FPGA part number, and top module name
#       - Each HDL source file must be read w/ read_verilog or read_vhdl
#       - Constraints file must be read with read_xdc
###############################################


# This script is called by 'make synthesis'so all filepaths 
# are referenced from the top level project directory containing
# the makefile.

#set RTL_SRC [lindex $argv 0]
#set XDC_SRC [lindex $argv 1]

#set INC_DIR0 [lindex $argv 2]
#set IP_SRC [lindex $argv 3]
#set BD_SRC [lindex $argv 4]

set outputDir "./build"
set partNum XC7A35TICSG324-1L
set synthTop fifo_generic
set synthName fifo_generic

# Read HDL source files
read_verilog -sv src/fifo_generic.sv

# read constraints
read_xdc constraints/constraints.xdc

# Synthesis
synth_design -top $synthTop -part $partNum -name synthName -verbose
opt_design

report_timing_summary -file $outputDir/synth_timing_summary.txt -nworst 10
report_utilization -file $outputDir/synth_util.txt


# Write post-synthesis design checkpoint
write_checkpoint -force $outputDir/post_synth
