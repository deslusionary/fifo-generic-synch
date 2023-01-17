###############################################
# Filename: sim.tcl
# Author: Christopher Tinker
# Date: 2022/09/27
#
# Description:
#   TCL flow for Vivado simulation. Creates an in-memory Vivado project, adds sources, runs a simulation, and exits
###############################################

# Sim Variables
set sim_time = 1000ns

# Read Source Files
xvlog -sv fifo_generic.sv

# Compile testbench file
xvlog -sv ./sim/fifo_tb.sv

# Elaborate Design
xelab -top fifo_tb -snapshot tb

# Simulate and log
xsim -snapshot tb

log_wave -recursive *
run all
exit

