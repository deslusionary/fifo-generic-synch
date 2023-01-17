###############################################
# Filename: Makefile
# Author: Christopher Tinker
# Date: 2022/09/27
#
# Description:
# 	Makefile for building Xilinx/Vivado FPGA projects
###############################################

#### Makefile Variables ###
# General
SHELL = /bin/bash

# Vivado
BUILD_DIR = build
VIVADO_FLAGS = -mode batch -journal ./build/$(1).jou \
			   -log ./build/$(1).log

# CocoTB
# SIM ?= icarus
# TOPLEVEL_LANG ?= verilog
# TOPLEVEL = fifo_generic
# MODULE = fifo_generic_tb
# VERILOG_SOURCES += fifo_generic.sv
# include $(shell cocotb-config --makefiles)/Makefile.sim


### Vivado Synthesis ###

#RTL_SRC = ./src/fifo_generic.sv
#XDC_SRC = ./constraints/
SCRIPT_SRC = scripts
#IP_SRC =
#BD_SRC =
#SIM_SRC =


all: $(BUILD_DIR)/bitstream.bit

synthesis: $(BUILD_DIR)/post_synth.dcp

impl: $(BUILD_DIR)/post_impl.dcp

bitstream: $(BUILD_DIR)/bitstream.bit


$(BUILD_DIR)/bitstream.bit: build/post_impl.dcp
	vivado -source $(SCRIPT_SRC)/bitstream.tcl $(call VIVADO_FLAGS,bitstream)

$(BUILD_DIR)/post_impl.dcp: build/post_synth.dcp
	vivado -source $(SCRIPT_SRC)/impl.tcl $(call VIVADO_FLAGS,impl)

$(BUILD_DIR)/post_synth.dcp: ./src/fifo_generic.sv
#	source ~/Vivado/2022.1/settings64.sh
	vivado -source $(SCRIPT_SRC)/synth.tcl $(call VIVADO_FLAGS,synth)


### Simulation ###
xsim: 
	vivado -source $(SCRIPT_SRC)/sim.tcl $(call VIVADO_FLAGS,sim)

### Maintenance ###
.phony:
cleanbuild:
	rm build/*

.PHONY: xsim cleanbuild