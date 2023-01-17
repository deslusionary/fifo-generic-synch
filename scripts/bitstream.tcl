###############################################
# Filename: bitstream.tcl
# Author: Christopher Tinker
# Date: 2022/09/27
#
# Description:
#   Generic TCL script for Vivado bitstream generation.
#   Called from Makefile in project top level folder
###############################################

set outputDir ./build

open_checkpoint $outputDir/post_impl.dcp


write_bitstream -force $outputDir/bitstream.bit
