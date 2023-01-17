###############################################
# Filename: impl.tcl
# Author: Christopher Tinker
# Date: 2022/09/27
#
# Description:
#   Generic TCL scriipt for Vivado place, route, and timing analysis
#   Update with correct output directory for each new project
###############################################
set outputDir ./build

open_checkpoint $outputDir/post_synth.dcp

place_design

# Post Place reports
report_utilization -file $outputDir/place_util.txt
report_timing -file $outputDir/place_timing.txt -nworst 10

write_checkpoint -force $outputDir/post_place

route_design

#Post route reports
report_methodology -file $outputDir/route_methodology.txt
report_timing -file $outputDir/route_timing.txt -nworst 10
report_timing_summary -file $outputDir/route_timing_summary.txt
report_high_fanout_nets -file $outputDir/fanout_nets.txt -histogram
report_io -file $outputDir/route_io_summary.txt
report_drc -file $outputDir/route_drc.txt

# Write checkpoint
write_checkpoint -force $outputDir/post_impl