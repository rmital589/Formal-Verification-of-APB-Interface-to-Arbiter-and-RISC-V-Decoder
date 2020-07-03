#Tcl script which can be used with JasperGold
#Use "source lab4.tcl" in the console to source this script
clear -all
#Reading the files (.v and .sv) 
analyze -v2k apb_parameters.v
analyze -v2k apb_slave.v
analyze -v2k arbiter.v
analyze -v2k arbiter_top.v
analyze -v2k PNSeqGen.v
analyze -sv bind_wrapper.sv
#Elaborating the design, specify the top module
elaborate -top arbiter_top
#You may  need to add commands below

#Set the clock
clock PCLK
#Set Reset

reset -expression  {!(PRESETn)}
#Prove all
prove -bg -all
