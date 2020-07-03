#Tcl script which can be used with JasperGold
#Use "source lab4_pb.tcl" in the console to source this script
clear -all
#Reading the files 
analyze -v2k alu_ops.v
analyze -v2k constants.v
analyze -v2k decoder.v
analyze -v2k rv32_opcodes.v
analyze -sv v_decoder.sv 
#Elaborating the design
elaborate -top decoder

#Set the clock
clock clk
#Set Reset
reset reset
#Prove all
prove -bg -all



