## Retaining the environment same as after lab4_pb.tcl add the command for the black boxing step

clear -all
#Reading the files 
analyze -v2k alu_ops.v
analyze -v2k constants.v
analyze -v2k decoder.v
analyze -v2k rv32_opcodes.v
analyze -v2k pipeline.v
#Elaborating the design
elaborate -bbox 1 -top pipeline

#Set the clock
clock clk
#Set Reset
reset reset
#Prove all
prove -bg -all