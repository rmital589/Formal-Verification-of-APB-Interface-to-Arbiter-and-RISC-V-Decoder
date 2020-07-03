`include "constants.v"
`include "rv32_opcodes.v"
`include "alu_ops.v"

//Write your properties in a module here.
module v_decoder(
	input clk,
	input reset,
	input [31:0] inst,
	input [`IMM_TYPE_WIDTH-1:0] imm_type,
	input [`REG_SEL-1:0] rs1,
	input [`REG_SEL-1:0] rs2,
	input [`REG_SEL-1:0] rd,
	input [`SRC_A_SEL_WIDTH-1:0] src_a_sel,
	input [`SRC_B_SEL_WIDTH-1:0] src_b_sel,
	input wr_reg,
	input uses_rs1,
	input uses_rs2,
	input illegal_instruction,
	input [`ALU_OP_WIDTH-1:0] alu_op,
	input [`RS_ENT_SEL-1:0] rs_ent,
	input [2:0] dmem_size,
	input [`MEM_TYPE_WIDTH-1:0] dmem_type,
	input [`MD_OP_WIDTH-1:0] md_req_op,
	input md_req_in_1_signed,
	input md_req_in_2_signed,
	input [`MD_OUT_SEL_WIDTH-1:0] md_req_out_sel
);

wire [6:0] opcode = inst[6:0];
wire [2:0] funct3 = inst[14:12];
wire [6:0] funct7 = inst[31:25];
wire write_into_rd = ((opcode == `RV32_LOAD) | (opcode == `RV32_OP) | (opcode == `RV32_AUIPC) | (opcode == `RV32_LUI)) ? 1'b1 : 1'b0;
wire assign_low32 = (funct3 ==  `RV32_FUNCT3_MULHSU) ? 1'b1:1'b0;
wire assign_high32 = ((funct3 ==  `RV32_FUNCT3_MULH) | (funct3 ==  `RV32_FUNCT3_MULHU )) ? 1'b1:1'b0;
wire signed_1_istrue = ((funct3 ==  `RV32_FUNCT3_MULH) | (funct3 == `RV32_FUNCT3_DIV) | (funct3 == `RV32_FUNCT3_REM) )? 1'b1:1'b0;
wire signed_1_isfalse = (funct3 ==  `RV32_FUNCT3_MULHSU)? 1'b1:1'b0;
wire signed_2_istrue = (funct3 == `RV32_FUNCT3_REM)? 1'b1:1'b0;
wire signed_2_isfalse = ((funct3 ==   `RV32_FUNCT3_MULH) | (funct3 ==  `RV32_FUNCT3_DIV ))? 1'b1:1'b0; 
wire [`ALU_OP_WIDTH-1:0]  add_or_sub = ((opcode == `RV32_OP) && (funct7[5])) ? `ALU_OP_SUB : `ALU_OP_ADD;
wire [`ALU_OP_WIDTH-1:0]  srl_or_sra = (funct7[5]) ? `ALU_OP_SRL : `ALU_OP_SRA;
int flag;

reg [`ALU_OP_WIDTH-1:0] r_alu_op;
reg [`RS_ENT_SEL-1:0] r_rs_ent; 
always @(*) begin
	r_alu_op = `ALU_OP_ADD;
	r_rs_ent = `RS_ENT_ALU;
	case(opcode)
	`RV32_LOAD : begin 
			r_rs_ent = `RS_ENT_LDST;
			flag = 0;
			end
	`RV32_STORE :	begin 
			r_rs_ent = `RS_ENT_JALR; 
			flag = 1;
			end  
	`RV32_BRANCH : begin
		case(funct3)
			 `RV32_FUNCT3_BEQ : begin 
						r_alu_op = `ALU_OP_SEQ;
						flag = 2;
					    end
            		 `RV32_FUNCT3_BNE : begin 
						r_alu_op = `ALU_OP_SNE;
						flag = 3;
					    end	
            		 `RV32_FUNCT3_BLT : begin
						r_alu_op = `ALU_OP_SLT;
						flag = 4;
					    end
             		 `RV32_FUNCT3_BLTU : begin 
						r_alu_op = `ALU_OP_SLTU;
						flag = 5;
						end
             		 `RV32_FUNCT3_BGE : begin 
						r_alu_op = `ALU_OP_SGE;
						flag = 6;
						end
             		 `RV32_FUNCT3_BGEU : begin 
						r_alu_op = `ALU_OP_SGEU; 
						flag = 7;
						end
		endcase
		r_rs_ent = `RS_ENT_BRANCH;
	 end
	 `RV32_JAL : begin 
				r_rs_ent = `RS_ENT_JAL;
				flag = 8;
			end
	 `RV32_JALR : begin 
				r_rs_ent = `RS_ENT_JALR;
				flag = 9;
			end
	 `RV32_OP_IMM : begin
				if(!funct7[0])
					begin
				 case (funct3)
        `RV32_FUNCT3_ADD_SUB : begin
				r_alu_op = add_or_sub;
				flag = (funct7[5]) ? 11 : 10 ; 
				end
                `RV32_FUNCT3_SLT : begin 
				r_alu_op = `ALU_OP_SLT;
				flag = 13;
				end
        `RV32_FUNCT3_SLTU : begin 
				r_alu_op = `ALU_OP_SLTU;
				flag = 14;
				end
        `RV32_FUNCT3_XOR : begin 
				r_alu_op = `ALU_OP_XOR;
				flag = 15;
				end
        `RV32_FUNCT3_SRA_SRL : begin
				r_alu_op = srl_or_sra; 
				flag = (funct7[5]) ? 16 : 17;
			      end
        `RV32_FUNCT3_OR : begin 
				r_alu_op = `ALU_OP_OR;
				flag = 18;
				end 
        `RV32_FUNCT3_AND : begin 
					r_alu_op = `ALU_OP_AND;   
					flag = 19;
				end
	`RV32_FUNCT3_SLL : begin 
				r_alu_op = `ALU_OP_SLL; 
				flag = 12;
				end

		endcase
		end
			else 
				begin
			if(funct7 == `RV32_FUNCT7_MUL_DIV)
				r_rs_ent = ( (funct3 == `RV32_FUNCT3_MUL) || (funct3 == `RV32_FUNCT3_MULH) || (funct3 == `RV32_FUNCT3_MULHSU) ||  (funct3 == `RV32_FUNCT3_MULHU) ) ? `RS_ENT_MUL : `RS_ENT_DIV;

				case(funct3)
		`RV32_FUNCT3_MUL : flag = 20;
		`RV32_FUNCT3_MULH : flag = 21;
		`RV32_FUNCT3_MULHSU : flag = 22;
		`RV32_FUNCT3_MULHU : flag = 23;
		`RV32_FUNCT3_DIV : flag = 24;
		`RV32_FUNCT3_DIVU : flag = 25;
		`RV32_FUNCT3_REM : flag = 26;
		`RV32_FUNCT3_REMU : flag = 27;
			endcase
			end
		end
     	
	 `RV32_OP  : begin
			if(!funct7[0])
				begin
				 case (funct3)
        `RV32_FUNCT3_ADD_SUB : r_alu_op = add_or_sub;
        `RV32_FUNCT3_SLT : r_alu_op = `ALU_OP_SLT;
        `RV32_FUNCT3_SLTU : r_alu_op = `ALU_OP_SLTU;
        `RV32_FUNCT3_XOR : r_alu_op = `ALU_OP_XOR;
        `RV32_FUNCT3_SRA_SRL : r_alu_op = srl_or_sra; 
        `RV32_FUNCT3_OR : r_alu_op = `ALU_OP_OR;
        `RV32_FUNCT3_AND : r_alu_op = `ALU_OP_AND;   
	`RV32_FUNCT3_SLL: r_alu_op = `ALU_OP_SLL; 
      endcase
end
	else 
				begin
			if(funct7 == `RV32_FUNCT7_MUL_DIV)
				r_rs_ent = ( (funct3 == `RV32_FUNCT3_MUL) || (funct3 == `RV32_FUNCT3_MULH) || (funct3 == `RV32_FUNCT3_MULHSU) ||  (funct3 == `RV32_FUNCT3_MULHU) ) ? `RS_ENT_MUL : `RS_ENT_DIV;
	end
		end
	default : begin
			r_alu_op = `ALU_OP_ADD;
			r_rs_ent = `RS_ENT_ALU;
			end	
	endcase
end
 
assert property (@(posedge clk) disable iff(reset) write_into_rd |-> wr_reg);

assert property (@(posedge clk) disable iff(reset) assign_low32 |-> md_req_out_sel == `MD_OUT_LO);
assert property (@(posedge clk) disable iff(reset) assign_high32 |-> md_req_out_sel == `MD_OUT_HI); 
assert property (@(posedge clk) disable iff(reset) signed_1_istrue |-> md_req_in_1_signed);
assert property (@(posedge clk) disable iff(reset) signed_1_isfalse |-> !md_req_in_1_signed);
assert property (@(posedge clk) disable iff(reset) signed_2_istrue |-> md_req_in_2_signed);
assert property (@(posedge clk) disable iff(reset) signed_2_isfalse |-> !md_req_in_2_signed);
assert property (@(posedge clk) disable iff(reset) r_alu_op == alu_op);
assert property (@(posedge clk) disable iff(reset) r_rs_ent == rs_ent);

genvar i;
for(i=0;i<30;i++) begin
	cover property( @(posedge clk) disable iff(reset) $fell(reset) ##[0:$] flag==i);
end

endmodule
module Wrapper;
//BIND HERE 
	bind decoder v_decoder w1 (
	.clk(clk),
	.reset(reset),
	.inst(inst),
	.imm_type(imm_type),
	.rs1(rs1),
	.rs2(rs2),
	.rd(rd),
	.src_a_sel(src_a_sel),
	.src_b_sel(src_b_sel),
	.wr_reg(wr_reg),
	.uses_rs1(uses_rs1),
	.uses_rs2(uses_rs2),
	.illegal_instruction(illegal_instruction),
	.alu_op(alu_op),
	.rs_ent(rs_ent),
	.dmem_size(dmem_size),
	.dmem_type(dmem_type),
	.md_req_op(md_req_op),
	.md_req_in_1_signed(md_req_in_1_signed),
	.md_req_in_2_signed(md_req_in_2_signed),
	.md_req_out_sel(md_req_out_sel)
);                                                            
endmodule                                                    
                                                             
                                                                                                                                        
                                                            
