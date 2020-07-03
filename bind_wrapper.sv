//EE382M-Verification of Digital Systems
//Lab 4 - Formal Property Verification
//
//
//Modules - apb_props and Wrapper
//SystemVerilog Properties for the module - arbiter_top

module apb_props(
// APB interface
input        PCLK,
input        PRESETn,
input        PWRITE,
input        PSEL,
input        PENABLE,
input  [7:0] PADDR,
input  [7:0] PWDATA,

input  [7:0] PRDATA,
input        PREADY,
// APB registers
input        APB_BYPASS,
input  [3:0] APB_REQ,
input  [2:0] APB_ARB_TYPE,
// Arbiter ports
input  [3:0] REQ,
input  [3:0] GNT
);

   wire      idle,setup,access;
   wire      read,write;
   assign read = PREADY & ~PWRITE;
   assign write = PREADY & PWRITE;
   assign idle = ~PSEL &  ~PENABLE;
   assign setup = PSEL &  ~PENABLE;
   assign access = PSEL &  PENABLE;

   reg [7:0] r_bypass,r_req,r_arb_type;
   reg [7:0] r_prdata;
   

   always @(posedge PCLK or negedge PRESETn) begin
      if(!PRESETn) begin
	 r_bypass <= 0;
	 r_req <=0;
	 r_arb_type <=8'h04;
      end
      else begin
	 if(PREADY &  PWRITE) begin
	    if(PADDR == 8'h10)
	      r_bypass <= PWDATA;
	    if(PADDR == 8'h14)
	      r_req <= PWDATA;
	    if(PADDR == 8'h1C)
	      r_arb_type <= PWDATA;
	    end
	 end

   end // always @ (posedge PCLK or negedge PRESETn)

   always @(*) begin
     
	 if(PREADY & ~PWRITE) begin
	     if(PADDR == 8'h10)
	       r_prdata <= r_bypass;
	    if(PADDR == 8'h14)
	      r_prdata <= r_req;
	    if(PADDR == 8'h1C)
	      r_prdata <= r_arb_type;
	    end
	 else
	   r_prdata <= 0;
      end
   
//Write APB interface properties here - assertions, cover properties and assume properties
  
   
  // assume property(@(posedge PCLK)   setup ##1 access ##1 idle );

  // assume property(@(posedge PCLK)  PSEL  |-> ($stable(PWRITE) && !$isunknown(PWRITE)) );
 //  assume property(@(posedge PCLK)  PSEL  |-> ($stable(PADDR) && !$isunknown(PADDR)) );
 // assume property(@(posedge PCLK)  PSEL  |-> ($stable(PWDATA) && !$isunknown(PWDATA))  );
 // assume property(PADDR == 8'h10 or PADDR == 8'h14 or PADDR == 8'h1C);
 //  assume property(@(posedge PCLK)  PADDR == 8'h10 |-> (PWDATA == 8'h00 or PWDATA == 8'h10) );

 /*  property apb_write_check;
      @(posedge PCLK)
	disable iff(!PRESETn)
	if(PREADY & PWRITE & ( PADDR == 8'h10) )
	  APB_BYPASS = ~r_bypass[0];
        if(PREADY & PWRITE & ( PADDR == 8'h14))
	  APB_REQ = r_req[3:0];
        if(PREADY & PWRITE & (PADDR == 8'h1C))
	  APB_ARB_TYPE == r_arb_type[2:0];
      endproperty

   property apb_read_check;
      @(posedge PCLK)
	disable iff(!PRESETn)
	if(PREADY & ~PWRITE)
	  PRDATA = r_prdata;
      endproperty

   property reset_check;
      @(negedge PRESETn)
	if(!PRESETn) begin
	   APB_BYPASS = 0;
	   APB_REQ = 0;
	   APB_ARB_TYPE = 3'd4;
	end
      endproperty

   assert property(apb_write_check);
   assert property(apb_read_check);
   assert property(reset_check); */

   assert property(@(posedge PCLK) disable iff(!PRESETn) (PREADY & PWRITE &  PADDR == 8'h10)  |=>  (APB_BYPASS == r_bypass[0]));
   assert property(@(posedge PCLK) disable iff(!PRESETn) (PREADY & PWRITE &  PADDR == 8'h14)  |=>  (APB_REQ == r_req[3:0]));
   assert property(@(posedge PCLK) disable iff(!PRESETn) (PREADY & PWRITE &  PADDR == 8'h1C)  |=>  (APB_ARB_TYPE == r_arb_type[2:0]));
   assert property(@(posedge PCLK) disable iff(!PRESETn) (PREADY & ~PWRITE) |-> PRDATA == r_prdata);
   assert property(@(posedge PCLK) $rose(PRESETn) |-> (APB_BYPASS == 0 and APB_REQ == 0 and APB_ARB_TYPE == 3'd4));

   cover property(@(posedge PCLK)  idle  ##[1:$] read);
   cover property(@(posedge PCLK)  idle  ##[1:$] write);
           
   
endmodule

module arb_props (
  clk,
  rst_n,
  req,
  arb_type,
  gnt
  );

input        clk;
input        rst_n;
input  [3:0] req;
input  [2:0] arb_type;

input  [3:0] gnt;

   reg [3:0] r_gnt_p0,r_gnt_p1,r_gnt_p2,r_gnt_p3;
   

//Write arbiter properties here - assertions, cover properties and assume properties

 /*  genvar    i;
   for(i=0;i<4;i++) begin
      assume property(@(posedge clk)  req[i] & ~gnt[i] ##1 $stable(req[i]));
      assume property(@(posedge clk)  req[i] & gnt[i] ##1 ~req[i]);
      end */
  /* property req0_check;
      @(posedge clk)
	disable iff(!rst_n)
	  if(req[0] & ~gnt[0])
	    ##1 $stable(req[0]);
          if(req[0] & gnt[0])
	    ##1 !req[0];
    endproperty

    property req1_check;
      @(posedge clk)
	disable iff(!rst_n)
	  if(req[1] & ~gnt[1])
	    ##1 $stable(req[1]);
          if(req[1] & gnt[1])
	    ##1 !req[1];
    endproperty

    property req2_check;
      @(posedge clk)
	disable iff(!rst_n)
	  if(req[2] & ~gnt[2])
	    ##1 $stable(req[2]);
          if(req[2] & gnt[2])
	    ##1 !req[2];
    endproperty

    property req3_check;
      @(posedge clk)
	disable iff(!rst_n)
	  if(req[3] & ~gnt[3])
	    ##1 $stable(req[3]);
          if(req[3] & gnt[3])
	    ##1 !req[3];
    endproperty
   
   assume property(req0_check);
   assume property(req1_check);
   assume property(req2_check);
   assume property(req3_check);
 */
   assert property(@(posedge clk) disable iff(!rst_n) $onehot(gnt) or gnt == 4'd0);
   genvar i;
   for(i=0;i<4;i++) begin
      assert property(@(posedge clk) disable iff(!rst_n) gnt[i] |-> gnt[i] && $past(req[i],1) );
      end

   always @(*) begin
  if(req[0])
    r_gnt_p0 = 4'b0001;
  else if(req[1])
    r_gnt_p0 = 4'b0010;
  else if(req[2])
    r_gnt_p0 = 4'b0100;
  else if(req[3])
    r_gnt_p0 = 4'b1000;
  else
    r_gnt_p0 = 4'b0000;
end

// P1 Fixed Priority req[1]
always @(*) begin
  if(req[1])
    r_gnt_p1 = 4'b0010;
  else if(req[0])
    r_gnt_p1 = 4'b0001;
  else if(req[2])
    r_gnt_p1 = 4'b0100;
  else if(req[3])
    r_gnt_p1 = 4'b1000;
  else
    r_gnt_p1 = 4'b0000;
end

// P2 Fixed Priority req[2]
always @(*) begin
  if(req[2])
    r_gnt_p2 = 4'b0100;
  else if(req[0])
    r_gnt_p2 = 4'b0001;
  else if(req[1])
    r_gnt_p2 = 4'b0010;
  else if(req[3])
    r_gnt_p2 = 4'b1000;
  else
    r_gnt_p2 = 4'b0000;
end

// P3 Fixed Priority req[3]
always @(*) begin
  if(req[3])
    r_gnt_p3 = 4'b1000;
  else if(req[0])
    r_gnt_p3 = 4'b0001;
  else if(req[1])
    r_gnt_p3 = 4'b0010;
  else if(req[2])
    r_gnt_p3 = 4'b0100;
  else
    r_gnt_p3 = 4'b0000;
end

   reg [3:0] r_gnt;
   always @(posedge clk or negedge rst_n)
begin
  if(!rst_n)
    r_gnt <= 4'b0000;
  else
    case(arb_type)
      3'b000: r_gnt <= r_gnt_p0;
      3'b001: r_gnt <= r_gnt_p1;
      3'b010: r_gnt <= r_gnt_p2;
      3'b011: r_gnt <= r_gnt_p3;
      default: r_gnt <= 4'b0000;
    endcase
end

   

   assert property(@(posedge clk) disable iff(!rst_n) (arb_type == 3'd1) or (arb_type == 3'd2) or (arb_type == 3'd3) or (arb_type ==3'd0) |=> gnt == r_gnt);
   
   
     assert property(@(posedge clk) disable iff(!rst_n) (arb_type == 3'd4 && req !=0) |=>  ##[0:3] gnt!=0);
     assert property(@(posedge clk) disable iff(!rst_n) (arb_type == 3'd5 && req !=0) |=>  ##[0:7] gnt!=0);
   

   genvar j;
   for(j=0;j<4;j++) begin
      cover property(@(posedge clk) disable iff(!rst_n) $rose(rst_n) ##[0:$] req[j]);
      cover property(@(posedge clk) disable iff(!rst_n) $rose(rst_n) ##[0:$] gnt[j]); 
      end
  
	    
   
endmodule

module Wrapper;

//Bind the 'apb_props' module with the 'arbiter_top' module to instantiate the properties
   bind apb_slave apb_props w1 (
 				.PCLK(PCLK),
				.PRESETn(PRESETn),
				.PADDR(PADDR),
				.PWRITE(PWRITE),
				.PSEL(PSEL),
				.PENABLE(PENABLE),
				.PWDATA(PWDATA),
				.PRDATA(PRDATA),
				.PREADY(PREADY),
				.APB_BYPASS(APB_BYPASS),
				.APB_REQ(APB_REQ),
				.APB_ARB_TYPE(APB_ARB_TYPE)
	);
   

//Bind the 'arb_props' module with the 'arbiter' module to instantiate the properties
   bind arbiter arb_props w2 (
			      .clk(clk),
			      .rst_n(rst_n),
			      .req(req),
			      .arb_type(arb_type),
			      .gnt(gnt)
 );
   

endmodule

