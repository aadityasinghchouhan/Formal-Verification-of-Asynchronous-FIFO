module wptr_full #(parameter ADDR_WIDTH = 4)(
	output logic wfull,
	output logic [ADDR_WIDTH-1:0] waddr,
	output logic [ADDR_WIDTH :0] wptr,
	input logic [ADDR_WIDTH :0] wq2_rptr,
	input logic winc, wclk, wrst_n);
	
	bit [ADDR_WIDTH:0] wbin;
	bit [ADDR_WIDTH:0] wgraynext, wbinnext;
	bit wfull_val;
	
	// GRAYSTYLE2 pointer
	always_ff @(posedge wclk or negedge wrst_n)
	begin
		if (!wrst_n) 
			{wbin, wptr} <= 0;
		else 
			{wbin, wptr} <= {wbinnext, wgraynext};
	end
	
	// Memory write-address pointer (okay to use binary to address memory)
	assign waddr = wbin[ADDR_WIDTH-1:0];
	assign wbinnext = (!wrst_n) ? 0 : (wbin + (winc & ~wfull));
	assign wgraynext = (!wrst_n) ? 0 : ((wbinnext>>1) ^ wbinnext);
	//------------------------------------------------------------------
	// Simplified version of the three necessary full-tests:
	// assign wfull_val=((wgnext[ADDR_WIDTH] !=wq2_rptr[ADDR_WIDTH] ) &&
	// (wgnext[ADDR_WIDTH-1] !=wq2_rptr[ADDR_WIDTH-1]) &&
	// (wgnext[ADDR_WIDTH-2:0]==wq2_rptr[ADDR_WIDTH-2:0]));
	//------------------------------------------------------------------
	assign wfull_val = (wgraynext=={~wq2_rptr[ADDR_WIDTH:ADDR_WIDTH-1],wq2_rptr[ADDR_WIDTH-2:0]});
	
	always_ff @(posedge wclk or negedge wrst_n)
	begin
		if (!wrst_n) 
			wfull <= 1'b0;
		else 
			wfull <= wfull_val;
	end
endmodule
