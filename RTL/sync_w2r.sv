module sync_w2r #(parameter ADDR_WIDTH = 4)(
	
	output logic [ADDR_WIDTH:0] rq2_wptr,
	input logic [ADDR_WIDTH:0] wptr,
	input logic rclk, rrst_n);
	
	logic [ADDR_WIDTH:0] rq1_wptr;
	
	always_ff @(posedge rclk or negedge rrst_n)
	begin
	if (!rrst_n) 
		{rq2_wptr,rq1_wptr} <= 0;
	else 
		{rq2_wptr,rq1_wptr} <= {rq1_wptr,wptr};
	end
		
endmodule
