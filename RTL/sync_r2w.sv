module sync_r2w #(parameter ADDR_WIDTH=4) (output logic [ADDR_WIDTH:0] wq2_rptr,
                                           input [ADDR_WIDTH:0] rptr,
                                           input wclk, wrst_n);

    logic [ADDR_WIDTH:0] wq1_rptr;
    
    //Procedural blocks
    always_ff@(posedge wclk or negedge wrst_n)
    begin
        if(!wrst_n)
        begin
            {wq2_rptr, wq1_rptr} <= 0;
        end
        else
        begin
            {wq2_rptr, wq1_rptr} <= {wq1_rptr, rptr};
        end
    end

endmodule