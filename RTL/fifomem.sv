// fifomem
module fifomem #(parameter DATA_WIDTH=8, ADDR_WIDTH=4) (output logic [DATA_WIDTH-1:0] rdata,
                                                        input [DATA_WIDTH-1:0] wdata,
                                                        input [ADDR_WIDTH-1:0] waddr, raddr,
                                                        input wclken, rclken, wfull, rempty, wrst_n, rrst_n, wclk, rclk);

    //Memory model depth
    localparam FIFO_DEPTH = 1 << ADDR_WIDTH;

    //Memory declaration
    logic [DATA_WIDTH-1:0] fifo [0:FIFO_DEPTH-1];

    //rdata output logic
    // assign rdata = fifo[raddr];

    always_ff@(negedge wrst_n)
    begin
        foreach(fifo[i])
            fifo[i] <= 0;
    end

    always_ff@(posedge wclk)
    begin
        if(wclken && !wfull && wrst_n)
        begin
            fifo[waddr] <= wdata;
        end
    end

    always_ff@(posedge rclk)
    begin
        if(rclken && !rempty)
        begin
            rdata <= fifo[raddr];
        end
        else
            rdata <= 0;
    end

endmodule
