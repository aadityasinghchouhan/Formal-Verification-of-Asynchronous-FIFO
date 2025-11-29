// Async fifo DUT
module asynch_fifo_dut #(parameter DATA_WIDTH=8, ADDR_WIDTH=4) (output [DATA_WIDTH-1:0] rdata,
                                                                output wfull,
                                                                output rempty,
                                                                input [DATA_WIDTH-1:0] wdata,
                                                                input winc, wclk, wrst_n,
                                                                input rinc, rclk, rrst_n);

    logic [ADDR_WIDTH-1:0] waddr, raddr;
    logic [ADDR_WIDTH:0] wptr, rptr, wq2_rptr, rq2_wptr;

    //Sub-module instantiation
    sync_r2w #(ADDR_WIDTH) SYNC_R2W (.*);
    sync_w2r #(ADDR_WIDTH) SYNC_W2R (.*);

    fifomem #(DATA_WIDTH, ADDR_WIDTH) FIFOMEM (.rdata(rdata),
                                           .wdata(wdata),
                                           .waddr(waddr),
                                           .raddr(raddr),
                                           .wclken(winc),
                                           .rclken(rinc),
                                           .wfull(wfull),
                                           .rempty(rempty),
                                           .wrst_n(wrst_n),
                                           .rrst_n(rrst_n),
                                           .rclk(rclk),
                                           .wclk(wclk));

    rptr_empty #(ADDR_WIDTH) RPTR_EMPTY (.*);

    wptr_full #(ADDR_WIDTH) WPTR_FULL (.*);

endmodule
