module asynch_fifo_cover(input [DATA_WIDTH-1:0] rdata,
                            input wfull,
                            input rempty,
                            input [DATA_WIDTH-1:0] wdata,
                            input winc, wclk, wrst_n,
                            input rinc, rclk, rrst_n);

    parameter DATA_WIDTH=8;
    parameter ADDR_WIDTH=4;

//FIFO becomes non-empty, rempty starts HIGH, later becomes LOW
// FIFO goes from empty to non-empty
cover property (@(posedge rclk) disable iff (!rrst_n || !wrst_n)
                rempty ##[1:$] !rempty);

//FIFO becomes full, At some point, wfull goes HIGH
// FIFO becomes full at least once
cover property (@(posedge wclk) disable iff (!wrst_n || !rrst_n)
                wfull);

// Full → not full, wfull HIGH, later goes LOW
// FIFO transitions from full to not-full
cover property (@(posedge wclk) disable iff (!wrst_n || !rrst_n)
                wfull ##[1:$] !wfull);

//Empty → not empty → empty
//rempty HIGH → LOW → HIGH again
// FIFO goes empty -> non-empty -> empty again
cover property (@(posedge rclk) disable iff (!rrst_n || !wrst_n)
                rempty ##[1:$] !rempty ##[1:$] rempty);

// Write pointer wraps from last address back to 0
cover property (@(posedge wclk) disable iff (!wrst_n)
                ($past(wbin) == FIFO_DEPTH-1) && (wbin == '0));

// Read pointer wraps from last address back to 0
cover property (@(posedge rclk) disable iff (!rrst_n)
                ($past(rbin) == FIFO_DEPTH-1) && (rbin == '0));

// A cycle where both read and write happen (not empty / not full)
cover property (@(posedge wclk or posedge rclk) disable iff (!wrst_n || !rrst_n)
                (winc && !wfull && rinc && !rempty));


// A change in rptr eventually shows up in synchronized wq2_rptr
cover property (@(posedge wclk) disable iff (!wrst_n || !rrst_n)
                $changed(rptr) ##[1:$] $changed(wq2_rptr));

// A change in wptr eventually shows up in synchronized rq2_wptr
cover property (@(posedge rclk) disable iff (!rrst_n || !wrst_n)
                $changed(wptr) ##[1:$] $changed(rq2_wptr));











endmodule 