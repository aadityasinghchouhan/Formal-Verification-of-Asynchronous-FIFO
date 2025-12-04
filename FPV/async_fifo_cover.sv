module async_fifo_cover #(parameter DATA_WIDTH=8, ADDR_WIDTH=4)
(
    input  [DATA_WIDTH-1:0] rdata,
    input                   wfull,
    input                   rempty,
    input  [DATA_WIDTH-1:0] wdata,
    input                   winc, wclk, wrst_n,
    input                   rinc, rclk, rrst_n
);

    // --------------------------------------------
    // FIFO becomes non-empty (rempty: high -> low)
    // --------------------------------------------
    property FIFO_NON_EMPTY;
        @(posedge rclk) disable iff (!rrst_n || !wrst_n)
            rempty ##[1:$] !rempty;
    endproperty
    FIFO_NON_EMPTY_C: cover property (FIFO_NON_EMPTY);

    // --------------------------------------------
    // FIFO becomes full (wfull goes high once)
    // --------------------------------------------
    property FIFO_FULL;
        @(posedge wclk) disable iff (!wrst_n || !rrst_n)
            wfull;
    endproperty
    FIFO_FULL_C: cover property (FIFO_FULL);

    // --------------------------------------------
    // FIFO full -> not full
    // --------------------------------------------
    property FIFO_FULL_TO_NOTFULL;
        @(posedge wclk) disable iff (!wrst_n || !rrst_n)
            wfull ##[1:$] !wfull;
    endproperty
    FIFO_FULL_TO_NOTFULL_C: cover property (FIFO_FULL_TO_NOTFULL);

    // --------------------------------------------
    // FIFO empty -> non-empty -> empty
    // --------------------------------------------
    property FIFO_EMPTY_NONEMPTY_EMPTY;
        @(posedge rclk) disable iff (!rrst_n || !wrst_n)
            rempty ##[1:$] !rempty ##[1:$] rempty;
    endproperty


    // --------------------------------------------
    // Write pointer wrap-around
    // --------------------------------------------
    property WPTR_WRAP;
        @(posedge wclk) disable iff (!wrst_n)
            ($past(wptr_full.wbin) == FIFO_DEPTH-1) && (wptr_full.wbin == '0);
    endproperty
    WPTR_WRAP_C: cover property (WPTR_WRAP);

    // --------------------------------------------
    // Read pointer wrap-around
    // --------------------------------------------
    property RPTR_WRAP;
        @(posedge rclk) disable iff (!rrst_n)
            ($past(rptr_empty.rbin) == FIFO_DEPTH-1) && (rptr_empty.rbin == '0);
    endproperty
    RPTR_WRAP_C: cover property (RPTR_WRAP);

    // --------------------------------------------
    // Simultaneous read & write (not empty/full)
    // --------------------------------------------
    property SIMULTANEOUS_RW;
        @(posedge wclk or posedge rclk) disable iff (!wrst_n || !rrst_n)
            (winc && !wfull && rinc && !rempty);
    endproperty
    SIMULTANEOUS_RW_C: cover property (SIMULTANEOUS_RW);

    // --------------------------------------------
    // rptr change shows up in wq2_rptr
    // --------------------------------------------
/*
    property RPTR_SYNCED_TO_WCLK;
        @(posedge wclk) disable iff (!wrst_n || !rrst_n)
            $changed(rptr) ##[1:$] $changed(wq2_rptr);
    endproperty
    RPTR_SYNCED_TO_WCLK_C: cover property (RPTR_SYNCED_TO_WCLK);

    // --------------------------------------------
    // wptr change shows up in rq2_wptr
    // --------------------------------------------
    property WPTR_SYNCED_TO_RCLK;
        @(posedge rclk) disable iff (!wrst_n || !rrst_n)
            $changed(wptr) ##[1:$] $changed(rq2_wptr);
    endproperty
    WPTR_SYNCED_TO_RCLK_C: cover property (WPTR_SYNCED_TO_RCLK);
*/
endmodule