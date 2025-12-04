// Inline SVA Reformatted with Named Properties (Option A Descriptive Names)

module async_fifo_assertion #(parameter DATA_WIDTH=8, ADDR_WIDTH=4) (
    input [DATA_WIDTH-1:0] rdata,
    input wfull,
    input rempty,
    input [DATA_WIDTH-1:0] wdata,
    input winc, wclk, wrst_n,
    input rinc, rclk, rrst_n,
    input [ADDR_WIDTH:0] wq1_rptr,
    input [ADDR_WIDTH:0] wq2_rptr,
    input [ADDR_WIDTH:0] rq1_wptr,
    input [ADDR_WIDTH:0] rq2_wptr,
    input [ADDR_WIDTH:0] wptr,
    input [ADDR_WIDTH:0] rptr,
    input [ADDR_WIDTH:0] rbin,
    input [ADDR_WIDTH:0] wbin
);

parameter DEPTH = fifomem.FIFO_DEPTH;
//----------------------------------------------------------
// sync_r2w : Read pointer → Write clock domain
//----------------------------------------------------------

// Reset behavior: When wrst_n LOW, wq1_rptr and wq2_rptr must be 0
property WQ_RPTR_RESET;
    @(posedge wclk) !wrst_n |-> (wq1_rptr == 0 && wq2_rptr == 0);
endproperty
WQ_RPTR_RESET_A: assert property(WQ_RPTR_RESET);

// wq1_rptr changes only on rising edge of wclk
//property WQ1_RPTR_EDGE_CHANGE;
    //@(posedge wclk) $rose(wclk) |-> !$stable(wq1_rptr);
//endproperty
//WQ1_RPTR_EDGE_CHANGE_A: assert property(WQ1_RPTR_EDGE_CHANGE);

// wq2_rptr changes only on rising edge of wclk
//property WQ2_RPTR_EDGE_CHANGE;
    //@(posedge wclk) $rose(wclk) |-> $changed(wq2_rptr);
//endproperty
//WQ2_RPTR_EDGE_CHANGE_A: assert property(WQ2_RPTR_EDGE_CHANGE);

// wq1_rptr captures rptr with 1-cycle latency
property WQ1_RPTR_LATENCY;
    @(posedge wclk) disable iff (!wrst_n)
    wq1_rptr == $past(rptr);
endproperty
WQ1_RPTR_LATENCY_A: assert property(WQ1_RPTR_LATENCY);

// wq2_rptr captures wq1_rptr with 1-cycle latency
property WQ2_RPTR_LATENCY;
    @(posedge wclk) disable iff (!wrst_n)
    wq2_rptr == $past(wq1_rptr);
endproperty
WQ2_RPTR_LATENCY_A: assert property(WQ2_RPTR_LATENCY);

// If rptr stable 2 cycles, wq2_rptr equals it after 2 cycles
property WQ2_RPTR_MATCH_STABLE_RPTR;
    @(posedge wclk) disable iff(!wrst_n)
        (rptr == $past(rptr) && rptr == $past(rptr,2)) |-> ##2 (wq2_rptr == $past(rptr,2));
endproperty
WQ2_RPTR_MATCH_STABLE_RPTR_A: assert property(WQ2_RPTR_MATCH_STABLE_RPTR);

//----------------------------------------------------------
// sync_w2r : Write pointer → Read clock domain
//----------------------------------------------------------

// Reset
property RQ_WPTR_RESET;
    @(posedge rclk) !rrst_n |-> (rq1_wptr == '0 && rq2_wptr == '0);
endproperty
RQ_WPTR_RESET_A: assert property(RQ_WPTR_RESET);

// rq1 change only on rclk
property RQ1_WPTR_EDGE_CHANGE;
    $changed(rq1_wptr) |-> $rose(rclk);
endproperty
RQ1_WPTR_EDGE_CHANGE_A: assert property(RQ1_WPTR_EDGE_CHANGE);

// rq2 change only on rclk
property RQ2_WPTR_EDGE_CHANGE;
    $changed(rq2_wptr) |-> $rose(rclk);
endproperty
RQ2_WPTR_EDGE_CHANGE_A: assert property(RQ2_WPTR_EDGE_CHANGE);

// rq1 captures wptr
property RQ1_WPTR_LATENCY;
    @(posedge rclk) disable iff (!rrst_n)
        rq1_wptr == $past(wptr);
endproperty
RQ1_WPTR_LATENCY_A: assert property(RQ1_WPTR_LATENCY);

// rq2 captures rq1
property RQ2_WPTR_LATENCY;
    @(posedge rclk) disable iff (!rrst_n)
        rq2_wptr == $past(rq1_wptr);
endproperty
RQ2_WPTR_LATENCY_A: assert property(RQ2_WPTR_LATENCY);

// stable wptr propagates
property RQ2_MATCH_STABLE_WPTR;
    @(posedge rclk) disable iff (!rrst_n)
        (wptr == $past(wptr) && wptr == $past(wptr,2))
        |-> ##2 (rq2_wptr == $past(wptr,2));
endproperty
RQ2_MATCH_STABLE_WPTR_A: assert property(RQ2_MATCH_STABLE_WPTR);

//--------------------------------------------------------------
// Write pointer + full flag
//--------------------------------------------------------------

// Reset clears pointers + full
property WBIN_WPTR_RESET;
    @(posedge wclk) !wrst_n |-> (wbin=='0 && wptr=='0 && wfull=='0);
endproperty
WBIN_WPTR_RESET_A: assert property(WBIN_WPTR_RESET);

// waddr reset
property WADDR_RESET;
    @(posedge wclk) !wrst_n |-> (waddr=='0);
endproperty
WADDR_RESET_A: assert property(WADDR_RESET);

// waddr = low bits of wbin
property WADDR_BIN_MAPPING;
    @(posedge wclk) disable iff (!wrst_n)
    waddr == wbin[ADDR_WIDTH-1:0];
endproperty
WADDR_BIN_MAPPING_A: assert property(WADDR_BIN_MAPPING);

// wptr = gray(wbin)
property WPTR_GRAY_MAPPING;
    @(posedge wclk) disable iff (!wrst_n)
        wptr == (wbin ^ (wbin>>1));
endproperty
WPTR_GRAY_MAPPING_A: assert property(WPTR_GRAY_MAPPING);

// Gray code single bit transition
property WPTR_GRAY_SINGLE_BIT_CHANGE;
    @(posedge wclk) disable iff (!wrst_n)
        (wbin == $past(wbin)+1)
        |-> $onehot(wptr ^ $past(wptr));
endproperty
WPTR_GRAY_SINGLE_BIT_CHANGE_A: assert property(WPTR_GRAY_SINGLE_BIT_CHANGE);

// No increment when full
property WBIN_HOLD_WHEN_FULL;
    @(posedge wclk) disable iff(!wrst_n)
        wfull |-> ##1 (wbin==$past(wbin) && wptr==$past(wptr));
endproperty
WBIN_HOLD_WHEN_FULL_A: assert property(WBIN_HOLD_WHEN_FULL);

// increment when winc && !wfull
property WBIN_INCREMENT_WHEN_ENABLED;
    @(posedge wclk) disable iff (!wrst_n)
        (winc && !wfull) |-> (wbin==$past(wptr_full.wbinnext) && wptr==$past(wptr_full.wgraynext));
endproperty
WBIN_INCREMENT_WHEN_ENABLED_A: assert property(WBIN_INCREMENT_WHEN_ENABLED);

// hold when !winc
property WBIN_HOLD_WHEN_NO_WINC;
    @(posedge wclk) disable iff (!wrst_n)
        !winc |-> (wbin==$past(wbin));
endproperty
WBIN_HOLD_WHEN_NO_WINC_A: assert property(WBIN_HOLD_WHEN_NO_WINC);

// full flag correctness
property WFULL_MATCHES_EXPR;
    @(posedge wclk) disable iff (!wrst_n)
        wfull == wfull_val;
endproperty
WFULL_MATCHES_EXPR_A: assert property(WFULL_MATCHES_EXPR);

// binary distance when full
property FULL_DISTANCE_IS_DEPTH;
    @(posedge wclk) disable iff (!wrst_n)
        wfull |-> (wbin - gray2bin(wq2_rptr) == DEPTH);
endproperty
FULL_DISTANCE_IS_DEPTH_A: assert property(FULL_DISTANCE_IS_DEPTH);

// full changes only on wclk
property WFULL_EDGE_CHANGE;
    $changed(wfull) |-> $rose(wclk);
endproperty
WFULL_EDGE_CHANGE_A: assert property(WFULL_EDGE_CHANGE);

//----------------------------------------------------------
// Read pointer + empty flag
//----------------------------------------------------------

// After reset rbin=0 rptr=0 rempty=1
property R_BIN_RPTR_EMPTY_RESET;
    @(posedge rclk)
        !rrst_n |-> (rbin=='0 && rptr=='0 && rempty==1'b1);
endproperty
R_BIN_RPTR_EMPTY_RESET_A: assert property(R_BIN_RPTR_EMPTY_RESET);

// raddr reset
property RADDR_RESET;
    @(posedge rclk)
        !rrst_n |-> (raddr=='0);
endproperty
RADDR_RESET_A: assert property(RADDR_RESET);

// raddr = low bits
property RADDR_BIN_MAPPING;
    @(posedge rclk) disable iff (!rrst_n)
        raddr == rbin[ADDR_WIDTH-1:0];
endproperty
RADDR_BIN_MAPPING_A: assert property(RADDR_BIN_MAPPING);

// rptr gray encoding
property RPTR_GRAY_MAPPING;
    @(posedge rclk) disable iff (!rrst_n)
        rptr == (rbin ^ (rbin>>1));
endproperty
RPTR_GRAY_MAPPING_A: assert property(RPTR_GRAY_MAPPING);

// gray single bit transition
property RPTR_GRAY_SINGLE_BIT_CHANGE;
    @(posedge rclk) disable iff (!rrst_n)
        (rbin == $past(rbin)+1) |-> $onehot(rptr ^ $past(rptr));
endproperty
RPTR_GRAY_SINGLE_BIT_CHANGE_A: assert property(RPTR_GRAY_SINGLE_BIT_CHANGE);

// no increment when empty
property R_BIN_HOLD_WHEN_EMPTY;
    @(posedge rclk) disable iff (!rrst_n)
        rempty |-> ##1 (rbin==$past(rbin) && rptr==$past(rptr));
endproperty
R_BIN_HOLD_WHEN_EMPTY_A: assert property(R_BIN_HOLD_WHEN_EMPTY);

// increment when enabled and not empty
property R_BIN_INCREMENT_WHEN_ENABLED;
    @(posedge rclk) disable iff (!rrst_n)
        (rinc && !rempty) |-> (rptr_empty.rbin==$past(rptr_empty.rbinnext) && rptr==$past(rptr_empty.rgraynext));
endproperty
R_BIN_INCREMENT_WHEN_ENABLED_A: assert property(R_BIN_INCREMENT_WHEN_ENABLED);

// hold rbin when !rinc
property R_BIN_HOLD_WHEN_NO_RINC;
    @(posedge rclk) disable iff (!rrst_n)
        !rinc |-> (rbin==$past(rbin));
endproperty
R_BIN_HOLD_WHEN_NO_RINC_A: assert property(R_BIN_HOLD_WHEN_NO_RINC);

// empty correctness
property REMPTY_MATCHES_EXPR;
    @(posedge rclk) disable iff (!rrst_n)
        rempty == rempty_val;
endproperty
REMPTY_MATCHES_EXPR_A: assert property(REMPTY_MATCHES_EXPR);

// rgraynext match
property REMPTY_VAL_EXPR;
    @(posedge rclk) disable iff (!rrst_n)
        rempty_val == (rgraynext == rq2_wptr);
endproperty
REMPTY_VAL_EXPR_A: assert property(REMPTY_VAL_EXPR);

// rempty changes only on rclk
property REMPTY_EDGE_CHANGE;
    $changed(rempty) |-> $rose(rclk);
endproperty
REMPTY_EDGE_CHANGE_A: assert property(EMPTY_EDGE_CHANGE);

//------------------------------------------------------
// FIFO Memory
//------------------------------------------------------
/*
genvar i;
generate
  for (i = 0; i < DEPTH; i++) begin : FIFO_CHECK

    // Clear on reset
    property FIFO_CLEAR_RESET;
      @(posedge wclk) !wrst_n |-> fifomem.fifo[i] == '0;
    endproperty
    FIFO_CLEAR_RESET_A: assert property (FIFO_CLEAR_RESET);

    // Write behavior (only fifo[waddr] updates)
    if (i == fifomem.waddr) begin : WRITE_LOC
      property FIFO_WRITE_LOCATION;
        @(posedge wclk) disable iff (!wrst_n)
          (wclken && !wfull) |-> fifomem.fifo[i] == $past(fifomem.wdata);
      endproperty
      FIFO_WRITE_LOCATION_A: assert property(FIFO_WRITE_LOCATION);
    end
    else begin : NO_WRITE_LOC
      property FIFO_NO_WRITE_OTHER_LOC;
        @(posedge wclk) disable iff (!wrst_n)
          (wclken && !wfull) |-> fifomem.fifo[i] == $past(fifomem.fifo[i]);
      endproperty
      FIFO_NO_WRITE_OTHER_LOC_A: assert property(FIFO_NO_WRITE_OTHER_LOC);
    end

    // No write when disabled/full
    property FIFO_HOLD_WHEN_NO_WRITE;
      @(posedge wclk) disable iff (!wrst_n)
        (!wclken || wfull) |-> fifomem.fifo[i] == $past(fifomem.fifo[i]);
    endproperty
    FIFO_HOLD_WHEN_NO_WRITE_A: assert property(FIFO_HOLD_WHEN_NO_WRITE);

    // Read side does not corrupt memory
    property FIFO_NO_READ_CORRUPTION;
      @(posedge rclk) disable iff (!rrst_n)
        1'b1 |-> fifomem.fifo[i] == $past(fifomem.fifo[i]);
    endproperty
    FIFO_NO_READ_CORRUPTION_A: assert property(FIFO_NO_READ_CORRUPTION);

  end
endgenerate

always_comb begin
foreach (fifomem.fifo[i]) begin

    // Clear on reset
    property FIFO_CLEAR_RESET_``i;
        @(posedge wclk) !wrst_n |-> fifomem.fifo[i]=='0;
    endproperty
    FIFO_CLEAR_RESET_``i``_A: assert property(FIFO_CLEAR_RESET_``i);

    // Write behavior match (only fifo[waddr] updates)
    if (i == waddr) begin
        property FIFO_WRITE_LOCATION_``i;
            @(posedge wclk) disable iff (!wrst_n)
                (wclken && !wfull) |-> fifomem.fifo[i] == $past(wdata);
        endproperty
        FIFO_WRITE_LOCATION_``i``_A: assert property(FIFO_WRITE_LOCATION_``i);
    end
    else begin
        property FIFO_NO_WRITE_OTHER_LOC_``i;
            @(posedge wclk) disable iff (!wrst_n)
                (wclken && !wfull) |-> fifomem.fifo[i] == $past(fifomem.fifo[i]);
        endproperty
        FIFO_NO_WRITE_OTHER_LOC_``i``_A: assert property(FIFO_NO_WRITE_OTHER_LOC_``i);
    end

    // No write when disabled/full
    property FIFO_HOLD_WHEN_NO_WRITE_``i;
        @(posedge wclk) disable iff (!wrst_n)
            (!wclken || wfull) |-> fifomem.fifo[i] == $past(fifomem.fifo[i]);
    endproperty
    FIFO_HOLD_WHEN_NO_WRITE_``i``_A: assert property(FIFO_HOLD_WHEN_NO_WRITE_``i);

    // read side does not corrupt memory
    property FIFO_NO_READ_CORRUPTION_``i;
        @(posedge rclk) disable iff (!rrst_n)
            1'b1 |-> fifomem.fifo[i] == $past(fifomem.fifo[i]);
    endproperty
    FIFO_NO_READ_CORRUPTION_``i``_A: assert property(FIFO_NO_READ_CORRUPTION_``i);

end
end
*/
// valid read returns fifo[raddr]
property READ_RETURNS_FIFO_DATA;
    @(posedge rclk) disable iff (!rrst_n)
        (rclken && !rempty) |-> rdata == $past(fifomem.fifo[fifomem.raddr]);
endproperty
READ_RETURNS_FIFO_DATA_A: assert property(READ_RETURNS_FIFO_DATA);

// no-read returns 0
property READ_RETURNS_ZERO_WHEN_IDLE;
    @(posedge rclk) disable iff (!rrst_n)
        (!rclken || rempty) |-> rdata == '0;
endproperty
READ_RETURNS_ZERO_WHEN_IDLE_A: assert property(READ_RETURNS_ZERO_WHEN_IDLE);

//--------------------------------------------------------------
// Global FIFO properties
//--------------------------------------------------------------

// full & empty cannot both be high
property FULL_AND_EMPTY_NEVER_SIMULTANEOUS;
    @(posedge wclk or posedge rclk)
        (wrst_n && rrst_n) |-> !(wfull && rempty);
endproperty
FULL_AND_EMPTY_NEVER_SIMULTANEOUS_A: assert property(FULL_AND_EMPTY_NEVER_SIMULTANEOUS);

// empty after global reset
sequence global_reset_release;
    !wrst_n && !rrst_n ##1 $rose(wrst_n && rrst_n);
endsequence

property EMPTY_AFTER_GLOBAL_RESET;
    @(posedge wclk or posedge rclk)
        global_reset_release |-> ##[0:$] (rempty && !wfull);
endproperty
EMPTY_AFTER_GLOBAL_RESET_A: assert property(EMPTY_AFTER_GLOBAL_RESET);
/*
// occupancy constraints
property OCCUPANCY_WITHIN_BOUNDS;
    @(posedge wclk) disable iff (!wrst_n || !rrst_n)
        occ_w <= FIFO_DEPTH;
endproperty
OCCUPANCY_WITHIN_BOUNDS_A: assert property(OCCUPANCY_WITHIN_BOUNDS);

property OCCUPANCY_NOT_NEGATIVE;
    @(posedge wclk) disable iff (!wrst_n || !rrst_n)
        occ_w[PTR_WIDTH] == 1'b0;
endproperty
OCCUPANCY_NOT_NEGATIVE_A: assert property(OCCUPANCY_NOT_NEGATIVE);

// no underflow (model)
property OCC_MODEL_NO_UNDERFLOW;
    @(posedge wclk or posedge rclk)
        occ_model >= 0;
endproperty
OCC_MODEL_NO_UNDERFLOW_A: assert property(OCC_MODEL_NO_UNDERFLOW);

// no overflow
property OCC_MODEL_NO_OVERFLOW;
    @(posedge wclk or posedge rclk)
        occ_model <= FIFO_DEPTH;
endproperty
OCC_MODEL_NO_OVERFLOW_A: assert property(OCC_MODEL_NO_OVERFLOW);
*/

endmodule

bind async_fifo_dut async_fifo_assertion #(8, 4) assertion_h (.*);
bind sync_r2w async_fifo_assertion #(8, 4) assertion_h (.*);
bind rptr_empty async_fifo_assertion #(8, 4) assertion_h (.*);
bind wptr_full async_fifo_assertion #(8, 4) assertion_h (.*);