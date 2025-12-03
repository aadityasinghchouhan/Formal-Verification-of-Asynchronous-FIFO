// Inline SVA

//assertion property @(posedge wclk) (data_in && write_enable |=> fifo_mem[wrptr] == wdata);


module asynch_fifo_assertion(input [DATA_WIDTH-1:0] rdata,
                            input wfull,
                            input rempty,
                            input [DATA_WIDTH-1:0] wdata,
                            input winc, wclk, wrst_n,
                            input rinc, rclk, rrst_n);

    parameter DATA_WIDTH=8;
    parameter ADDR_WIDTH=4;

////---------------------------------------------------------- sync_r2w   read pointer -> write clock domain //----------------------------------------------------------

//Reset behavior When wrst_n is LOW, both wq1_rptr and wq2_rptr must be 0 on every wclk rising edge.
assert property ( @(posedge wclk)  !wrst_n |-> ( wq1_rptr == 0 && wq2_rptr== 0 ) );

//wq1_rptr change only on rising edges of wclk              // if the pointer changes at any time, that time must be a posedge wclk
assert property ( @(posedge wclk) $changed(wq1_rptr) |-> $rose(wclk) );

// wq2_rptr change only on rising edges of wclk
assert property ( @(posedge wclk) $changed(wq2_rptr) |-> $rose(wclk) );

// wq1_rptr captures rptr with 1-cycle latency in write clock domain 
assert ptoperty ( @(posedge wclk) disable iff (!wrst_n)
wq1_rptr == $past(rptr) );

//wq2_rptr captures wq1_rptr with 1-cycle latency 
assert property ( @(posedge wclk) diasble iff (!wrst_n) 
    wq2_rptr == $past(wq1_rptr) );

// If rptr is same for the last 2 cycles, then in 2 cycles wq2_rptr equals that stable values 
assert property ( @(posedge wclk) disable iff(!wrst_n) 
    ( rptr == $past(rptr) && rptr == $past(rptr,2) )
    |-> ##2 (wq2_rptr == $past(rptr,2) ) );

//----------------------------------------------------------Assertions for sync_w2r (write pointer -> read clock domain)----------------------------------------------

// When rrst_n is LOW, both rq1_wptr and rq2_wptr must be 0 on every rclk rising edge.
assert property (@(posedge rclk) !rrst_n |-> (rq1_wptr == '0 && rq2_wptr == '0));

// rq1_wptr only changes on rclk rising edge
assert property ( $changed(rq1_wptr) |-> $rose(rclk) );

// rq2_wptr only changes on rclk rising edge
assert property ( $changed(rq2_wptr) |-> $rose(rclk) );

// rq1_wptr captures wptr with 1-cycle latency in read clock domain
assert property (@(posedge rclk) disable iff (!rrst_n) rq1_wptr == $past(wptr));

// rq2_wptr captures rq1_wptr with 1-cycle latency (2-cycle from wptr)
assert property (@(posedge rclk) disable iff (!rrst_n) rq2_wptr == $past(rq1_wptr));

// If wptr is same for the last 2 cycles, then in 2 cycles rq2_wptr equals that stable value
assert property (@(posedge rclk) disable iff (!rrst_n)
        (wptr == $past(wptr) && wptr == $past(wptr,2))
        |-> ##2 (rq2_wptr == $past(wptr,2)));


//-------------------------------------------------------------- Write pointer and full flag -----------------------------------------------------------------------

// When wrst_n is lowm wbin, wptr wfull must be 0
assert property ( @(posedge wclk) !wrst_n |-> (wbin == '0 && wptr == '0 && wfull == '0) );

//when wrst_n is low, waddr must be 0
assert property ( @(posedge wclk) !wrst_n |-> (waddr =='0) );

// after reset, waddr must equal the lower ADDR_WIDTH bits of wbin          BINARY -> ADDRESS MAPPING 
assert property ( @(posedge wclk) disable iff (!wrst_n)
                    waddr == wbin[ADDR_WIDTH-1:0] );

// After reset, wptr must be the gray coded form of wbin 
assert property ( @(posedge wclk) diasable iff (!wrst_n)
                    wptr == (wbin ^ (wbin >> 1) ) );                    // gary(x) = x ^ (x >> 1)


//Gray single bit transistions - when wbin increments bu exactly 1, wptr must change by exactly 1 bit 
assert property ( @(posedge wclk) disable iff (!wrst_n) 
                (wbin == $past(wbin) + 1)  |-> $onehot (wptr ^ $past(wptr)));


// (No increment when full) If wfull is high and wrst_n is high, then on next wclk edge, wbin and wptr must remain unchanged regardless of winc 
assert property ( @(posedg wclk) diasble iff(!wrst_n) 
                wfull |-> ##1 (wbin == $past(wbin) && wptr == $past(wptr) ) );  

// when write enable is asserted and not full, wbin incremnets by 1
// {wbin, wptr} <= {wbinnext, wgraynext};
assert property (@(posedge wclk) disable iff (!wrst_n)
                 (winc && !wfull)
                 |-> (wbin == $past(wbinnext) && wptr == $past(wgraynext)));

// If winc is LOW or wrst_n is LOW, then wbin must not increment.        
assert property (@(posedge wclk) disable iff (!wrst_n)
                 !winc |-> (wbin == $past(wbin)));
    
// Full flag correctness, wfull equals full expression (wfull_val)
// Registered full flag matches its combinational expression
assert property (@(posedge wclk) disable iff (!wrst_n)
                 wfull == wfull_val);
/*
// Example: wfull_val definition (pointer comparison with inverted MSBs)
// wfull_val = (wgraynext == {~wq2_rptr[PTR_WIDTH-1:PTR_WIDTH-2],
//                            wq2_rptr[PTR_WIDTH-3:0]});
assert property (@(posedge wclk) disable iff (!wrst_n)
                 wfull_val == (wgraynext ==
                     {~wq2_rptr[PTR_WIDTH-1:PTR_WIDTH-2],
                       wq2_rptr[PTR_WIDTH-3:0]}));
*/ 

// When wfull is HIGH, wbin − rbin_synced == DEPTH,  When full, binary distance between wbin and synchronized read pointer is DEPTH
assert property (@(posedge wclk) disable iff (!wrst_n)
                 wfull |-> (wbin - gray2bin(wq2_rptr) == DEPTH[PTR_WIDTH-1:0]));

// Full flag can only change in sync with wclk edges 
assert property ( $changed(wfull) |-> $rose(wclk) );

//---------------------------------------------------------- rptr_empty - read pointer and empty flag (read domain) ----------------------------------------------------

// When rrst_n is LOW, rbin and rptr must be 0, and rempty must be 1.
assert property (@(posedge rclk)
                 !rrst_n |-> (rbin == '0 && rptr == '0 && rempty == 1'b1));

//When rrst_n is LOW, raddr must be 0.
assert property (@(posedge rclk)
                 !rrst_n |-> (raddr == '0));

//Binary → address mapping
//After reset, raddr = lower ADDR_WIDTH bits of rbin.                
assert property (@(posedge rclk) disable iff (!rrst_n)
                 raddr == rbin[ADDR_WIDTH-1:0]);

//Binary → Gray mapping
//After reset, rptr is Gray encoding of rbin.
assert property (@(posedge rclk) disable iff (!rrst_n)
                 rptr == (rbin ^ (rbin >> 1)));

// Gray single-bit transitions
//Whenever rbin increments by 1, rptr changes by exactly 1 bit.
assert property (@(posedge rclk) disable iff (!rrst_n)
                 (rbin == $past(rbin) + 1)
                 |-> $onehot(rptr ^ $past(rptr)));

//No increment when empty
//If rempty is HIGH and rrst_n is HIGH, next cycle rbin and rptr unchanged.
assert property (@(posedge rclk) disable iff (!rrst_n)
                 rempty |-> ##1 (rbin == $past(rbin) && rptr == $past(rptr)));

//Increment when enabled and not empty
//If rinc=1, rempty=0, rrst_n=1 → next cycle rbin++, rptr = next Gray
// {rbin, rptr} <= {rbinnext, rgraynext};
assert property (@(posedge rclk) disable iff (!rrst_n)
                 (rinc && !rempty)
                 |-> (rbin == $past(rbinnext) && rptr == $past(rgraynext)));

//If rinc is LOW, rbin must not incremen, When read enable is LOW, rbin must hold its value
assert property (@(posedge rclk) disable iff (!rrst_n)
                 !rinc |-> (rbin == $past(rbin)));

// After reset, raddr = lower ADDR_WIDTH bits of rbin Address is derived from low bits of read binary pointer      Binary -> address mapping 
assert property (@(posedge rclk) disable iff (!rrst_n)
                 raddr == rbin[ADDR_WIDTH-1:0]);

// After reset, rptr is Gray encoding of rbin.              Binary → Gray mapping 
// Gray pointer is Gray-encoding of read binary pointer
assert property (@(posedge rclk) disable iff (!rrst_n)
                 rptr == (rbin ^ (rbin >> 1)));

// Gray single-bit transitions, Whenever rbin increments by 1, rptr changes by exactly 1 bit.
// When rbin increments by 1, rptr must change by exactly one bit
assert property (@(posedge rclk) disable iff (!rrst_n)
                 (rbin == $past(rbin) + 1)
                 |-> $onehot(rptr ^ $past(rptr)));

//No increment when empty, If rempty is HIGH and rrst_n is HIGH, next cycle rbin and rptr unchanged.
// If FIFO is empty, read pointer must not advance
assert property (@(posedge rclk) disable iff (!rrst_n)
                 rempty |-> ##1 (rbin == $past(rbin) && rptr == $past(rptr)));


//Increment when enabled and not empty, If rinc=1, rempty=0, rrst_n=1 → next cycle rbin++, rptr = next Gray
// {rbin, rptr} <= {rbinnext, rgraynext};
assert property (@(posedge rclk) disable iff (!rrst_n)
                 (rinc && !rempty)
                 |-> (rbin == $past(rbinnext) && rptr == $past(rgraynext)));


//No unintended increment If rinc is LOW, rbin must not increment.
// When read enable is LOW, rbin must hold its value
assert property (@(posedge rclk) disable iff (!rrst_n)
                 !rinc |-> (rbin == $past(rbin)));

//Empty expression matches next pointer condition, After reset, rempty must equal rempty_val, and rempty_val is (rgraynext == rq2_wptr).
assert property (@(posedge rclk) disable iff (!rrst_n)
                 rempty == rempty_val);

// rempty_val itself matches next-gray vs synced write pointer
assert property (@(posedge rclk) disable iff (!rrst_n)
                 rempty_val == (rgraynext == rq2_wptr));

// Empty flag stability, rempty may change only on rclk rising edges.
// rempty must not glitch; it can only change on rclk edges
assert property ( $changed(rempty) |-> $rose(rclk) );


// ------------------------------------------------------FIFO MEMORY-----------------------------------------------------------

// All FIFO locations are cleared when write reset is active
foreach (fifo[i]) begin
  assert property (@(posedge wclk)
                   !wrst_n |-> fifo[i] == '0);
end

//Write happens only when enabled and not full, On posedge wclk, if wclken && !wfull && wrst_n,
// then fifo[waddr] is updated to wdata, all other fifo[i] remain unchanged

// When a valid write occurs, only fifo[waddr] is updated to wdata
foreach (fifo[i]) begin
  // Location being written: takes new data
  if (i == waddr) begin
    assert property (@(posedge wclk) disable iff (!wrst_n)
                     (wclken && !wfull)
                     |-> fifo[i] == $past(wdata));
  end
  // All other locations: must hold their previous values
  else begin
    assert property (@(posedge wclk) disable iff (!wrst_n)
                     (wclken && !wfull)
                     |-> fifo[i] == $past(fifo[i]));
  end
end

// No write when full or disabled, On posedge wclk, if wclken is LOW, or wfull is HIGH, or wrst_n is LOW, then no memory location must change.
// If write is disabled or FIFO is full, memory array must not change
foreach (fifo[i]) begin
  assert property (@(posedge wclk) disable iff (!wrst_n)
                   (!wclken || wfull)
                   |-> fifo[i] == $past(fifo[i]));
end

//Read returns stored data when enabled and not empty
//On posedge rclk, if rclken && !rempty && resets deasserted,
//then rdata must equal the value stored in fifo[raddr] right before that edge.

// When a valid read occurs, rdata must return the stored value
assert property (@(posedge rclk) disable iff (!rrst_n)
                 (rclken && !rempty)
                 |-> rdata == $past(fifo[raddr]));


//Read outputs 0 when not reading
//On posedge rclk, if rclken is LOW or rempty is HIGH, then rdata must be 0.

// When read is not happening (disabled or empty), rdata is driven to 0
assert property (@(posedge rclk) disable iff (!rrst_n)
                 (!rclken || rempty)
                 |-> rdata == '0);

// No unintended memory corruption from read side
// Operations in the read clock domain must never modify any element of fifo.
// Read clock domain must not modify FIFO contents
foreach (fifo[i]) begin
  assert property (@(posedge rclk) disable iff (!rrst_n)
                   1'b1 |-> fifo[i] == $past(fifo[i]));
end


// -------------------------------------------------------------------------async_fifo_dut -----------------------------------------------------------------------

// Once both wrst_n and rrst_n are deasserted, wfull and rempty must never be HIGH at the same time.
// After both resets are released, FIFO cannot be both full and empty
assert property (@(posedge wclk or posedge rclk)
                 (wrst_n && rrst_n) |-> !(wfull && rempty));

//Empty after global reset
//Shortly after both resets go low then high, rempty must be HIGH and wfull LOW.
sequence global_reset_release;
  !wrst_n && !rrst_n ##1 $rose(wrst_n && rrst_n);
endsequence

// Eventually after global reset, FIFO is empty and not full
property empty_after_reset;
  @(posedge wclk or posedge rclk)
    global_reset_release |-> ##[0:$] (rempty && !wfull);
endproperty

assert property (empty_after_reset);



//Cross-domain consistency via occupancy (optional, strong)
//a helper to convert Gray pointers back to binary 
function automatic [PTR_WIDTH-1:0] gray2bin (input [PTR_WIDTH-1:0] g);
  integer i;
  begin
    gray2bin[PTR_WIDTH-1] = g[PTR_WIDTH-1];
    for (i = PTR_WIDTH-2; i >= 0; i = i-1)
      gray2bin[i] = gray2bin[i+1] ^ g[i];
  end
endfunction
// Define a write-domain view of occupancy (binary difference between wbin and synced read pointer):
localparam int FIFO_DEPTH = (1 << ADDR_WIDTH);

logic [PTR_WIDTH:0] wbin_ext, rbinw_ext;
logic [PTR_WIDTH:0] occ_w;

always_comb begin
  wbin_ext  = {1'b0, wbin};
  rbinw_ext = {1'b0, gray2bin(wq2_rptr)};   // read ptr as seen in write domain
  occ_w     = wbin_ext - rbinw_ext;        // modulo 2^PTR_WIDTH arithmetic
end

//Pointer difference matches occupancy (never > depth or < 0)
//Effective occupancy equals wbin − synced-rptr, and is within [0, DEPTH].
// No overflow: occupancy never exceeds FIFO_DEPTH
assert property (@(posedge wclk) disable iff (!wrst_n || !rrst_n)
                 occ_w <= FIFO_DEPTH);

// No underflow: occupancy never negative (unsigned, so check MSB)
assert property (@(posedge wclk) disable iff (!wrst_n || !rrst_n)
                 occ_w[PTR_WIDTH] == 1'b0);  // sign bit must stay 0

//No “reading more than written” (matching counts)
//For any interval, number of successful reads cannot exceed number of successful writes.

int signed occ_model;

always_ff @(posedge wclk or posedge rclk) begin
  if (!wrst_n || !rrst_n) begin
    occ_model <= 0;
  end else begin
    if ($rose(wclk) && wr_fire)
      occ_model <= occ_model + 1;
    if ($rose(rclk) && rd_fire)
      occ_model <= occ_model - 1;
  end
end

// No underflow: can't read more than written
assert property (@(posedge wclk or posedge rclk)
                 occ_model >= 0);

// Optional: no overflow beyond depth (if you want it tied to DEPTH)
assert property (@(posedge wclk or posedge rclk)
                 occ_model <= FIFO_DEPTH);




endmodule 