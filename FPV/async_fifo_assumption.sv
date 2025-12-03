module asynch_fifo_assumption(input [DATA_WIDTH-1:0] rdata,
                            input wfull,
                            input rempty,
                            input [DATA_WIDTH-1:0] wdata,
                            input winc, wclk, wrst_n,
                            input rinc, rclk, rrst_n);

    parameter DATA_WIDTH=8;
    parameter ADDR_WIDTH=4;


//winc, rinc, resets, wclk and rclk are never X or Z.
winc_not_x : assume property !$isunknown(winc);

rinc_not_x : assume property !$isunknown(rinc);

reset_not_x: assume property !$isunknown(reset);

rclk_not_x : assume property !$isunknown(rclk);

wclk_not_x :assume property !$isunknown(wclk);

// Write clock toggles continuously
wclk_toggle1 : assume property (@(posedge wclk) $fell(wclk));
wclk_toggle2 : assume property (@(negedge wclk) $rose(wclk));

// Read clock toggles continuously
rclk_toggle1 : assume property (@(posedge rclk) $fell(rclk));
rclk_toggle2 : assume property (@(negedge rclk) $rose(rclk));

// wrst_n starts low
assume property ( $initstate |-> wrst_n == 1'b0));

// rrst_n starts low
assume property ( $initstate |-> rrst_n == 1'b0));

// wrst_n never glitches after release 
assume property ( @(posedge wclk) $rose(wrst_n) |-> $stable(wrst_n) );

// rrst_n never glitches after release 
assume property ( @(posedge rclk) $rose(rrst_n) |-> $stable(rrst_n) );

//winc is stable within an wclk cycle
assume property ( @(posedge wclk) $stable(winc) ); 
// assume property ( $changed(winc) |-> $rose(wclk) );          // by using this, the signal can change on a specific edge

//rinc is stable within an rclk cycle
//assume property ( $changed(rinc) |-> $rose(rclk) );           // by using this, the signal can change on a specific edge 
assume property ( @(posedge rclk) $stable(rinc) );

//wdata is stable when winc happens 
assume property ( @(posedge wclk) winc |-> $stable(wdata) );


// No writing when fifo is full
assume property ( full |-> !winc );

// No reading when fifo is empty
assume property ( empty |-> !rinc );

endmodule 