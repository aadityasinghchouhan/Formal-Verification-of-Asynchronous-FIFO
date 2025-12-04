set_fml_appmode FPV 
set design async_fifo_dut 

read_file -top $design -format sverilog -sva -aep all -vcs {-f ../RTL/filelist}

# Creating clock and reset signals
create_clock clk -period 100 -initial 0 
create_reset rst_b -sense low

# Runing a reset simulation
sim_run -stable 
sim_save_reset

check_fv
report_fv