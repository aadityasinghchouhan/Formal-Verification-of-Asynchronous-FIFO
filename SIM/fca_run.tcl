set_fml_appmode COV

set design async_fifo_dut
read_file -top $design -format sverilog -sva -vcs {-f ../RTL/filelist} -cov all

# Creating clock and reset signals
create_clock clk -period 100 -initial 0 
create_reset rst_b -sense low

# Runing a reset simulation
sim_run -stable 
sim_save_reset

check_fv_setup

#check_fv
#report_fv
