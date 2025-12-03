set_fml_appmode FXP

set design async_fifo_dut

read_file -top $design -format sverilog -sva -vcs {-f ../RTL/filelist}

create_clock clk -period 100
create_reset resetn -sense low

sim_run -stable
sim_save_reset

fxp_generate