// Uses helper module Memory -- similar to top module of a testbench
`include "memory.sv"

task setup (
    input gpu dut,
    input Memory program_mem,
    input logic [15:0] pmem[],

    input Memory data_mem,
    input logic [15:0] dmem[],

    input int threads
); 
begin
// Generate clock with a period of 25 us
// Reset DUT - wait one posedge of clock
dut.reset <= 1'b1;
@(posedge dut.clk);
dut.reset <= 1'b0;

// Load program and data memory
program_mem.load(pmem);
data_mem.load(dmem);

// Write number of threads to register device_control_data
dut.device_control_data <= threads;
dut.device_control_write_enable <= 1'b1;
@(posedge dut.clk);
dut.device_control_write_enable <= 1'b0;

// Start DUT and wait for it to finish
dut.start <= 1'b1;
end
endtask