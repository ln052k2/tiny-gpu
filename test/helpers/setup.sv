// Uses helper module Memory -- similar to top module of a testbench
`include "memory.sv"

task automatic setup (
    input  logic       clk,
    output logic       reset,
    output logic       start,
    output logic       device_control_write_enable,
    output logic [7:0] device_control_data,

    ref Memory         program_mem,
    input logic [15:0] pmem[],

    ref Memory         data_mem,
    input logic [7:0]  dmem[],

    input int          threads
); 
begin
    // Reset DUT - assert reset
    reset = 1'b1;
    @(posedge clk);
    reset = 1'b0;

    // Load program and data memory
    program_mem.load(pmem);
    data_mem.load(dmem);

    // Write number of threads to register via device control
    device_control_data = threads[7:0]; // Assuming 8-bit device_control_data
    device_control_write_enable = 1'b1;
    @(posedge clk);
    device_control_write_enable = 1'b0;

    // Start DUT
    start = 1'b1;
    @(posedge clk);
    start = 1'b0;
end
endtask
