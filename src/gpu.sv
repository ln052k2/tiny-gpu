// `default_nettype none
`timescale 1ns/1ns

// GPU
// > Built to use an external async memory with multi-channel read/write
// > Assumes that the program is loaded into program memory, data into data memory, and threads into
//   the device control register before the start signal is triggered
// > Has memory controllers to interface between external memory and its multiple cores
// > Configurable number of cores and thread capacity per core
module gpu #(
    parameter DATA_MEM_ADDR_BITS = 8,        // Number of bits in data memory address (256 rows)
    parameter DATA_MEM_DATA_BITS = 8,        // Number of bits in data memory value (8 bit data)
    parameter DATA_MEM_NUM_CHANNELS = 4,     // Number of concurrent channels for sending requests to data memory
    parameter PROGRAM_MEM_ADDR_BITS = 8,     // Number of bits in program memory address (256 rows)
    parameter PROGRAM_MEM_DATA_BITS = 16,    // Number of bits in program memory value (16 bit instruction)
    parameter PROGRAM_MEM_NUM_CHANNELS = 1,  // Number of concurrent channels for sending requests to program memory
    parameter NUM_CORES = 2,                 // Number of cores to include in this GPU
    parameter THREADS_PER_BLOCK = 4          // Number of threads to handle per block (determines the compute resources of each core)
) (
    input wire clk,
    input wire reset,

    // Kernel Execution
    input wire start,
    output wire done,

    // Device Control Register
    input wire device_control_write_enable,
    input wire [7:0] device_control_data,

    mem_if.mem program_mem_if,
    mem_if.mem data_mem_if
);

    // Control
    wire [7:0] thread_count;

    // Compute Core State
    logic [NUM_CORES-1:0] core_start;
    logic [NUM_CORES-1:0] core_reset;
    logic [NUM_CORES-1:0] core_done;
    logic [7:0] core_block_id [NUM_CORES-1:0];
    logic [$clog2(THREADS_PER_BLOCK):0] core_thread_count [NUM_CORES-1:0];

    // LSU <> Data Memory Controller Channels
    localparam NUM_LSUS = NUM_CORES * THREADS_PER_BLOCK;
    mem_if #(
        .ADDR_BITS(DATA_MEM_ADDR_BITS),
        .DATA_BITS(DATA_MEM_DATA_BITS),
        .CHANNELS(NUM_LSUS)
    ) lsu_if();

    // Fetcher <> Program Memory Controller Channels
    // Interface encompasses all cores 
    localparam NUM_FETCHERS = NUM_CORES;
    mem_if #(
        .ADDR_BITS(PROGRAM_MEM_ADDR_BITS),
        .DATA_BITS(PROGRAM_MEM_DATA_BITS),
        .CHANNELS(NUM_FETCHERS)
    ) fetcher_if();
    
    // Device Control Register
    dcr dcr_instance (
        .clk(clk),
        .reset(reset),

        .device_control_write_enable(device_control_write_enable),
        .device_control_data(device_control_data),
        .thread_count(thread_count)
    );

    // Data Memory Controller
    controller #(
        .ADDR_BITS(DATA_MEM_ADDR_BITS),
        .DATA_BITS(DATA_MEM_DATA_BITS),
        .NUM_CONSUMERS(NUM_LSUS),
        .NUM_CHANNELS(DATA_MEM_NUM_CHANNELS)
    ) data_memory_controller (
        .clk(clk),
        .reset(reset),

        .consumer_if(lsu_if),
        .mem_if(data_mem_if)
    );

    // Program Memory Controller
    controller #(
        .ADDR_BITS(PROGRAM_MEM_ADDR_BITS),
        .DATA_BITS(PROGRAM_MEM_DATA_BITS),
        .NUM_CONSUMERS(NUM_FETCHERS),
        .NUM_CHANNELS(PROGRAM_MEM_NUM_CHANNELS),
        .WRITE_ENABLE(0)
    ) program_memory_controller (
        .clk(clk),
        .reset(reset),

        .consumer_if(fetcher_if),
        .mem_if(program_mem_if)
    );

    // Dispatcher
    dispatch #(
        .NUM_CORES(NUM_CORES),
        .THREADS_PER_BLOCK(THREADS_PER_BLOCK)
    ) dispatch_instance (
        .clk(clk),
        .reset(reset),
        .start(start),
        .thread_count(thread_count),
        .core_done(core_done),
        .core_start(core_start),
        .core_reset(core_reset),
        .core_block_id(core_block_id),
        .core_thread_count(core_thread_count),
        .done(done)
    );

    // Compute Cores
    genvar i;
    generate
        for (i = 0; i < NUM_CORES; i = i + 1) begin : cores
            // EDA: We create separate signals here to pass to cores because of a requirement
            // by the OpenLane EDA flow (uses Verilog 2005) that prevents slicing the top-level signals
            mem_if #(
                .ADDR_BITS(DATA_MEM_ADDR_BITS),
                .DATA_BITS(DATA_MEM_DATA_BITS),
                .CHANNELS(THREADS_PER_BLOCK)
            ) core_lsu_if();

            // Pass through signals between LSUs and data memory controller
            genvar j;
            for (j = 0; j < THREADS_PER_BLOCK; j = j + 1) begin
                localparam lsu_index = i * THREADS_PER_BLOCK + j;
                always @(posedge clk) begin 
                    lsu_if.read_valid[lsu_index] <= core_lsu_if.read_valid[j];
                    lsu_if.read_address[lsu_index] <= core_lsu_if.read_address[j];

                    lsu_if.write_valid[lsu_index] <= core_lsu_if.write_valid[j];
                    lsu_if.write_address[lsu_index] <= core_lsu_if.write_address[j];
                    lsu_if.write_data[lsu_index] <= core_lsu_if.write_data[j];
                    
                    core_lsu_if.read_ready[j] <= lsu_if.read_ready[lsu_index];
                    core_lsu_if.read_data[j] <= lsu_if.read_data[lsu_index];
                    core_lsu_if.write_ready[j] <= lsu_if.write_ready[lsu_index];
                end
            end

            // Compute Core
            core #(
                .DATA_MEM_ADDR_BITS(DATA_MEM_ADDR_BITS),
                .DATA_MEM_DATA_BITS(DATA_MEM_DATA_BITS),
                .PROGRAM_MEM_ADDR_BITS(PROGRAM_MEM_ADDR_BITS),
                .PROGRAM_MEM_DATA_BITS(PROGRAM_MEM_DATA_BITS),
                .THREADS_PER_BLOCK(THREADS_PER_BLOCK)
            ) core_instance (
                .clk(clk),
                .reset(core_reset[i]),
                .start(core_start[i]),
                .done(core_done[i]),
                .block_id(core_block_id[i]),
                .thread_count(core_thread_count[i]),

                .program_mem_if(core_fetcher_if),                
                .data_mem_if(core_lsu_if)
            );
        end
    endgenerate
endmodule
