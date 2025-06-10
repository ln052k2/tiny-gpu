// `default_nettype none
`timescale 1ns/1ns

// COMPUTE CORE
// > Handles processing 1 block at a time
// > The core also has it's own scheduler to manage control flow
// > Each core contains 1 fetcher & decoder, and register files, ALUs, LSUs, PC for each thread
module core #(
    parameter DATA_MEM_ADDR_BITS = 8,
    parameter DATA_MEM_DATA_BITS = 8,
    parameter PROGRAM_MEM_ADDR_BITS = 8,
    parameter PROGRAM_MEM_DATA_BITS = 16,
    parameter THREADS_PER_BLOCK = 4
) (
    input wire clk,
    input wire reset,

    // Kernel Execution
    input wire start,
    output wire done,

    // Block Metadata
    input wire [7:0] block_id,
    input wire [$clog2(THREADS_PER_BLOCK):0] thread_count,

    // Program Memory
    mem_if.mem program_mem_if,
    // Data Memory
    mem_if.mem data_mem_if
);
    // State
    logic [2:0] core_state;
    logic [2:0] fetcher_state;
    logic [15:0] instruction;

    // Intermediate Signals
    logic [7:0] current_pc;
    wire [7:0] next_pc[THREADS_PER_BLOCK-1:0];
    logic [7:0] rs[THREADS_PER_BLOCK-1:0];
    logic [7:0] rt[THREADS_PER_BLOCK-1:0];
    logic [1:0] lsu_state[THREADS_PER_BLOCK-1:0];
    logic [7:0] lsu_out[THREADS_PER_BLOCK-1:0];
    wire [7:0] alu_out[THREADS_PER_BLOCK-1:0];
    
    // Decoded Instruction Signals
    logic [3:0] decoded_rd_address;
    logic [3:0] decoded_rs_address;
    logic [3:0] decoded_rt_address;
    logic [2:0] decoded_nzp;
    logic [7:0] decoded_immediate;

    // Decoded Control Signals
    logic decoded_reg_write_enable;           // Enable writing to a register
    logic decoded_mem_read_enable;            // Enable reading from memory
    logic decoded_mem_write_enable;           // Enable writing to memory
    logic decoded_nzp_write_enable;           // Enable writing to NZP register
    logic [1:0] decoded_reg_input_mux;        // Select input to register
    logic [1:0] decoded_alu_arithmetic_mux;   // Select arithmetic operation
    logic decoded_alu_output_mux;             // Select operation in ALU
    logic decoded_pc_mux;                     // Select source of next PC
    logic decoded_ret;

    // Fetcher
    fetcher #(
        .PROGRAM_MEM_ADDR_BITS(PROGRAM_MEM_ADDR_BITS),
        .PROGRAM_MEM_DATA_BITS(PROGRAM_MEM_DATA_BITS)
    ) fetcher_instance (
        .clk(clk),
        .reset(reset),
        .core_state(core_state),
        .current_pc(current_pc),
        .mem_if(program_mem_if),
        .fetcher_state(fetcher_state),
        .instruction(instruction) 
    );

    // Decoder
    decoder decoder_instance (
        .clk(clk),
        .reset(reset),
        .core_state(core_state),
        .instruction(instruction),
        .decoded_rd_address(decoded_rd_address),
        .decoded_rs_address(decoded_rs_address),
        .decoded_rt_address(decoded_rt_address),
        .decoded_nzp(decoded_nzp),
        .decoded_immediate(decoded_immediate),
        .decoded_reg_write_enable(decoded_reg_write_enable),
        .decoded_mem_read_enable(decoded_mem_read_enable),
        .decoded_mem_write_enable(decoded_mem_write_enable),
        .decoded_nzp_write_enable(decoded_nzp_write_enable),
        .decoded_reg_input_mux(decoded_reg_input_mux),
        .decoded_alu_arithmetic_mux(decoded_alu_arithmetic_mux),
        .decoded_alu_output_mux(decoded_alu_output_mux),
        .decoded_pc_mux(decoded_pc_mux),
        .decoded_ret(decoded_ret)
    );

    // Scheduler
    scheduler #(
        .THREADS_PER_BLOCK(THREADS_PER_BLOCK)
    ) scheduler_instance (
        .clk(clk),
        .reset(reset),
        .start(start),
        .fetcher_state(fetcher_state),
        .core_state(core_state),
        .decoded_mem_read_enable(decoded_mem_read_enable),
        .decoded_mem_write_enable(decoded_mem_write_enable),
        .decoded_ret(decoded_ret),
        .lsu_state(lsu_state),
        .current_pc(current_pc),
        .next_pc(next_pc),
        .done(done)
    );

    // Dedicated ALU, LSU, registers, & PC unit for each thread this core has capacity for
    genvar i;
    generate
        for (i = 0; i < THREADS_PER_BLOCK; i = i + 1) begin : threads
            // ALU
            alu alu_instance (
                .clk(clk),
                .reset(reset),
                .enable(i < thread_count),
                .core_state(core_state),
                .decoded_alu_arithmetic_mux(decoded_alu_arithmetic_mux),
                .decoded_alu_output_mux(decoded_alu_output_mux),
                .rs(rs[i]),
                .rt(rt[i]),
                .alu_out(alu_out[i])
            );

            // LSU
            mem_if #(
                .ADDR_BITS(8),
                .DATA_BITS(8),
                .CHANNELS(1)
            ) lsu_mem_if ();
            
            lsu lsu_instance (
                .clk(clk),
                .reset(reset),
                .enable(i < thread_count),
                .core_state(core_state),
                .decoded_mem_read_enable(decoded_mem_read_enable),
                .decoded_mem_write_enable(decoded_mem_write_enable),
                .mem_if(lsu_mem_if),
                .rs(rs[i]),
                .rt(rt[i]),
                .lsu_state(lsu_state[i]),
                .lsu_out(lsu_out[i])
            );

            // Register File
            registers #(
                .THREADS_PER_BLOCK(THREADS_PER_BLOCK),
                .THREAD_ID(i),
                .DATA_BITS(DATA_MEM_DATA_BITS)
            ) register_instance (
                .clk(clk),
                .reset(reset),
                .enable(i < thread_count),
                .block_id(block_id),
                .core_state(core_state),
                .decoded_reg_write_enable(decoded_reg_write_enable),
                .decoded_reg_input_mux(decoded_reg_input_mux),
                .decoded_rd_address(decoded_rd_address),
                .decoded_rs_address(decoded_rs_address),
                .decoded_rt_address(decoded_rt_address),
                .decoded_immediate(decoded_immediate),
                .alu_out(alu_out[i]),
                .lsu_out(lsu_out[i]),
                .rs(rs[i]),
                .rt(rt[i])
            );

            // Program Counter
            pc #(
                .DATA_MEM_DATA_BITS(DATA_MEM_DATA_BITS),
                .PROGRAM_MEM_ADDR_BITS(PROGRAM_MEM_ADDR_BITS)
            ) pc_instance (
                .clk(clk),
                .reset(reset),
                .enable(i < thread_count),
                .core_state(core_state),
                .decoded_nzp(decoded_nzp),
                .decoded_immediate(decoded_immediate),
                .decoded_nzp_write_enable(decoded_nzp_write_enable),
                .decoded_pc_mux(decoded_pc_mux),
                .alu_out(alu_out[i]),
                .current_pc(current_pc),
                .next_pc(next_pc[i])
            );
        end
    endgenerate
endmodule
