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
    output logic program_mem_read_valid,
    output logic [PROGRAM_MEM_ADDR_BITS-1:0] program_mem_read_address,
    input logic program_mem_read_ready,
    input logic [PROGRAM_MEM_DATA_BITS-1:0] program_mem_read_data,

    // Data Memory
    output logic [THREADS_PER_BLOCK-1:0] data_mem_read_valid,
    output logic [DATA_MEM_ADDR_BITS-1:0] data_mem_read_address [THREADS_PER_BLOCK-1:0],
    input logic [THREADS_PER_BLOCK-1:0] data_mem_read_ready,
    input wire [DATA_MEM_DATA_BITS-1:0] data_mem_read_data [THREADS_PER_BLOCK-1:0],
    output logic [THREADS_PER_BLOCK-1:0] data_mem_write_valid,
    output logic [DATA_MEM_ADDR_BITS-1:0] data_mem_write_address [THREADS_PER_BLOCK-1:0],
    output logic [DATA_MEM_DATA_BITS-1:0] data_mem_write_data [THREADS_PER_BLOCK-1:0],
    input logic [THREADS_PER_BLOCK-1:0] data_mem_write_ready
);
    // State
    logic [2:0] core_state;
    logic [2:0] fetcher_state;
    logic [15:0] instruction;
    logic [7:0] current_pc;

    // Intermediate Signals (per thread)
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

    // Pipeline Stages
    typedef enum logic [2:0] {
        IF = 3'b000,  // Instruction Fetch
        ID = 3'b001,  // Instruction Decode
        EX = 3'b010,  // Execute
        MEM = 3'b011, // Memory Access
        WB = 3'b100   // Write Back
    } stage_t;
    localparam int PIPELINE_STAGES = 5;

    // Pipeline Register
    typedef struct packed {
        logic [7:0] pc;
        logic [15:0] instruction;
        logic decoded_reg_write_enable;
        logic decoded_mem_read_enable;
        logic decoded_mem_write_enable;
        logic decoded_nzp_write_enable;
        logic [3:0] decoded_rd_address;
        logic [3:0] decoded_rs_address;
        logic [3:0] decoded_rt_address;
        logic [2:0] decoded_nzp;
        logic [7:0] decoded_immediate;
        logic [1:0] decoded_reg_input_mux;
        logic [1:0] decoded_alu_arithmetic_mux;
        logic decoded_alu_output_mux;
        logic decoded_pc_mux;
        logic decoded_ret;
        logic [7:0] rs;
        logic [7:0] rt;
        logic [7:0] alu_out;
        logic [1:0] lsu_state;
        logic [7:0] lsu_out;
    } p_register_t;

    p_register_t pipeline_regs[THREADS_PER_BLOCK-1:0][PIPELINE_STAGES-1:0];

    always_ff @(posedge clk) begin
        for (int i = 0; i < THREADS_PER_BLOCK; i++) begin
            if (reset) begin
                if_id[i].valid    <= 0;
                id_ex[i].valid    <= 0;
                ex_mem[i].valid   <= 0;
                mem_wb[i].valid   <= 0;
            end else if (i < thread_count) begin
                mem_wb[i] <= ex_mem[i];
                ex_mem[i] <= id_ex[i];
                id_ex[i]  <= if_id[i];
                if_id[i]  <= fetch_output[i];  // You define this from fetcher
            end
        end
    end


    // Fetcher
    fetcher #(
        .PROGRAM_MEM_ADDR_BITS(PROGRAM_MEM_ADDR_BITS),
        .PROGRAM_MEM_DATA_BITS(PROGRAM_MEM_DATA_BITS)
    ) fetcher_instance (
        .clk(clk),
        .reset(reset),
        .core_state(core_state),
        .current_pc(current_pc),
        .mem_read_valid(program_mem_read_valid),
        .mem_read_address(program_mem_read_address),
        .mem_read_ready(program_mem_read_ready),
        .mem_read_data(program_mem_read_data),
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
                .decoded_alu_arithmetic_mux(pipeline_regs[i][STAGE_EXECUTE].decoded_alu_arithmetic_mux),
                .decoded_alu_output_mux(pipeline_regs[i][STAGE_EXECUTE].decoded_alu_output_mux),
                .rs(pipeline_regs[i][STAGE_EXECUTE].rs),
                .rt(pipeline_regs[i][STAGE_EXECUTE].rt),
                .alu_out(alu_out[i])
            );

            // LSU
            lsu lsu_instance (
                .clk(clk),
                .reset(reset),
                .enable(i < thread_count),
                .core_state(core_state),
                .decoded_mem_read_enable(pipeline_regs[i][STAGE_MEMORY].decoded_mem_read_enable),
                .decoded_mem_write_enable(pipeline_regs[i][STAGE_MEMORY].decoded_mem_write_enable),
                .mem_read_valid(data_mem_read_valid[i]),
                .mem_read_address(data_mem_read_address[i]),
                .mem_read_ready(data_mem_read_ready[i]),
                .mem_read_data(data_mem_read_data[i]),
                .mem_write_valid(data_mem_write_valid[i]),
                .mem_write_address(data_mem_write_address[i]),
                .mem_write_data(data_mem_write_data[i]),
                .mem_write_ready(data_mem_write_ready[i]),
                .rs(pipeline_regs[i][STAGE_MEMORY].rs),
                .rt(pipeline_regs[i][STAGE_MEMORY].rt),
                .lsu_state(lsu_state[i]),
                .lsu_out(lsu_out[i])
            );

            // Register Files
            registers #(
                .THREADS_PER_BLOCK(THREADS_PER_BLOCK),
                .THREAD_ID(i),
                .DATA_BITS(DATA_MEM_DATA_BITS)
            ) registers_instance (
                .clk(clk),
                .reset(reset),
                .enable(i < thread_count),
                .block_id(block_id),
                .core_state(core_state),
                .decoded_reg_write_enable(pipeline_regs[i][STAGE_WRITEBACK].decoded_reg_write_enable),
                .decoded_reg_input_mux(pipeline_regs[i][STAGE_WRITEBACK].decoded_reg_input_mux),
                .decoded_rd_address(pipeline_regs[i][STAGE_WRITEBACK].decoded_rd_address),
                .decoded_rs_address(pipeline_regs[i][STAGE_WRITEBACK].decoded_rs_address),
                .decoded_rt_address(pipeline_regs[i][STAGE_WRITEBACK].decoded_rt_address),
                .decoded_immediate(pipeline_regs[i][STAGE_WRITEBACK].decoded_immediate),
                .alu_out(alu_out[i]),
                .lsu_out(lsu_out[i]),
                .rs(rs[i]),
                .rt(rt[i])
            );

            // PC
            pc #(
                .DATA_MEM_DATA_BITS(DATA_MEM_DATA_BITS),
                .PROGRAM_MEM_ADDR_BITS(PROGRAM_MEM_ADDR_BITS)
            ) pc_instance (
                .clk(clk),
                .reset(reset),
                .enable(i < thread_count),
                .core_state(core_state),
                .decoded_nzp(pipeline_regs[i][STAGE_WRITEBACK].decoded_nzp),
                .decoded_immediate(pipeline_regs[i][STAGE_WRITEBACK].decoded_immediate),
                .decoded_nzp_write_enable(pipeline_regs[i][STAGE_WRITEBACK].decoded_nzp_write_enable),
                .decoded_pc_mux(pipeline_regs[i][STAGE_WRITEBACK].decoded_pc_mux),
                .alu_out(alu_out[i]),
                .current_pc(pipeline_regs[i][STAGE_WRITEBACK].pc),
                .next_pc()  // Next PC logic here or pipelined separately
            );
        end
    endgenerate

    // Pipeline register update and advance logic
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            integer t, s;
            for (t = 0; t < THREADS_PER_BLOCK; t = t + 1) begin
                for (s = 0; s < PIPELINE_STAGES; s = s + 1) begin
                    pipeline_regs[t][s] <= '0;
                end
            end
        end else begin
            integer t;
            for (t = 0; t < THREADS_PER_BLOCK; t = t + 1) begin
                // Advance pipeline stages for each thread
                pipeline_regs[t][STAGE_WRITEBACK] <= pipeline_regs[t][STAGE_MEMORY];
                pipeline_regs[t][STAGE_MEMORY]    <= pipeline_regs[t][STAGE_EXECUTE];
                pipeline_regs[t][STAGE_EXECUTE]   <= pipeline_regs[t][STAGE_DECODE];
                pipeline_regs[t][STAGE_DECODE]    <= pipeline_regs[t][STAGE_FETCH];

                // Fetch stage gets new inputs
                pipeline_regs[t][STAGE_FETCH].pc           <= /* current PC for thread t */;
                pipeline_regs[t][STAGE_FETCH].instruction  <= /* fetched instruction for thread t */;
                pipeline_regs[t][STAGE_FETCH].decoded_reg_write_enable <= decoded_reg_write_enable;
                pipeline_regs[t][STAGE_FETCH].decoded_mem_read_enable  <= decoded_mem_read_enable;
                pipeline_regs[t][STAGE_FETCH].decoded_mem_write_enable <= decoded_mem_write_enable;
                pipeline_regs[t][STAGE_FETCH].decoded_nzp_write_enable <= decoded_nzp_write_enable;
                pipeline_regs[t][STAGE_FETCH].decoded_rd_address       <= decoded_rd_address;
                pipeline_regs[t][STAGE_FETCH].decoded_rs_address       <= decoded_rs_address;
                pipeline_regs[t][STAGE_FETCH].decoded_rt_address       <= decoded_rt_address;
                pipeline_regs[t][STAGE_FETCH].decoded_nzp              <= decoded_nzp;
                pipeline_regs[t][STAGE_FETCH].decoded_immediate        <= decoded_immediate;
                pipeline_regs[t][STAGE_FETCH].decoded_reg_input_mux    <= decoded_reg_input_mux;
                pipeline_regs[t][STAGE_FETCH].decoded_alu_arithmetic_mux <= decoded_alu_arithmetic_mux;
                pipeline_regs[t][STAGE_FETCH].decoded_alu_output_mux   <= decoded_alu_output_mux;
                pipeline_regs[t][STAGE_FETCH].decoded_pc_mux           <= decoded_pc_mux;
                pipeline_regs[t][STAGE_FETCH].decoded_ret              <= decoded_ret;
                // Set rs, rt, alu_out, lsu_state, lsu_out as needed or 0 for fetch stage
                pipeline_regs[t][STAGE_FETCH].rs                       <= 0;
                pipeline_regs[t][STAGE_FETCH].rt                       <= 0;
                pipeline_regs[t][STAGE_FETCH].alu_out                  <= 0;
                pipeline_regs[t][STAGE_FETCH].lsu_state                <= 0;
                pipeline_regs[t][STAGE_FETCH].lsu_out                  <= 0;
            end
        end
    end
endmodule
