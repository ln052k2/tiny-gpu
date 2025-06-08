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
    logic [2:0] core_state [THREADS_PER_BLOCK-1:0]; // technically, state for each thread
    logic [2:0] fetcher_state [THREADS_PER_BLOCK-1:0];
    logic [15:0] instruction;

    // Intermediate Signals (per thread)
    logic [7:0] current_pc [THREADS_PER_BLOCK-1:0];
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
    // Is this the best way to design this? Probably not...
    // But we're trying to keep as close to the original design as possible
    // i.e core_state being an output of scheduler 
    localparam IDLE = 3'b000, // Waiting to start
        FETCH = 3'b001,       // Fetch instructions from program memory
        DECODE = 3'b010,      // Decode instructions into control signals
        REQUEST = 3'b011,     // Request data from registers or memory
        WAIT = 3'b100,        // Wait for response from memory if necessary
        EXECUTE = 3'b101,     // Execute ALU and PC calculations
        UPDATE = 3'b110,      // Update registers, NZP, and PC
        DONE = 3'b111;        // Done executing this block

    // logic [$clog2(THREADS_PER_BLOCK)-1:0] fetch_thread_ID, decode_thread_ID;
    typedef enum logic [2:0] {
        STAGE_FETCH,
        STAGE_DECODE,
        STAGE_EXECUTE,
        STAGE_MEMORY,
        STAGE_WRITEBACK
    } stage_t;
    localparam int PIPELINE_STAGES = 5;

    // Pipeline registers
    // Stage 1 -> 2: FETCH to DECODE
    typedef struct {
        logic valid;
        logic [7:0] pc;
        logic [15:0] instruction;
        logic [$clog2(THREADS_PER_BLOCK)-1:0] thread_id;
    } fetch_decode_t;
    fetch_decode_t fetch_decode[THREADS_PER_BLOCK-1:0];

    // Stage 2 -> 3: DECODE to EXECUTE
    typedef struct {
        logic [3:0] rd, rs, rt;
        logic [2:0] nzp;
        logic [7:0] immediate;
        logic reg_write_enable, mem_read_enable, 
              mem_write_enable, nzp_write_enable;
        logic [1:0] reg_input_mux, alu_arithmetic_mux;
        logic alu_output_mux, pc_mux, ret;
    } decode_execute_t;
    decode_execute_t decode_execute[THREADS_PER_BLOCK-1:0];

    // Stage 3 -> 4: EXECUTE to MEMORY
    typedef struct {
        // ALU outputs
        logic [7:0] alu_out;
        // LSU outputs
        logic mem_read_valid, mem_write_valid;
        logic [7:0] mem_read_address, mem_write_address, 
                    mem_write_data, lsu_out;
        logic [1:0] lsu_state;
        // Registers outputs
        logic [7:0] rs, rt;
        // Control signals
        logic reg_write_enable, nzp_write_enable;
    } execute_memory_t;
    execute_memory_t execute_memory[THREADS_PER_BLOCK-1:0];

    // Stage 4 -> 5: MEMORY to WRITEBACK
    typedef struct {
        logic valid, reg_write_enable, nzp_write_enable;
        logic ret;
        logic [7:0] pc, alu_result, mem_read_data;
        logic [3:0] rd;
    } memory_writeback_t;
    memory_writeback_t memory_writeback[THREADS_PER_BLOCK-1:0];

    // Scheduler
    scheduler #(
        .THREADS_PER_BLOCK(THREADS_PER_BLOCK),
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

    // Fetcher
    fetcher #(
        .PROGRAM_MEM_ADDR_BITS(PROGRAM_MEM_ADDR_BITS),
        .PROGRAM_MEM_DATA_BITS(PROGRAM_MEM_DATA_BITS)
    ) fetcher_instance (
        .clk(clk),
        .reset(reset),
        .core_state(core_state),
        .current_pc(current_pc[current_thread]),
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
            lsu lsu_instance (
                .clk(clk),
                .reset(reset),
                .enable(i < thread_count),
                .core_state(core_state),
                .decoded_mem_read_enable(decoded_mem_read_enable),
                .decoded_mem_write_enable(decoded_mem_write_enable),
                .mem_read_valid(data_mem_read_valid[i]),
                .mem_read_address(data_mem_read_address[i]),
                .mem_read_ready(data_mem_read_ready[i]),
                .mem_read_data(data_mem_read_data[i]),
                .mem_write_valid(data_mem_write_valid[i]),
                .mem_write_address(data_mem_write_address[i]),
                .mem_write_data(data_mem_write_data[i]),
                .mem_write_ready(data_mem_write_ready[i]),
                .rs(rs[i]),
                .rt(rt[i]),
                .lsu_state(lsu_state[i]),
                .lsu_out(lsu_out[i])
            );

            // Register File
            registers #(
                .THREADS_PER_BLOCK(THREADS_PER_BLOCK),
                .THREAD_ID(i),
                .DATA_BITS(DATA_MEM_DATA_BITS),
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

    // Update pipeline logic
    always_ff @(posedge clk) begin
        for (int i = 0; i < THREADS_PER_BLOCK; i = i + 1) begin
            case (core_state[i])
                IDLE: begin
                    fetch_decode[i].valid <= 0;
                    decode_execute[i].valid <= 0;
                    execute_memory[i].valid <= 0;
                    memory_writeback[i].valid <= 0;
                end

                // FETCH -> DECODE
                FETCH: begin
                    fetch_decode[i].valid        <= 1;
                    fetch_decode[i].instruction  <= program_mem_read_data[i];
                    fetch_decode[i].pc           <= current_pc[i];
                    fetch_decode[i].thread_id    <= i;
                end

                // DECODE -> EXECUTE
                DECODE:
                    decode_execute[i].rd                <= decoded_rd_address;
                    decode_execute[i].rs                <= decoded_rs_address;
                    decode_execute[i].rt                <= decoded_rt_address;
                    decode_execute[i].nzp               <= decoded_nzp;
                    decode_execute[i].immediate         <= decoded_immediate;
                    decode_execute[i].reg_write_enable  <= decoded_reg_write_enable;
                    decode_execute[i].mem_read_enable   <= decoded_mem_read_enable;
                    decode_execute[i].mem_write_enable  <= decoded_mem_write_enable;
                    decode_execute[i].nzp_write_enable  <= decoded_nzp_write_enable;
                    decode_execute[i].reg_input_mux     <= decoded_reg_input_mux;
                    decode_execute[i].alu_arithmetic_mux<= decoded_alu_arithmetic_mux;
                    decode_execute[i].alu_output_mux    <= decoded_alu_output_mux;
                    decode_execute[i].pc_mux            <= decoded_pc_mux;
                    decode_execute[i].ret               <= decoded_ret;

                // EXECUTE -> MEMORY
                EXECUTE:
                    execute_memory[i].alu_out        <= alu_out[i];
                    execute_memory[i].lsu_out        <= lsu_out[i];
                    execute_memory[i].mem_read_valid <= decoded_mem_read_enable;
                    execute_memory[i].mem_write_valid<= decoded_mem_write_enable;
                    execute_memory[i].mem_read_address <= data_mem_read_address[i];
                    execute_memory[i].mem_write_address<= data_mem_write_address[i];
                    execute_memory[i].mem_write_data   <= data_mem_write_data[i];
                    execute_memory[i].lsu_state        <= lsu_state[i];
                    execute_memory[i].rs               <= rs[i];
                    execute_memory[i].rt               <= rt[i];
                    execute_memory[i].reg_write_enable <= decoded_reg_write_enable;
                    execute_memory[i].nzp_write_enable <= decoded_nzp_write_enable;
                
                MEMORY:
                    // MEMORY -> WRITEBACK
                    memory_writeback[i].valid        <= decoded_reg_write_enable;
                    memory_writeback[i].reg_write_enable <= decoded_reg_write_enable;
                    memory_writeback[i].nzp_write_enable <= decoded_nzp_write_enable;
                    memory_writeback[i].ret          <= decoded_ret;
                    memory_writeback[i].pc           <= current_pc[i];
                    memory_writeback[i].alu_result   <= alu_out[i];
                    memory_writeback[i].mem_read_data<= data_mem_read_data[i];
                    memory_writeback[i].rd           <= decoded_rd_address;
            endcase
        end
    end

endmodule