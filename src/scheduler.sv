// `default_nettype none
`timescale 1ns/1ns

// SCHEDULER
// > Manages the entire control flow of a single compute core processing 1 block
// 1. FETCH - Retrieve instruction at current program counter (PC) from program memory
// 2. DECODE - Decode the instruction into the relevant control signals
// 3. REQUEST - If we have an instruction that accesses memory, trigger the async memory requests from LSUs
// 4. WAIT - Wait for all async memory requests to resolve (if applicable)
// 5. EXECUTE - Execute computations on retrieved data from registers / memory
// 6. UPDATE - Update register values (including NZP register) and program counter
// > Each core has it's own scheduler where multiple threads can be processed with
//   the same control flow at once.
// > Technically, different instructions can branch to different PCs, requiring "branch divergence." In
//   this minimal implementation, we assume no branch divergence (naive approach for simplicity)
module scheduler #(
    parameter THREADS_PER_BLOCK = 4
) (
    input wire clk,
    input wire reset,
    input wire start,
    
    // Control Signals
    input logic decoded_mem_read_enable [THREADS_PER_BLOCK],
    input logic decoded_mem_write_enable [THREADS_PER_BLOCK],
    input logic decoded_ret,

    // Memory Access State
    input logic [2:0] fetcher_state [THREADS_PER_BLOCK-1:0],
    input wire [1:0] lsu_state [THREADS_PER_BLOCK-1:0],

    // Current & Next PC
    output logic [7:0] current_pc [THREADS_PER_BLOCK-1:0],
    input wire [7:0] next_pc [THREADS_PER_BLOCK-1:0],

    // Execution State
    output logic [2:0] core_state [THREADS_PER_BLOCK-1:0],
    // output logic thread_done [THREADS_PER_BLOCK-1:0],
    output logic done
);
    logic [THREADS_PER_BLOCK-1:0] thread_done;
    logic kernel_end;

    localparam IDLE = 3'b000, // Waiting to start
        FETCH = 3'b001,       // Fetch instructions from program memory
        DECODE = 3'b010,      // Decode instructions into control signals
        REQUEST = 3'b011,     // Request data from registers or memory
        WAIT = 3'b100,        // Wait for response from memory if necessary
        EXECUTE = 3'b101,     // Execute ALU and PC calculations
        UPDATE = 3'b110,      // Update registers, NZP, and PC
        DONE = 3'b111;        // Done executing this block

    integer i;
    always @(posedge clk) begin
        if (reset) begin
            kernel_done <= 1'b0;
            done <= 1'b0;
            done_thread <= '0;
            for (i = 0; i < THREADS_PER_BLOCK; i = i + 1) begin
                current_pc[i] <= 0;
                core_state[i] <= IDLE;
            end
        end else begin
            // If decoded_ret is asserted anywhere, set kernel_done flag
            if (decoded_ret)
                kernel_done <= 1'b1;

            for (i = 0; i < THREADS_PER_BLOCK; i = i + 1) begin
                case (core_state[i])
                    IDLE: begin
                        if (start && !kernel_done) begin
                            core_state[i] <= FETCH;
                            done_thread[i] <= 1'b0;
                        end else if (kernel_done) begin
                            done_thread[i] <= 1'b1;
                            core_state[i] <= DONE;
                        end
                    end
                    FETCH: begin
                        if (kernel_done) begin
                            done_thread[i] <= 1'b1;
                            core_state[i] <= DONE;
                        end else if (fetcher_state[i] == 3'b010) begin
                            core_state[i] <= DECODE;
                        end
                    end
                    DECODE: begin
                        core_state[i] <= REQUEST;
                    end
                    REQUEST: begin
                        core_state[i] <= WAIT;
                    end
                    WAIT: begin
                        if (!(lsu_state[i] == 2'b01 || lsu_state[i] == 2'b10)) begin
                            core_state[i] <= EXECUTE;
                        end
                    end
                    EXECUTE: begin
                        core_state[i] <= UPDATE;
                    end
                    UPDATE: begin
                        if (decoded_ret) begin
                            done_thread[i] <= 1'b1;
                            core_state[i] <= DONE;
                        end else begin
                            current_pc[i] <= next_pc[i];
                            core_state[i] <= FETCH;
                        end
                    end
                    DONE: begin
                        done_thread[i] <= 1'b1;
                        // Remain done until reset
                    end
                endcase
            end

            // All threads done => done = 1
            // Will need to have per-thread decoded_ret in the future if supporting branch divergence
            done <= &done_thread;
        end
    end
endmodule