// `default_nettype none
`timescale 1ns/1ns

// REGISTER FILE
// > Each thread within each core has it's own register file with 13 free registers and 3 read-only registers
// > Read-only registers hold the familiar %blockIdx, %blockDim, and %threadIdx values critical to SIMD
module registers #(
    parameter THREADS_PER_BLOCK = 4,
    parameter THREAD_ID = 0,
    parameter DATA_BITS = 8
) (
    input wire clk,
    input wire reset,
    input wire enable, // If current block has less threads then block size, some registers will be inactive

    // Kernel Execution
    input logic [7:0] block_id,

    // State
    input logic [2:0] core_state,

    // Instruction Signals
    input logic [3:0] decoded_rd_address,
    input logic [3:0] decoded_rs_address,
    input logic [3:0] decoded_rt_address,

    // Control Signals
    input logic decoded_reg_write_enable,
    input logic [1:0] decoded_reg_input_mux,
    input logic [DATA_BITS-1:0] decoded_immediate,

    // Thread Unit Outputs
    input logic [DATA_BITS-1:0] alu_out,
    input logic [DATA_BITS-1:0] lsu_out,

    // Registers
    output logic [7:0] rs,
    output logic [7:0] rt
);
    import states_pkg::*;
    integer i;

    typedef enum logic [1:0] {
        ARITHMETIC = 2'b00,
        MEMORY = 2'b01,
        CONSTANT = 2'b10
    } alu_reg_t;

    // 16 registers per thread (13 free registers and 3 read-only registers)
    logic [7:0] registers[15:0];

    always @(posedge clk) begin
        if (reset) begin
            // Empty rs, rt
            rs <= 0;
            rt <= 0;
            // Initialize all free registers
            for (i = 0; i <= 12; i = i + 1) begin
                registers[i] <= 8'b0;
            end
            // Initialize read-only registers
            registers[13] <= 8'b0;              // %blockIdx
            registers[14] <= THREADS_PER_BLOCK; // %blockDim
            registers[15] <= THREAD_ID;         // %threadIdx
        end else if (enable) begin 
            // [Bad Solution] Shouldn't need to set this every cycle
            registers[13] <= block_id; // Update the block_id when a new block is issued from dispatcher
            
            // Fill rs/rt when core_state = REQUEST
            if (core_state_t'(core_state) == REQUEST) begin 
                rs <= registers[decoded_rs_address];
                rt <= registers[decoded_rt_address];
            end

            // Store rd when core_state = UPDATE
            if (core_state_t'(core_state) == UPDATE) begin 
                // Only allow writing to R0 - R12
                if (decoded_reg_write_enable && decoded_rd_address < 13) begin
                    case (alu_reg_t'(decoded_reg_input_mux))
                        ARITHMETIC: begin 
                            // ADD, SUB, MUL, DIV
                            registers[decoded_rd_address] <= alu_out;
                        end
                        MEMORY: begin 
                            // LDR
                            registers[decoded_rd_address] <= lsu_out;
                        end
                        CONSTANT: begin 
                            // CONST
                            registers[decoded_rd_address] <= decoded_immediate;
                        end
                    endcase
                end
            end
        end
    end
endmodule
