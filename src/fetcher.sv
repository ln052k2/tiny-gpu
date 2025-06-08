// `default_nettype none
`timescale 1ns/1ns

// INSTRUCTION FETCHER
// > Retrieves the instruction at the current PC from global data memory
// > Each core has it's own fetcher
module fetcher #(
    parameter PROGRAM_MEM_ADDR_BITS = 8,
    parameter PROGRAM_MEM_DATA_BITS = 16,
    parameter THREADS_PER_BLOCK = 4
) (
    input wire clk,
    input wire reset,
    
    // Execution State
    input logic [2:0] core_state [THREADS_PER_BLOCK-1:0],
    input logic [7:0] current_pc [THREADS_PER_BLOCK-1:0],

    // Program Memory
    output logic mem_read_valid,
    output logic [PROGRAM_MEM_ADDR_BITS-1:0] mem_read_address,
    input logic mem_read_ready,
    input logic [PROGRAM_MEM_DATA_BITS-1:0] mem_read_data,

    // Fetcher Output
    output logic [THREADS_PER_BLOCK-1:0][2:0] fetcher_state,
    output logic [THREADS_PER_BLOCK-1:0][PROGRAM_MEM_DATA_BITS-1:0] instruction
);
    localparam IDLE = 3'b000, 
        FETCHING = 3'b001, 
        FETCHED = 3'b010;
    
    genvar i;
    generate
        for (i = 0; i < THREADS_PER_BLOCK; i++) begin : fetch_thread
            always @(posedge clk) begin
                if (reset) begin
                    fetcher_state[i] <= IDLE;
                    mem_read_valid[i] <= 0;
                    mem_read_address[i] <= 0;
                    instruction[i] <= {PROGRAM_MEM_DATA_BITS{1'b0}};
                end else begin
                    case (fetcher_state[i])
                        IDLE: begin
                            // Start fetching when core_state = FETCH
                            if (core_state[i] == 3'b001) begin
                                fetcher_state[i] <= FETCHING;
                                mem_read_valid[i] <= 1;
                                mem_read_address[i] <= current_pc[i];
                            end
                        end
                        FETCHING: begin
                            // Wait for response from program memory
                            if (mem_read_ready[i]) begin
                                fetcher_state[i] <= FETCHED;
                                instruction[i] <= mem_read_data[i];
                                mem_read_valid[i] <= 0;
                            end
                        end
                        FETCHED: begin
                            // Reset when core_state = DECODE
                            if (core_state[i] == 3'b010) begin
                                fetcher_state[i] <= IDLE;
                            end
                        end
                    endcase
                end
            end
        end
    endgenerate
endmodule
