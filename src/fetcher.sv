// `default_nettype none
`timescale 1ns/1ns

// INSTRUCTION FETCHER
// > Retrieves the instruction at the current PC from global data memory
// > Each core has it's own fetcher
module fetcher #(
    parameter PROGRAM_MEM_ADDR_BITS = 8,
    parameter PROGRAM_MEM_DATA_BITS = 16
) (
    input wire clk,
    input wire reset,
    
    // Execution State
    input logic [2:0] core_state,
    input logic [7:0] current_pc,

    // Program Memory
    mem_if.mem mem_if,
    // Fetcher Output
    output logic [2:0] fetcher_state,
    output logic [PROGRAM_MEM_DATA_BITS-1:0] instruction
);
    import states_pkg::*;

    always @(posedge clk) begin
        if (reset) begin
            fetcher_state <= FETCHER_IDLE;
            mem_if.read_valid <= 0;
            mem_if.read_address[0] <= {PROGRAM_MEM_ADDR_BITS{1'b0}};
            instruction <= {PROGRAM_MEM_DATA_BITS{1'b0}};
        end else begin
            case (fetcher_state_t'(fetcher_state))
                // careful... states for core/fetcher shouldn't overlap
                FETCHER_IDLE: begin
                    // Start fetching when core_state = FETCH
                    if (core_state_t'(core_state) == FETCH) begin
                        fetcher_state <= FETCHING;
                        mem_if.read_valid <= 1;
                        mem_if.read_address[0] <= current_pc;
                    end
                end
                FETCHING: begin
                    // Wait for response from program memory
                    if (mem_if.read_ready) begin
                        fetcher_state <= FETCHED;
                        instruction <= mem_if.read_data[0]; // Store the instruction when received
                        mem_if.read_valid <= 0;
                    end
                end
                FETCHED: begin
                    // Reset when core_state = DECODE
                    if (core_state_t'(core_state) == DECODE) begin 
                        fetcher_state <= FETCHER_IDLE;
                    end
                end
            endcase
        end
    end
endmodule
