// `default_nettype none
`timescale 1ns/1ns

// LOAD-STORE UNIT
// > Handles asynchronous memory load and store operations and waits for response
// > Each thread in each core has it's own LSU
// > LDR, STR instructions are executed here
module lsu (
    input wire clk,
    input wire reset,
    input wire enable, // If current block has less threads then block size, some LSUs will be inactive

    // State
    input logic [2:0] core_state,

    // Memory Control Sgiansl
    input logic decoded_mem_read_enable,
    input logic decoded_mem_write_enable,

    // Registers
    input logic [7:0] rs,
    input logic [7:0] rt,

    // Data Memory
    // output logic mem_read_valid,
    // output logic [7:0] mem_read_address,
    // input logic mem_read_ready,
    // input logic [7:0] mem_read_data,
    // output logic mem_write_valid,
    // output logic [7:0] mem_write_address,
    // output logic [7:0] mem_write_data,
    // input logic mem_write_ready,
    mem_if.mem mem_if

    // LSU Outputs
    output logic [1:0] lsu_state,
    output logic [7:0] lsu_out
);
    localparam IDLE = 2'b00, REQUESTING = 2'b01, WAITING = 2'b10, DONE = 2'b11;

    always @(posedge clk) begin
        if (reset) begin
            lsu_state <= IDLE;
            lsu_out <= 0;
            mem_if.read_valid <= 0;
            mem_if.read_address <= 0;
            mem_if.write_valid <= 0;
            mem_if.write_address <= 0;
            mem_if.write_data <= 0;
        end else if (enable) begin
            // If memory read enable is triggered (LDR instruction)
            if (decoded_mem_read_enable) begin 
                case (lsu_state)
                    IDLE: begin
                        // Only read when core_state = REQUEST
                        if (core_state == 3'b011) begin 
                            lsu_state <= REQUESTING;
                        end
                    end
                    REQUESTING: begin 
                        mem_if.read_valid <= 1;
                        mem_if.read_address <= rs;
                        lsu_state <= WAITING;
                    end
                    WAITING: begin
                        if (mem_if.read_ready == 1) begin
                            mem_if.read_valid <= 0;
                            lsu_out <= mem_if.read_data;
                            lsu_state <= DONE;
                        end
                    end
                    DONE: begin 
                        // Reset when core_state = UPDATE
                        if (core_state == 3'b110) begin 
                            lsu_state <= IDLE;
                        end
                    end
                endcase
            end

            // If memory write enable is triggered (STR instruction)
            if (decoded_mem_write_enable) begin 
                case (lsu_state)
                    IDLE: begin
                        // Only read when core_state = REQUEST
                        if (core_state == 3'b011) begin 
                            lsu_state <= REQUESTING;
                        end
                    end
                    REQUESTING: begin 
                        mem_if.write_valid <= 1;
                        mem_if.write_address <= rs;
                        mem_if.write_data <= rt;
                        lsu_state <= WAITING;
                    end
                    WAITING: begin
                        if (mem_if.write_ready) begin
                            mem_if.write_valid <= 0;
                            lsu_state <= DONE;
                        end
                    end
                    DONE: begin 
                        // Reset when core_state = UPDATE
                        if (core_state == 3'b110) begin 
                            lsu_state <= IDLE;
                        end
                    end
                endcase
            end
        end
    end
endmodule
