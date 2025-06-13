// `default_nettype none
`timescale 1ns/1ns

// ARITHMETIC-LOGIC UNIT
// > Executes computations on register values
// > In this minimal implementation, the ALU supports the 4 basic arithmetic operations
// > Each thread in each core has it's own ALU
// > ADD, SUB, MUL, DIV instructions are all executed here

module alu (
    input wire clk,
    input wire reset,
    input wire enable, // If current block has less threads then block size, some ALUs will be inactive

    input logic [2:0] core_state,

    input logic [1:0] decoded_alu_arithmetic_mux,
    input logic decoded_alu_output_mux,

    input logic [7:0] rs,
    input logic [7:0] rt,
    output wire [7:0] alu_out,

    // division is now multi step
    output wire alu_busy
);
    import alu_ops_pkg::*;
    import alu_state_pkg::*;
    

    logic [7:0] alu_out_reg;
    assign alu_out = alu_out_reg;

    // if we're in a multi step operation, set busy flag
    alu_state_t alu_state;
    assign alu_busy = (alu_state !== IDLE && alu_state !== DONE) || (alu_state == IDLE && decoded_alu_arithmetic_mux == DIV);

    // instantiate divider unit
    logic div_start;
    wire [7:0] div_result;
    wire div_done;
    divider #(.N(8)) divider_unit(.clk(clk), .reset(reset), .start(div_start), .dividend(rs), .divisor(rt), .result(div_result), .done(div_done));
    // bind assertions model, if we should
    `ifndef SILENT
        bind divider_unit divider_assertions divider_assertions_unit(.*);
    `endif

    always @(posedge clk) begin 
        if (alu_state == DONE)
            alu_state <= IDLE;
        if (reset) begin 
            alu_out_reg <= 8'b0;
            alu_state <= IDLE;
        end else if (enable) begin
            div_start <= 'b0;
            if (alu_state == WAIT_DIV) begin
                if (div_done) begin
                    alu_out_reg <= div_result;
                    alu_state <= DONE;
                end
            end else if (core_state == core_states_pkg::EXECUTE) begin 
                if (decoded_alu_output_mux == 1) begin 
                    // Set values to compare with NZP register in alu_out[2:0]
                    alu_out_reg <= {5'b0, (rs - rt > 0), (rs - rt == 0), (rs - rt < 0)};
                end else begin 
                    // Execute the specified arithmetic instruction
                    case (decoded_alu_arithmetic_mux)
                        ADD: begin 
                            alu_out_reg <= rs + rt;
                        end
                        SUB: begin 
                            alu_out_reg <= rs - rt;
                        end
                        MUL: begin 
                            alu_out_reg <= rs * rt;
                        end
                        DIV: begin 
                            div_start <= 1;
                            alu_state <= WAIT_DIV;
                        end
                    endcase
                end
            end
        end
    end
endmodule
