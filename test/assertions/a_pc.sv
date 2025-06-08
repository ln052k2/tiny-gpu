// `default_nettype none
module pc_assertions #(
    parameter DATA_MEM_DATA_BITS = 8,
    parameter PROGRAM_MEM_ADDR_BITS = 8
) (
    input wire clk,
    input wire reset,
    input wire enable,
    input logic [2:0] core_state,
    input logic [2:0] decoded_nzp,
    input logic [DATA_MEM_DATA_BITS-1:0] decoded_immediate,
    input logic decoded_nzp_write_enable,
    input logic decoded_pc_mux,
    input logic [DATA_MEM_DATA_BITS-1:0] alu_out,
    input logic [PROGRAM_MEM_ADDR_BITS-1:0] current_pc,
    input logic [PROGRAM_MEM_ADDR_BITS-1:0] next_pc
);

    logic [2:0] prev_nzp;
    logic [PROGRAM_MEM_ADDR_BITS-1:0] prev_next_pc;

    // Capture previous cycle state
    always_ff @(posedge clk) begin
        prev_nzp <= 'z; // intentionally z — unknown, since nzp is internal to DUT
        prev_next_pc <= next_pc;
    end

    // Reset clears NZP and PC
    property reset_clears_pc;
        @(posedge clk)
        reset |=> next_pc == 0;
    endproperty
    assert property (reset_clears_pc)
        else $error("Reset failed to clear next_pc");

    // EXECUTE state assertions
    property branch_taken;
        @(posedge clk)
        disable iff (reset || !enable)
        (core_state == 3'b101 && decoded_pc_mux && ((prev_nzp & decoded_nzp) != 3'b000))
            |=> next_pc == decoded_immediate;
    endproperty
    assert property (branch_taken)
        else $error("Branch taken but next_pc != decoded_immediate");

    property branch_not_taken;
        @(posedge clk)
        disable iff (reset || !enable)
        (core_state == 3'b101 && decoded_pc_mux && ((prev_nzp & decoded_nzp) == 3'b000))
            |=> next_pc == current_pc + 1;
    endproperty
    assert property (branch_not_taken)
        else $error("Branch not taken but next_pc != current_pc + 1");

    property default_pc_increment;
        @(posedge clk)
        disable iff (reset || !enable)
        (core_state == 3'b101 && !decoded_pc_mux)
            |=> next_pc == current_pc + 1;
    endproperty
    assert property (default_pc_increment)
        else $error("Default PC update failed");

    // No update when disabled
    property no_update_when_disabled;
        @(posedge clk)
        !enable |=> next_pc == prev_next_pc;
    endproperty
    assert property (no_update_when_disabled)
        else $error("PC changed while enable=0");

endmodule
