module scheduler_assertions #(
    parameter THREADS_PER_BLOCK = 4
) (
    input  logic clk,
    input  logic reset,
    input  logic start,

    input  logic decoded_mem_read_enable,
    input  logic decoded_mem_write_enable,
    input  logic decoded_ret,

    input  logic [2:0] fetcher_state,
    input  logic [1:0] lsu_state [THREADS_PER_BLOCK-1:0],

    input  logic [7:0] next_pc   [THREADS_PER_BLOCK-1:0],
    input  logic [7:0] current_pc,
    input  logic [2:0] core_state,
    input  logic done
);

    logic [2:0] prev_core_state;
    logic [7:0] prev_pc;
    logic       prev_done;

    always_ff @(posedge clk) begin
        prev_core_state <= core_state;
        prev_pc         <= current_pc;
        prev_done       <= done;
    end

    // Reset initializes state
    property reset_initializes;
        @(posedge clk) reset |=> (core_state == 3'b000 && current_pc == 0 && done == 0);
    endproperty
    assert property (reset_initializes)
        else $error("Reset did not properly initialize scheduler state.");

    // Start triggers transition from IDLE to FETCH
    property start_transitions_to_fetch;
        @(posedge clk)
        disable iff (reset)
        (prev_core_state == 3'b000 && start) |=> (core_state == 3'b001);
    endproperty
    assert property (start_transitions_to_fetch)
        else $error("Start signal did not transition scheduler from IDLE to FETCH.");

    // FETCH -> DECODE if fetcher state is FETCHED
    property fetch_to_decode;
        @(posedge clk)
        disable iff (reset)
        (prev_core_state == 3'b001 && fetcher_state == 3'b010) |=> core_state == 3'b010;
    endproperty
    assert property (fetch_to_decode)
        else $error("Scheduler did not move from FETCH to DECODE correctly.");

    // WAIT -> EXECUTE only when all LSUs are IDLE or DONE
    genvar i;
    generate
        for (i = 0; i < THREADS_PER_BLOCK; i++) begin : lsu_asserts
            property wait_blocks_if_lsu_pending;
                @(posedge clk)
                disable iff (reset)
                (prev_core_state == 3'b100 && (lsu_state[i] == 2'b01 || lsu_state[i] == 2'b10)) |=> core_state == 3'b100;
            endproperty
            assert property (wait_blocks_if_lsu_pending)
                else $error("WAIT state exited while lsu_state[%0d] was still active (REQUESTING or WAITING).", i);
        end
    endgenerate

    // PC updates on UPDATE if no RET
    property pc_updates_on_update;
        @(posedge clk)
        disable iff (reset)
        (prev_core_state == 3'b110 && !decoded_ret)
            |=> current_pc == next_pc[THREADS_PER_BLOCK-1];
    endproperty
    assert property (pc_updates_on_update)
        else $error("PC did not update to expected next_pc[%0d] on UPDATE state.", THREADS_PER_BLOCK-1);

    // Scheduler enters DONE and sets done=1 on RET
    property done_flag_on_ret;
        @(posedge clk)
        disable iff (reset)
        (prev_core_state == 3'b110 && decoded_ret) |=> (done == 1 && core_state == 3'b111);
    endproperty
    assert property (done_flag_on_ret)
        else $error("RET did not set done flag or enter DONE state properly.");

endmodule
