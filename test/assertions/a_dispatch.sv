module dispatch_assertions #(
    parameter NUM_CORES = 2,
    parameter THREADS_PER_BLOCK = 4
) (
    input logic clk,
    input logic reset,
    input logic start,
    input logic [7:0] thread_count,
    input logic [NUM_CORES-1:0] core_done,
    input logic [NUM_CORES-1:0] core_start,
    input logic [NUM_CORES-1:0] core_reset,
    input logic [7:0] core_block_id [NUM_CORES-1:0],
    input logic [$clog2(THREADS_PER_BLOCK):0] core_thread_count [NUM_CORES-1:0],
    input logic [7:0] blocks_dispatched,
    input logic [7:0] blocks_done,
    input logic done
);

    wire [7:0] total_blocks;
    assign total_blocks = (thread_count + THREADS_PER_BLOCK - 1) / THREADS_PER_BLOCK;

    // Assert blocks_dispatched never exceeds total_blocks
    property dispatched_bound;
        @(posedge clk) disable iff (reset)
        blocks_dispatched <= total_blocks;
    endproperty
    assert property (dispatched_bound)
        else $error("Too many blocks dispatched! %0d > %0d", blocks_dispatched, total_blocks);

    // Assert blocks_done never exceeds total_blocks
    property blocks_done_bound;
        @(posedge clk) disable iff (reset)
        blocks_done <= total_blocks;
    endproperty
    assert property (blocks_done_bound)
        else $error("Too many blocks marked as done! %0d > %0d", blocks_done, total_blocks);

    // Assert 'done' only goes high when all blocks are done
    property done_when_all_blocks_complete;
        @(posedge clk) disable iff (reset)
        done |-> blocks_done == total_blocks;
    endproperty
    assert property (done_when_all_blocks_complete)
        else $error("Done signal went high before all blocks completed.");

    // Per-core assertions
    genvar i;
    generate
        for (i = 0; i < NUM_CORES; i++) begin : core_asserts

            // Start implies valid block ID and thread count
            property start_has_valid_metadata;
                @(posedge clk) disable iff (reset)
                core_start[i] |-> (core_block_id[i] < total_blocks &&
                    core_thread_count[i] <= THREADS_PER_BLOCK);
            endproperty
            assert property (start_has_valid_metadata)
                else $error("Core %0d started with invalid block_id or thread_count.", i);

            // Final block should have correct thread count
            property final_block_has_correct_count;
                @(posedge clk) disable iff (reset)
                (core_start[i] && core_block_id[i] == total_blocks - 1) |->
                    core_thread_count[i] == thread_count - ((total_blocks - 1) * THREADS_PER_BLOCK);
            endproperty
            assert property (final_block_has_correct_count)
                else $error("Final block dispatched to core %0d has incorrect thread count.", i);

            // core_done should only trigger a reset
            property done_triggers_reset;
                @(posedge clk) disable iff (reset)
                core_done[i] |-> core_reset[i];
            endproperty
            assert property (done_triggers_reset)
                else $error("core_done[%0d] did not result in core_reset.", i);
        end
    endgenerate

endmodule
