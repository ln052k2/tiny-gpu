module round_robin_replacer #(
    parameter int NUM_SETS    = 1,
    parameter int ASSOC       = 1,
    parameter int IDX_BITS    = $clog2(NUM_SETS),
    parameter int WAY_BITS    = $clog2(ASSOC)
) (
    input  wire                 clk,
    input  wire                 reset,
    input  wire                 miss,
    input  wire [IDX_BITS-1:0]  set_index,
    output reg  [WAY_BITS-1:0]  victim
);
    // per‐set pointer
    reg [WAY_BITS-1:0] ptr [NUM_SETS-1:0];
    int i;
    `ifndef SYNTH
    initial begin
        for (i=0; i<NUM_SETS; i=i+1)
            ptr[i] <=0;
    end
    `endif

    always @(posedge clk) begin
        if (reset) begin
            victim <= '0;
            for (i = 0; i < NUM_SETS; i = i + 1)
                ptr[i] <= 0;
        end else if (miss) begin
            victim <= ptr[set_index];
            ptr[set_index] <= ptr[set_index] + 1;
        end
    end
endmodule