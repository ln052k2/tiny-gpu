module round_robin_replacement #(
  parameter int SETS = 4,
  parameter int WAYS = 4,
  // derived
  localparam int SET_BITS = $clog2(SETS),
  localparam int WAY_BITS = $clog2(WAYS)
)(
  input logic clk,
  input logic reset,

  // which set needs an eviction?
  input logic [SET_BITS-1:0] set_idx,

  // pulse high for exactly one cycle when you decide to evict
  input logic evict_req,
  // which way should be evicted this cycle?
  output logic [WAY_BITS-1:0] victim_way;
);

  // one pointer per set
  logic [WAY_BITS-1:0] rr_ptr [SETS];

  // on reset initialize all pointers to zero
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      for (int s = 0; s < SETS; s++)
        rr_ptr[s] <= '0;
    end else if (evict_req) begin
      // bump the pointer for this set
      rr_ptr[set_idx] <= rr_ptr[set_idx] + 1;
    end
  end

  // combinationally expose the current pointer as the victim
  assign victim_way = rr_ptr[set_idx];

endmodule
