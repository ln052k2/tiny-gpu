`timescale 1ns/1ps

module test_divider;
  parameter N = 8;
  localparam MAX = 2**N;

  // Clock & reset
  logic clk;
  logic reset;

  // DUT interface
  logic start;
  logic [N-1:0] dividend, divisor;
  logic [N-1:0] result;
  logic done;

  // Instantiate DUT and assertion wrapper
  divider #(.N(N), .verbose_flag(0)) dut (
    .clk      (clk),
    .reset    (reset),
    .start    (start),
    .dividend (dividend),
    .divisor  (divisor),
    .result   (result),
    .done     (done)
  );
  `ifndef QUIET
bind dut divider_assertions dut_assert(.*);
`endif
  always #5 clk = ~clk;

  initial begin
    automatic int i, j;
    bit failed_by_divisor[int][int];
    bit failed_by_dividend[int][int];
    clk      = 0;
    reset    = 1;
    start    = 0;
    dividend = '0;
    divisor  = '0;
    // hold reset for one cycle
    #1;
    reset = 0;
    // exhaustive
    for (i = 0; i < MAX; i+=1) begin
      for (j = 0; j < MAX; j+=1) begin
        dividend = i[N-1:0];
        divisor  = j[N-1:0];

        @(posedge clk);
        start = 1;
        @(posedge clk);
        start = 0;

        wait (done);
        if (result != dividend / divisor) begin
            failed_by_divisor[divisor][dividend] = 1;
            failed_by_dividend[dividend][divisor] = 1;

        @(posedge clk);
      end
    end

        
            
    end
    foreach(failed_by_dividend[key]) $display("%0d failed with %0d divisors", key, failed_by_dividend[key].size());
    foreach(failed_by_divisor[key]) $display("%0d failed with %0d dividends", key, failed_by_divisor[key].size());
    // All done
    $display("** Exhaustive tests complete");
    $finish;
  end

endmodule
