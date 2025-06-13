`include "helpers/memory.sv"
// auto generated and for debug purposes only
module tb;
  localparam ADDR_BITS = 8,
             DATA_BITS = 8,
             CONSUMERS = 1,
             SETS      = 4,
             WAYS      = 4,
             WORDS     = 1;

  reg                   clk;
  reg                   reset;
  reg                   read_valid;
  reg  [ADDR_BITS-1:0]  read_address;
  wire                  read_ready;
  wire                  mem_read_valid;
  wire [ADDR_BITS-1:0]  mem_read_address;
  reg                   mem_read_ready;
  reg  [DATA_BITS-1:0]  mem_read_data;

  // stub memory: simple read-through
  always @(posedge clk) begin
    if (mem_read_valid) begin
      mem_read_ready <= 1;
      mem_read_data  <= mem_read_address[DATA_BITS-1:0];
    end else
      mem_read_ready <= 0;
  end

 mem_if #(
        .ADDR_BITS(8),
        .DATA_BITS(8),
        .CHANNELS(1)
    ) mem_if_test();
 mem_if #(
        .ADDR_BITS(8),
        .DATA_BITS(8),
        .CHANNELS(1)
    ) mem_if_test2();


  cache #(
    .ADDR_BITS(ADDR_BITS),
    .DATA_BITS(DATA_BITS),
    .CONSUMERS(CONSUMERS),
    .SETS(SETS),
    .WAYS(WAYS),
    .WORDS_PER_LINE(WORDS)
  ) uut (
    .clk         (clk),
    .reset       (reset),
    .consumer_if (mem_if_test),
    .memory_if   (mem_if_test_2)
  );

  // clock generator
  initial clk = 0;
  always #5 clk = ~clk;

  // test sequence
  initial begin
    // 1) Reset
    reset = 1;
    read_valid = 0;
    #20;
    reset = 0;

    // 2) Issue one read
    @(posedge clk);
    read_address = 8'h3C;
    read_valid   = 1;
    @(posedge clk);
    read_valid   = 0;

    // 4) Terminate
    #20;
    $finish;
  end
endmodule
