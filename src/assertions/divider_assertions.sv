module divider_assertions #(
  parameter N = 8
) (
  input  logic           clk,
  input  logic           reset,
  input  logic           start,
  input  logic [N-1:0]   dividend,
  input  logic [N-1:0]   divisor,
  input  logic [N-1:0]   result,
  input  logic           done
);

  // after exactly N cycles from the rising-edge of start, ready must be high
  property p_done_after_N;
    // detect a new start assertion (start high and past cycle low)
    @(posedge clk) disable iff (reset)
      $rose(start) |=> ##N done;
  endproperty
  assert property (p_done_after_N)
    else $error("***ERROR: DIVIDER: done not high exactly %0d cycles after start asserted", N);

  // when finished, the result must be correct (unless we're dividing by zero in which case we don't care)
  property p_correct_result;
    @(posedge clk) disable iff (reset)
      ($rose(start) && (divisor !== '0)) 
        |=> ##N (done && (result === dividend / divisor));
  endproperty
  assert property (p_correct_result)
    else $error("***ERROR: DIVIDER: bad result! %0d / %0d; expected %0d, got %0d", dividend, divisor, dividend/divisor, result);
  
endmodule
