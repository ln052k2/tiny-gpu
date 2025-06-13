`ifndef SYNTHESIS
    `define VERBOSE(args) if (verbose_flag) $display args
`else 
    `define VERBOSE(args) 
`endif

module divider #(parameter N = 8, verbose_flag=0)(
    input  logic               clk,
    input  logic               reset,
    input  logic               start,
    input  logic [N-1:0]   dividend,
    input  logic [N-1:0]   divisor,
    output logic [N-1:0]   result,
    output logic               done
);
typedef enum logic [1:0] {
    IDLE,
    RUN,
    DONE
} state_t;
state_t state;

// shift register for looping
logic [N-2:0] counter;
// register to hold divisor during calculation
logic [N-1:0] divisor_reg;

// partial remainder and quotient go in a joint register
typedef struct packed {
    // remainder needs an extra bit so we can add N-bit divisor... also needs a sign bit
    bit [N+1:0] remainder;
    bit [N-1:0] quotient;
} AQ_reg_t;

// we will use combinational logic to determine new remainder and quotient every cycle
AQ_reg_t AQ_reg, AQ_next;

always_comb begin
    // shift AQ register to the left
    AQ_next = AQ_reg << 1;
    // if the remainder is positive, subtract the divisor, else add the divisor
    if (AQ_next.remainder[N+1] == 0)
        AQ_next.remainder = $signed(AQ_next.remainder - divisor_reg);
    else
        AQ_next.remainder = AQ_next.remainder + divisor_reg;
    // now, if the new remainder is positive, set LSB of quotient to 1, otherwise set it to 0
    if (AQ_next.remainder[N+1] == 0)
        AQ_next.quotient[0] = 1;
    else
        AQ_next.quotient[0] = 0;
end

int c;
always_ff @(posedge clk, posedge reset) begin
    if(reset) begin
        state <= IDLE;
        done <= 1'b0;
        AQ_reg <= 1'b0;
    end else case (state)
        IDLE: begin
            // clear done flag
            done <= 1'b0;
            if (start) begin
                `VERBOSE(("about to calculate %0d / %0d",dividend, divisor));
                c <= 0;
                // load inputs and start processing
                AQ_reg.remainder <= '0;
                AQ_reg.quotient <= dividend;
                divisor_reg <= divisor;
                state <= RUN;
                // initialise shift counter
                counter <= '1;
            end
        end
        RUN: begin
            c <= c+ 1;
            `VERBOSE(("begin step %0d, quotient %b, remainder %b, divisor %b",c,AQ_reg.quotient,AQ_reg.remainder, divisor_reg));
            // since we used combinational logic to calculate the new quotient and remainder, we just store this value in the register
            AQ_reg <= AQ_next;
            // we're finished when the 1 has shifted out of the counter
            if (counter === '0) begin
                state <= DONE;
                done <= 1'b1;
            end
            counter <= (counter << 1);
        end
        DONE: begin
            `VERBOSE(("step %0d, quotient %b, remainder %b",c,AQ_reg.quotient,AQ_reg.remainder));
            `VERBOSE(("took %0d, result: %0d (%0b)", c, result, result));
            state <= IDLE;
        end
    endcase
end

assign result = AQ_reg.quotient;

endmodule