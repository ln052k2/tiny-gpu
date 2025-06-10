module divider #(parameter N = 8)(
    input  logic               clk,
    input  logic               reset,
    input  logic               start,
    input  logic [N-1:0]   dividend,
    input  logic [N-1:0]   divisor,
    output logic [N-1:0]   result,
    output logic               done
);
int n_cycles;
    typedef enum logic [1:0] {
        IDLE,
        RUN,
        DONE
    } state_t;

    state_t state, next_state;

    logic signed [N:0]   acc; 
    logic [N-1:0]        q;  // quotient
    logic [N-1:0]        m;  // remainder
    logic [$clog2(N+1)-1:0] count;
    logic [N-1:0]        dividend_reg;

    assign result = q;
    assign done = (state == DONE);

    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            state <= IDLE;
        else
            state <= next_state;
    end

    always_comb begin
        case (state)
            IDLE:  next_state = start ? RUN : IDLE;
            RUN:   next_state = (count == N-1) ? DONE : RUN;
            DONE:  next_state = IDLE;
            default: next_state = IDLE;
        endcase
    end

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            acc <= 0;
            q <= 0;
            m <= 0;
            count <= 0;
        end else begin
            case (state)
                IDLE: begin
                    if (start) begin
                        acc <= 0;
                        dividend_reg <= dividend;
                        q <= dividend;
                        m <= divisor;
                        count <= 0;
                    end
                end

                RUN: begin
                    // shift left (acc || q)
                    acc = {acc[N-1:0], q[N-1]};
                    q   = {q[N-2:0], 1'b0};

                    // perform subtraction or addition based on acc sign
                    if (acc[N] == 1) 
                        acc = acc + m;
                    else
                        acc = acc - m;

                    // set new quotient bit
                    if (acc[N] == 1) 
                        q[0] = 0;
                    else
                        q[0] = 1;

                    count <= count + 1;

                    // correction after final step, if remainder is negative
                    if (count == N - 1) begin
                        if (acc[N] == 1) 
                            acc = acc + m;
                    end
                end
                DONE: begin
                        //nop
                end
            endcase
        end
    end

endmodule
