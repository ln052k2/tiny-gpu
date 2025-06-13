module round_robin_arbiter #(
    parameter int N = 4,
)(
    input logic [N-1:0] requests,
    input logic active,
    input logic clk,
    input logic reset,
    output logic [$clog2(N)] grant
);

logic [$clog2(N)-1:0] last_grant;
logic [$clog2(N)-1:0] next_grant;
logic grant_valid;
logic [N-1:0] rotated;

always_comb begin
    int unsigned shift = (last_grant + 1) % N;
    // rotate requests vector
    rotated = (requests << shift) | (requests >> (N - shift));
    grant_valid = 1'b0;
    next_grant = last_grant;
    // 
    for (int i = 0; i < N; i++) begin
        if (!grant_valid && rotated[i]) begin
            grant_valid = 1'b1;
            next_grant = (shift + i) % N;
        end
    end
end

// hold previous grant until new grant computed 
assign grant = (active && grant_valid) ? next_grant : last_grant;


always_ff @(posedge clk or posedge reset) begin
    if (reset)
        last_grant <= '0;
    else if (active && |requests && grant_valid)
        last_grant <= next_grant;
end
endmodule
