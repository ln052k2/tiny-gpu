module test_arbiter;
    localparam int N = 4;

    logic [N-1:0] requests;
    logic active;
    logic clk;
    logic reset;

    logic [$clog2(N)-1:0] grant;

    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    round_robin_arbiter #(.N(N)) dut (
        .requests(requests),
        .active(active),
        .clk(clk),
        .reset(reset),
        .grant(grant)
    );

    initial begin
        $display("time | Reset | active | requests | grant");
        $monitor("%4t |  %b    |   %b    |   %b    |  %d", $time, reset, active, requests, grant);
    end

    initial begin
        //initialize
        reset = 1;
        active = 0;
        requests = '0;
        #20;
        reset = 0;
        // run some basic tests just for manual checking
        active = 1;
        requests = 4'b0000;
        #10;
        requests = 4'b0010;
        #10;
        requests = 4'b1010;
        requests = 4'b1010;
        #10;
        requests = 4'b1111;
        #40; // step through several grants
        active = 0;
        requests = 4'b0101;
        #20;
        $display("\n***FINISHED");
        $finish;
    end
endmodule
