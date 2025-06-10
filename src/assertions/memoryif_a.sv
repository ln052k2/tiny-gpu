module mem_if_a #(
    parameter int ADDR_BITS = 8,
    parameter int DATA_BITS = 16,
    parameter int CHANNELS  = 1
)(
    input logic clk,
    input logic reset,
    mem_if.mem mem
);

    // Properties and Assertions
    genvar ch;
    generate
        for (ch = 0; ch < CHANNELS; ch++) begin : assert_per_channel

            // Read and write cannot be simultaneous
            property unique_read_write_p;
                @(posedge clk) disable iff (reset)
                !(mem_if.read_valid[0] && mem_if.write_valid[0]);
            endproperty
            unique_read_write_a: assert property(unique_read_write_p)
                 else $error("LSU attempted to issue both read and write in same cycle");

            // Read valid must be followed by read ready eventually (for now)
            property read_response_p;
                @(posedge clk) disable iff (reset)
                mem_if.read_valid[0] |=> ##[1:15] mem_if.read_ready[0];
            endproperty
            read_response_a: assert property (read_response_p)
                else $error("read_valid was not followed by read_ready");

            // Write valid must be followed by write ready eventually
            property write_response_p;
                @(posedge clk) disable iff (reset)
                mem_if.write_valid[0] |=> ##[1:15] mem_if.write_ready[0];
            endproperty
            write_response_a: assert property (write_response_p)
                else $error("write_valid was not followed by write_ready");

            property read_valid_drop_p;
                @(posedge clk) disable iff (reset)
                mem_if.read_valid[0] ##1 mem_if.read_ready[0] |=> !mem_if.read_valid[0];
            endproperty
            read_valid_drop_a: assert property (read_valid_drop_p)
                else $error("read_valid should be dropped after read_ready");

            property write_valid_drop_p;
                @(posedge clk) disable iff (reset)
                mem_if.write_valid[0] ##1 mem_if.write_ready[0] |=> !mem_if.write_valid[0];
            endproperty
            write_valid_drop_a: assert property (write_valid_drop_p)
                else $error("write_valid should be dropped after write_ready");

    endgenerate

endmodule