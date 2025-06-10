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

            // === READ Channel ===

            // If read_valid is high, read_ready must eventually go high
            property read_acknowledge;
                @(posedge clk)
                disable iff (reset)
                mem.read_valid[ch] |=> ##[1:$] mem.read_ready[ch];
            endproperty
            assert property (read_acknowledge)
                else $error("READ: Channel %0d valid not acknowledged", ch);

            // If read_valid is asserted, address must remain stable
            property read_address_stable;
                @(posedge clk)
                disable iff (reset)
                mem.read_valid[ch] |=> mem.read_valid[ch] &&
                    $stable(mem.read_address[ch]);
            endproperty
            assert property (read_address_stable)
                else $error("READ: Channel %0d address not stable", ch);

            // === WRITE Channel ===

            // If write_valid is high, write_ready must eventually go high
            property write_acknowledge;
                @(posedge clk)
                disable iff (reset)
                mem.write_valid[ch] |=> ##[1:$] mem.write_ready[ch];
            endproperty
            assert property (write_acknowledge)
                else $error("WRITE: Channel %0d valid not acknowledged", ch);

            // If write_valid is asserted, address and data must remain stable
            property write_data_stable;
                @(posedge clk)
                disable iff (reset)
                mem.write_valid[ch] |=> mem.write_valid[ch] &&
                    $stable(mem.write_address[ch]) &&
                    $stable(mem.write_data[ch]);
            endproperty
            assert property (write_data_stable)
                else $error("WRITE: Channel %0d address/data not stable", ch);

            // Ready should not be asserted without valid
            property ready_only_if_valid;
                @(posedge clk)
                disable iff (reset)
                !(mem.read_ready[ch] && !mem.read_valid[ch]) &&
                !(mem.write_ready[ch] && !mem.write_valid[ch]);
            endproperty
            assert property (ready_only_if_valid)
                else $error("Channel %0d: Ready asserted without Valid", ch);

        end
    endgenerate

endmodule