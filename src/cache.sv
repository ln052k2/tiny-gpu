module cache #(
    parameter ADDR_BITS = 8,
    parameter DATA_BITS = 8,
    parameter CHANNELS = 4,
    parameter CACHE_LINES = 16
)(
    input wire clk,
    input wire reset,

    // From LSU
    mem_if.consumer cache_if, // CHANNELS=4

    // To Global Memory
    mem_if.mem data_mem_if
);

    localparam LINE_INDEX_BITS = $clog2(CACHE_LINES);
    localparam TAG_BITS = ADDR_BITS - LINE_INDEX_BITS;

    typedef struct packed {
        logic valid;
        logic [TAG_BITS-1:0] tag;
        logic [DATA_BITS-1:0] data;
    } cache_line_t;

    cache_line_t cache_mem[CACHE_LINES];

    // Arbitration
    logic [$clog2(CHANNELS)-1:0] current_grant;
    logic [CHANNELS-1:0] grant_mask;
    always_comb begin
        grant_mask = '0;
        grant_mask[current_grant] = 1'b1;
    end

    int candidate;
    // Round-robin arbitration
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            current_grant <= 0;
        end else begin
            for (int i = 1; i <= CHANNELS; i++) begin
                candidate = (current_grant + i) % CHANNELS;
                if (cache_if.read_valid[candidate] || cache_if.write_valid[candidate]) begin
                    current_grant <= candidate;
                    break;
                end
            end
        end
    end

    // Cache lookup
    logic [ADDR_BITS-1:0] addr;
    logic [LINE_INDEX_BITS-1:0] index;
    logic [TAG_BITS-1:0] tag;
    cache_line_t line;

    assign addr = cache_if.read_valid[current_grant] ? cache_if.read_address[current_grant] :
                  cache_if.write_valid[current_grant] ? cache_if.write_address[current_grant] :
                  '0;
    assign index = addr[LINE_INDEX_BITS-1:0];
    assign tag = addr[ADDR_BITS-1:LINE_INDEX_BITS];

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            for (int i = 0; i < CACHE_LINES; i++) begin
                cache_mem[i].valid <= 1'b0;
                cache_mem[i].tag <= '0;
                cache_mem[i].data <= '0;
            end
        end else begin
            line = cache_mem[index];

            if (cache_if.read_valid[current_grant]) begin
                if (line.valid && line.tag == tag) begin
                    // Cache hit
                    cache_if.read_data[current_grant] <= line.data;
                    cache_if.read_ready[current_grant] <= 1'b1;
                end else begin
                    // Cache miss
                    cache_if.read_ready[current_grant] <= 1'b0;
                    data_mem_if.read_valid[0] <= 1'b1;
                    data_mem_if.read_address[0] <= addr;

                    if (data_mem_if.read_ready[0]) begin
                        cache_mem[index].valid <= 1'b1;
                        cache_mem[index].tag <= tag;
                        cache_mem[index].data <= data_mem_if.read_data[0];
                        cache_if.read_data[current_grant] <= data_mem_if.read_data[0];
                        cache_if.read_ready[current_grant] <= 1'b1;
                        data_mem_if.read_valid[0] <= 1'b0;
                    end
                end
            end else begin
                cache_if.read_ready[current_grant] <= 1'b0;
            end

            if (cache_if.write_valid[current_grant]) begin
                // Write-through
                data_mem_if.write_valid[0] <= 1'b1;
                data_mem_if.write_address[0] <= addr;
                data_mem_if.write_data[0] <= cache_if.write_data[current_grant];

                cache_mem[index].valid <= 1'b1;
                cache_mem[index].tag <= tag;
                cache_mem[index].data <= cache_if.write_data[current_grant];

                if (data_mem_if.write_ready[0]) begin
                    cache_if.write_ready[current_grant] <= 1'b1;
                    data_mem_if.write_valid[0] <= 1'b0;
                end else begin
                    cache_if.write_ready[current_grant] <= 1'b0;
                end
            end else begin
                cache_if.write_ready[current_grant] <= 1'b0;
            end
        end
    end

    // Clear other channels' ready signals
    generate
        for (genvar i = 0; i < CHANNELS; i++) begin
            if (i != current_grant) begin
                always_comb begin
                    cache_if.read_ready[i] = 0;
                    cache_if.write_ready[i] = 0;
                    cache_if.read_data[i] = 0;
                end
            end
        end
    endgenerate

endmodule
