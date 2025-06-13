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

// Fix #2: Request buffering - track pending requests per channel
typedef struct packed {
    logic valid;
    logic is_write;
    logic [ADDR_BITS-1:0] addr;
    logic [DATA_BITS-1:0] data;
} request_buffer_t;

request_buffer_t request_queue [CHANNELS];
logic [CHANNELS-1:0] channel_waiting_for_memory;

// Fix #3: Parallel cache lookup for all channels
logic [CHANNELS-1:0] cache_hits_read;
logic [CHANNELS-1:0] cache_hits_write;
logic [LINE_INDEX_BITS-1:0] channel_index [CHANNELS];
logic [TAG_BITS-1:0] channel_tag [CHANNELS];
cache_line_t channel_line [CHANNELS];

// Generate parallel lookups for all channels
genvar i;
generate
    for (i = 0; i < CHANNELS; i++) begin : gen_lookup
        // Calculate index and tag for each channel
        assign channel_index[i] = cache_if.read_valid[i] ? 
                                  cache_if.read_address[i][LINE_INDEX_BITS-1:0] :
                                  cache_if.write_address[i][LINE_INDEX_BITS-1:0];
        
        assign channel_tag[i] = cache_if.read_valid[i] ? 
                                cache_if.read_address[i][ADDR_BITS-1:LINE_INDEX_BITS] :
                                cache_if.write_address[i][ADDR_BITS-1:LINE_INDEX_BITS];
        
        assign channel_line[i] = cache_mem[channel_index[i]];
        
        // Parallel hit detection
        assign cache_hits_read[i] = cache_if.read_valid[i] && 
                                   channel_line[i].valid && 
                                   (channel_line[i].tag == channel_tag[i]);
        
        assign cache_hits_write[i] = cache_if.write_valid[i] && 
                                    channel_line[i].valid && 
                                    (channel_line[i].tag == channel_tag[i]);
    end
endgenerate

// Arbitration - only one channel can use memory interface at a time
logic [$clog2(CHANNELS)-1:0] current_grant;
logic [CHANNELS-1:0] needs_memory;
logic memory_busy;

// Channels that need memory access (misses or writes)
assign needs_memory = ((cache_if.read_valid & ~cache_hits_read) | 
                       cache_if.write_valid) & ~channel_waiting_for_memory;

assign memory_busy = data_mem_if.read_valid[0] || data_mem_if.write_valid[0];

// Fixed: Single always_ff block for arbitration
int candidate;
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        current_grant <= 0;
    end else begin
        // Only advance grant when memory is free AND we need to find a new channel
        if (!memory_busy) begin
            for (int j = 1; j <= CHANNELS; j++) begin
                candidate = (current_grant + j) % CHANNELS;
                if (needs_memory[candidate]) begin
                    current_grant <= candidate;
                    break;
                end
            end
        end
    end
end

// Main cache logic
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        // Reset cache
        for (int i = 0; i < CACHE_LINES; i++) begin
            cache_mem[i].valid <= 1'b0;
            cache_mem[i].tag <= '0;
            cache_mem[i].data <= '0;
        end
        
        // Reset request buffers
        for (int i = 0; i < CHANNELS; i++) begin
            request_queue[i].valid <= 1'b0;
            cache_if.read_ready[i] <= 1'b0;
            cache_if.write_ready[i] <= 1'b0;
            cache_if.read_data[i] <= '0;
        end
        
        channel_waiting_for_memory <= '0;
        data_mem_if.read_valid[0] <= 1'b0;
        data_mem_if.write_valid[0] <= 1'b0;
        
    end else begin
        
        // Handle cache hits immediately in parallel
        for (int i = 0; i < CHANNELS; i++) begin
            // Read hits
            if (cache_hits_read[i]) begin
                cache_if.read_data[i] <= channel_line[i].data;
                cache_if.read_ready[i] <= 1'b1;
            end else if (!cache_if.read_valid[i]) begin
                cache_if.read_ready[i] <= 1'b0;
            end
            
            // Write hits (write-through)
            if (cache_hits_write[i] && !channel_waiting_for_memory[i]) begin
                // Update cache immediately for hits
                cache_mem[channel_index[i]].data <= cache_if.write_data[i];
                // But still need to write through to memory
                request_queue[i].valid <= 1'b1;
                request_queue[i].is_write <= 1'b1;
                request_queue[i].addr <= cache_if.write_address[i];
                request_queue[i].data <= cache_if.write_data[i];
            end else if (!cache_if.write_valid[i]) begin
                cache_if.write_ready[i] <= 1'b0;
            end
        end
        
        // Handle memory interface - clear ready signals first
        for (int i = 0; i < CHANNELS; i++) begin
            if (channel_waiting_for_memory[i] && i != current_grant) begin
                cache_if.read_ready[i] <= 1'b0;
                cache_if.write_ready[i] <= 1'b0;
            end
        end

        // Handle memory completions
        if (data_mem_if.read_ready[0] && data_mem_if.read_valid[0]) begin
            // Memory read completed - find which channel was waiting
            for (int i = 0; i < CHANNELS; i++) begin
                if (channel_waiting_for_memory[i] && request_queue[i].valid && !request_queue[i].is_write) begin
                    logic [LINE_INDEX_BITS-1:0] resp_index;
                    logic [TAG_BITS-1:0] resp_tag;
                    resp_index = request_queue[i].addr[LINE_INDEX_BITS-1:0];
                    resp_tag = request_queue[i].addr[ADDR_BITS-1:LINE_INDEX_BITS];
                    
                    // Update cache
                    cache_mem[resp_index].valid <= 1'b1;
                    cache_mem[resp_index].tag <= resp_tag;
                    cache_mem[resp_index].data <= data_mem_if.read_data[0];
                    
                    // Respond to requesting channel
                    cache_if.read_data[i] <= data_mem_if.read_data[0];
                    cache_if.read_ready[i] <= 1'b1;
                    
                    // Clear request state
                    request_queue[i].valid <= 1'b0;
                    channel_waiting_for_memory[i] <= 1'b0;
                    break;
                end
            end
            // Clear memory interface
            data_mem_if.read_valid[0] <= 1'b0;
            
        end else if (data_mem_if.write_ready[0] && data_mem_if.write_valid[0]) begin
            // Memory write completed - find which channel was waiting
            for (int i = 0; i < CHANNELS; i++) begin
                if (channel_waiting_for_memory[i] && request_queue[i].valid && request_queue[i].is_write) begin
                    // Respond to requesting channel
                    cache_if.write_ready[i] <= 1'b1;
                    
                    // Clear request state
                    request_queue[i].valid <= 1'b0;
                    channel_waiting_for_memory[i] <= 1'b0;
                    break;
                end
            end
            // Clear memory interface
            data_mem_if.write_valid[0] <= 1'b0;
            
        end else if (!memory_busy && needs_memory[current_grant]) begin
            // Start new memory request for current granted channel
            request_queue[current_grant].valid <= 1'b1;
            channel_waiting_for_memory[current_grant] <= 1'b1;
            
            if (cache_if.read_valid[current_grant] && !cache_hits_read[current_grant]) begin
                // Read miss
                request_queue[current_grant].is_write <= 1'b0;
                request_queue[current_grant].addr <= cache_if.read_address[current_grant];
                data_mem_if.read_valid[0] <= 1'b1;
                data_mem_if.read_address[0] <= cache_if.read_address[current_grant];
                cache_if.read_ready[current_grant] <= 1'b0;
                
            end else if (cache_if.write_valid[current_grant]) begin
                // Write (miss or hit with write-through)
                request_queue[current_grant].is_write <= 1'b1;
                request_queue[current_grant].addr <= cache_if.write_address[current_grant];
                request_queue[current_grant].data <= cache_if.write_data[current_grant];
                data_mem_if.write_valid[0] <= 1'b1;
                data_mem_if.write_address[0] <= cache_if.write_address[current_grant];
                data_mem_if.write_data[0] <= cache_if.write_data[current_grant];
                cache_if.write_ready[current_grant] <= 1'b0;
                
                // For write miss, update cache too
                if (!cache_hits_write[current_grant]) begin
                    logic [LINE_INDEX_BITS-1:0] wr_index;
                    logic [TAG_BITS-1:0] wr_tag;
                    wr_index = cache_if.write_address[current_grant][LINE_INDEX_BITS-1:0];
                    wr_tag = cache_if.write_address[current_grant][ADDR_BITS-1:LINE_INDEX_BITS];
                    cache_mem[wr_index].valid <= 1'b1;
                    cache_mem[wr_index].tag <= wr_tag;
                    cache_mem[wr_index].data <= cache_if.write_data[current_grant];
                end
            end
        end
    end
end

endmodule