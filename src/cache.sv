// Per-Core L1 Data Cache for tiny-gpu
// This cache is instantiated directly inside each core.sv
// Sits between the core's LSUs and the data memory controller

module core_l1_cache #(
    parameter CACHE_SIZE = 16,              // Number of cache lines per core
    parameter ADDR_BITS = 8,                // Address width
    parameter DATA_BITS = 8,                // Data width
    parameter THREADS_PER_BLOCK = 4,        // LSUs per core
    parameter TAG_BITS = 4,                 // Tag width
    parameter INDEX_BITS = 4                // Index width
) (
    input wire clk,
    input wire reset,
    
    // Interface TO core's LSUs (cache appears as memory controller to LSUs)
    input wire [THREADS_PER_BLOCK-1:0] lsu_read_valid,
    input wire [ADDR_BITS-1:0] lsu_read_address [THREADS_PER_BLOCK-1:0],
    output logic [THREADS_PER_BLOCK-1:0] lsu_read_ready,
    output logic [DATA_BITS-1:0] lsu_read_data [THREADS_PER_BLOCK-1:0],
    input wire [THREADS_PER_BLOCK-1:0] lsu_write_valid,
    input wire [ADDR_BITS-1:0] lsu_write_address [THREADS_PER_BLOCK-1:0],
    input wire [DATA_BITS-1:0] lsu_write_data [THREADS_PER_BLOCK-1:0],
    output logic [THREADS_PER_BLOCK-1:0] lsu_write_ready,
    
    // Interface FROM cache to data memory controller (core's external interface)
    output logic mem_read_valid,
    output logic [ADDR_BITS-1:0] mem_read_address,
    input wire mem_read_ready,
    input wire [DATA_BITS-1:0] mem_read_data,
    output logic mem_write_valid,
    output logic [ADDR_BITS-1:0] mem_write_address,
    output logic [DATA_BITS-1:0] mem_write_data,
    input wire mem_write_ready,
    
    // Cache control
    input wire cache_flush
);

    // Cache storage
    logic [DATA_BITS-1:0] cache_data [0:CACHE_SIZE-1];
    logic [TAG_BITS-1:0] cache_tags [0:CACHE_SIZE-1];
    logic cache_valid [0:CACHE_SIZE-1];
    logic cache_dirty [0:CACHE_SIZE-1];
    
    // Current serving LSU (round-robin within core)
    logic [$clog2(THREADS_PER_BLOCK)-1:0] serving_lsu;
    logic [$clog2(THREADS_PER_BLOCK)-1:0] next_serving_lsu;
    
    // Current request
    logic current_is_read;
    logic [ADDR_BITS-1:0] current_addr;
    logic [DATA_BITS-1:0] current_wdata;
    
    // Address decomposition
    wire [TAG_BITS-1:0] addr_tag = current_addr[ADDR_BITS-1:ADDR_BITS-TAG_BITS];
    wire [INDEX_BITS-1:0] addr_index = current_addr[INDEX_BITS-1:0];
    
    // Cache line access
    wire [TAG_BITS-1:0] line_tag = cache_tags[addr_index];
    wire line_valid = cache_valid[addr_index];
    wire line_dirty = cache_dirty[addr_index];
    wire [DATA_BITS-1:0] line_data = cache_data[addr_index];
    
    // Hit detection
    wire cache_hit_detected = line_valid && (line_tag == addr_tag);
    
    // Cache state machine
    typedef enum logic [2:0] {
        IDLE,
        CHECK_HIT,
        WRITEBACK,
        ALLOCATE_READ,
        ALLOCATE_WRITE,
        COMPLETE
    } cache_state_t;
    
    cache_state_t state, next_state;
    
    // Victim line handling
    logic [ADDR_BITS-1:0] victim_addr;
    logic [DATA_BITS-1:0] victim_data;
    
    // State machine transitions
    always_ff @(posedge clk) begin
        if (reset) begin
            state <= IDLE;
        end else begin
            state <= next_state;
        end
    end
    
    always_comb begin
        next_state = state;
        
        case (state)
            IDLE: begin
                if (lsu_read_valid[serving_lsu] || lsu_write_valid[serving_lsu]) begin
                    next_state = CHECK_HIT;
                end
            end
            
            CHECK_HIT: begin
                if (cache_hit_detected) begin
                    next_state = COMPLETE;
                end else begin
                    // Cache miss - check if victim needs writeback
                    if (line_valid && line_dirty) begin
                        next_state = WRITEBACK;
                    end else if (current_is_read) begin
                        next_state = ALLOCATE_READ;
                    end else begin
                        next_state = ALLOCATE_WRITE;
                    end
                end
            end
            
            WRITEBACK: begin
                if (mem_write_ready) begin
                    if (current_is_read) begin
                        next_state = ALLOCATE_READ;
                    end else begin
                        next_state = ALLOCATE_WRITE;
                    end
                end
            end
            
            ALLOCATE_READ: begin
                if (mem_read_ready) begin
                    next_state = COMPLETE;
                end
            end
            
            ALLOCATE_WRITE: begin
                if (mem_write_ready) begin
                    next_state = COMPLETE;
                end
            end
            
            COMPLETE: begin
                next_state = IDLE;
            end
        endcase
    end
    
    // LSU arbitration (round-robin within this core)
    always_ff @(posedge clk) begin
        if (reset) begin
            serving_lsu <= 0;
        end else if (state == IDLE) begin
            serving_lsu <= next_serving_lsu;
        end
    end
    
    // Find next LSU to serve
    always_comb begin
        next_serving_lsu = serving_lsu;
        
        // Round-robin through this core's LSUs
        for (int i = 1; i <= THREADS_PER_BLOCK; i++) begin
            logic [$clog2(THREADS_PER_BLOCK)-1:0] candidate;
            candidate = (serving_lsu + i) % THREADS_PER_BLOCK;
            if (lsu_read_valid[candidate] || lsu_write_valid[candidate]) begin
                next_serving_lsu = candidate;
                break;
            end
        end
        
        // If current LSU still has request, serve it
        if (lsu_read_valid[serving_lsu] || lsu_write_valid[serving_lsu]) begin
            next_serving_lsu = serving_lsu;
        end
    end
    
    // Capture current request details
    always_ff @(posedge clk) begin
        if (reset) begin
            current_is_read <= 0;
            current_addr <= 0;
            current_wdata <= 0;
        end else if (state == IDLE) begin
            if (lsu_read_valid[serving_lsu]) begin
                current_is_read <= 1;
                current_addr <= lsu_read_address[serving_lsu];
                current_wdata <= 0;
            end else if (lsu_write_valid[serving_lsu]) begin
                current_is_read <= 0;
                current_addr <= lsu_write_address[serving_lsu];
                current_wdata <= lsu_write_data[serving_lsu];
            end
        end
    end
    
    // Main cache control logic
    always_ff @(posedge clk) begin
        if (reset) begin
            // Initialize cache
            for (int i = 0; i < CACHE_SIZE; i++) begin
                cache_data[i] <= 0;
                cache_tags[i] <= 0;
                cache_valid[i] <= 0;
                cache_dirty[i] <= 0;
            end
            
            // Initialize LSU outputs
            for (int i = 0; i < THREADS_PER_BLOCK; i++) begin
                lsu_read_ready[i] <= 0;
                lsu_read_data[i] <= 0;
                lsu_write_ready[i] <= 0;
            end
            
            // Initialize memory outputs
            mem_read_valid <= 0;
            mem_read_address <= 0;
            mem_write_valid <= 0;
            mem_write_address <= 0;
            mem_write_data <= 0;
            
            victim_addr <= 0;
            victim_data <= 0;
            
        end else begin
            // Handle cache flush
            if (cache_flush) begin
                for (int i = 0; i < CACHE_SIZE; i++) begin
                    cache_valid[i] <= 0;
                    cache_dirty[i] <= 0;
                end
            end
            
            // Default values
            for (int i = 0; i < THREADS_PER_BLOCK; i++) begin
                lsu_read_ready[i] <= 0;
                lsu_write_ready[i] <= 0;
            end
            mem_read_valid <= 0;
            mem_write_valid <= 0;
            
            case (state)
                IDLE: begin
                    if (lsu_read_valid[serving_lsu] || lsu_write_valid[serving_lsu]) begin
                        // accessed
                    end
                end
                
                CHECK_HIT: begin
                    if (cache_hit_detected) begin
                        if (current_is_read) begin
                            // Read hit
                            lsu_read_data[serving_lsu] <= line_data;
                        end else begin
                            // Write hit - update cache
                            cache_data[addr_index] <= current_wdata;
                            cache_dirty[addr_index] <= 1; // Mark dirty for writeback
                        end
                    end else begin                        
                        // Save victim line if dirty
                        if (line_valid && line_dirty) begin
                            victim_addr <= {line_tag, addr_index};
                            victim_data <= line_data;
                        end
                    end
                end
                
                WRITEBACK: begin
                    // Write back dirty victim line
                    mem_write_valid <= 1;
                    mem_write_address <= victim_addr;
                    mem_write_data <= victim_data;
                end
                
                ALLOCATE_READ: begin
                    // Fetch from memory for read miss
                    mem_read_valid <= 1;
                    mem_read_address <= current_addr;
                    
                    if (mem_read_ready) begin
                        // Allocate cache line
                        cache_data[addr_index] <= mem_read_data;
                        cache_tags[addr_index] <= addr_tag;
                        cache_valid[addr_index] <= 1;
                        cache_dirty[addr_index] <= 0;
                        lsu_read_data[serving_lsu] <= mem_read_data;
                    end
                end
                
                ALLOCATE_WRITE: begin
                    // Write through to memory and allocate
                    mem_write_valid <= 1;
                    mem_write_address <= current_addr;
                    mem_write_data <= current_wdata;
                    
                    if (mem_write_ready) begin
                        // Allocate cache line
                        cache_data[addr_index] <= current_wdata;
                        cache_tags[addr_index] <= addr_tag;
                        cache_valid[addr_index] <= 1;
                        cache_dirty[addr_index] <= 0; // Clean since written through
                    end
                end
                
                COMPLETE: begin
                    // Signal completion to requesting LSU
                    if (current_is_read) begin
                        lsu_read_ready[serving_lsu] <= 1;
                    end else begin
                        lsu_write_ready[serving_lsu] <= 1;
                    end
                end
            endcase
        end
    end
    
    // Debug output
    `ifdef DEBUG
    always_ff @(posedge clk) begin
        if (state == CHECK_HIT) begin
            $display("Core Cache [LSU %0d]: addr=0x%02h, %s %s", 
                     serving_lsu, current_addr,
                     current_is_read ? "READ" : "WRITE",
                     cache_hit_detected ? "HIT" : "MISS");
        end
    end
    `endif

endmodule