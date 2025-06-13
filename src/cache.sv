module cache #(
    parameter ADDR_BITS = 8,
    parameter DATA_BITS = 8,
    parameter CONSUMERS = 4,
    parameter SETS = 4,
    parameter WAYS = 4,
    parameter WORDS_PER_LINE = 1,
    parameter ARBITRATOR = "rr",
    parameter REPLACEMENT_POLICY = "rr",
    parameter WRITE_THROUGH_POLICY = 0, // default - write-back
    parameter WRITE_ALLOCATE_POLICY = 1
)(
    input wire clk,
    input wire reset,

    memory_if.consumer consumer_if,

    // To Global Memory
    mem_if.mem memory_if
);

import cache_state_pkg::*;

localparam OFFSET_BITS = $clog2(WORDS_PER_LINE);
localparam SET_BITS = $clog2(SETS);
localparam TAG_BITS = ADDR_BITS - SET_BITS - OFFSET_BITS;
localparam CACHE_LINES = SETS * WAYS;

typedef struct packed {
    bit valid;
    bit dirty;
    logic [TAG_BITS-1:0] tag;
    logic [DATA_BITS-1:0] data;
} cache_line_t;

// create the actual cache store
cache_line_t cache [SETS][WAYS];

// persistent store address and type
bit read_op;
logic [ADDR_BITS-1:0] addr_raw;

// break down address into components

typedef struct packed {
    logic [TAG_BITS-1:0] tag,
    logic [(SET_BITS?SET_BITS:1)-1:0] set,
    logic [(OFFSET_BITS?OFFSET_BITS:1)-1:0] offset
} addr_components_t;

function addr_components_t breakdown(input logic [ADDR_BITS-1:0] addr);
begin
    if (OFFSET_BITS > 0)
        result.offset = addr[OFFSET_BITS-1:0];
    else
        result.offset = '0;

    if (SET_BITS > 0)
        result.set = addr[OFFSET_BITS +: SET_BITS];
    else
        result.set = '0;

    result.tag = addr[ADDR_BITS-1 -: TAG_BITS];

    return result;
end
endfunction

addr_components_t addr_components;
assign addr_components = breakdown(addr_raw);

// generate arbiter based on parameters
// this allows the arbiter itself to be swapped out easily

wire [$clog2(CONSUMERS)-1] grant_idx;
logic [$clog2(CONSUMERS) -1]  grant_idx_reg;
wire [CONSUMERS-1:0] requests_vec = (consumer_if.read_valid|consumer_if.write_valid);

bit must_evict;
wire [$clog2(WAYS)-1:0] victim_way;
generate
    // ensure cache parameters are valid
    if(ADDR_BITS <= (SET_BITS+OFFSET_BITS))
        initial $fatal("Invalid cache dimensions");

    // if we have multiple channels - instantiate an arbiter to decide who gets the grant
    // this is an index, not a vector, because each channel is an unpacked array
    if(CONSUMERS>1) begin
        case (ARBITRATOR)
        "rr":
            round_robin_arbiter #(.N(CONSUMERS)) rra(
                .requests(requests_vec),
                .grants(grant_idx), 
                .active(state==IDLE),
                .clk(clk), 
                .reset(reset),
            );
        default: initial $fatal("Invalid arbitrator");
        endcase
    end else begin
        // single channel - no arbitration required
        assign grant_idx = 1'b0;
    end

    case (REPLACEMENT_POLICY)
        "rr":
            round_robin_replacement #(.SETS(SETS),.WAYS(WAYS)) rrr(
                .clk(clk),
                .reset(reset),
                .set_idx(addr_components.set),
                .evict_req(must_evict),
                .victim_way(victim_way)
            );
        /*"lru":
            lru_replacement #(.SETS(SETS),.WAYS(WAYS)) lru(
                // not implemented
            );*/
        default: initial $fatal("Invalid eviction policy");
    endcase

endgenerate

/*
typedef enum {
    IDLE, 
    LOOKUP,
    HIT,
    ALLOCATE,
    WRITE, 
    READY
} cache_state_e;
(note: moved to pkg)
*/
cache_state_e state, then_state;
bit hit;
logic [$clog2(WAYS)-1:0] hit_way;
// temporary data register, for writing to memory
logic [DATA_BITS-1:0] tmp_data;

// determine if there is a free spot in the current way
wire [$clog2(WAYS)-1:0] write_way;
always_comb begin
    bit evict = '1;
    write_way = '0;
    for (logic [$clog2(WAYS)-1:0] w=0; w<WAYS; w++) begin
        if(!cache[addr_components.set][w].valid) begin
            evict = 0;
            write_way = w;
        end
    end
    if (evict) begin
        // tell replacement unit to find replacement if we missed
        must_evict = (state == MISS) & evict;
        write_way = victim_way;
    end else begin
        must_evict = 0;
    end
end
// control FSM
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        // clear
        for (int i=0; i<SETS; i++)
            for (int j=0; j<WAYS; j++)
                cache[i][j] <= '{valid:0, dirty:0, tag:'0, data:'0};
        state <= IDLE;
        read_op <= 0;
        addr_raw <= '0;
        hit<=0;
        // tell all consumers we've reset
        for (int i = 0; i < CONSUMERS; i++) begin
            consumer_if.read_ready[i] <= 0;
            consumer_if.write_ready[i] <= 0;
        end
        memory_if.read_valid[0]  <= 0;
        memory_if.write_valid[0] <= 0;
    end else begin

        case (state)
            IDLE: begin
                consumer_if.read_ready[grant_idx_reg] <= 0;
                consumer_if.write_ready[grant_idx_reg] <= 0;
                memory_if.read_valid[0] <= 0;
                memory_if.write_valid[0] <= 0;
                if (requests_vec != 0) begin
                    // skip arbitration
                    if(CONSUMERS==1) begin
                        hit<=0;
                        state <= LOOKUP;
                        addr_raw <= consumer_if.addr[0];
                        read_op <= consumer_if.read_valid[0];
                    end else begin
                        state <= WAIT_ARBITRATION;
                    end
                end
            end

            WAIT_ARBITRATION: begin
                addr_raw <= consumer_if.addr[grant_idx];
                // since we know read_valid | write_valid was asserted, this is fine
                read_op <= consumer_if.read_valid[grant_idx]; 
                grant_idx_reg <= grant_idx;
                state <= LOOKUP;
            end

            LOOKUP: begin
                // default: miss
                state <= MISS;
                // look up tag
                for (int w = 0; w < WAYS; w++) begin
                    if (cache[addr_components.set][w].valid &&
                        cache[addr_components.set][w].tag == addr_components.tag) begin
                        //CACHE HIT!
                        state <= HIT;
                        hit_way <= w;
                    end
                end
            end
            
            // happy path first!
            HIT: begin
                hit<=1;
                state <= READY;
                if (read_op) begin
                    // return requested data
                    consumer_if.read_data[grant_idx_reg] <= cache[addr_components.set][hit_way].data;
                end else begin
                    cache[addr_components.set][hit_way].data <= consumer_if.write_data[grant_idx_reg];
                    // write if write-through mode
                    if(WRITE_THROUGH_POLICY) begin
                        tmp_data <= consumer_if.write_data[grant_idx_reg];
                        state <= WRITE_MEM;
                        // a 'callback', of sorts.
                        then_state <= READY;
                    end else begin
                        cache[addr_components.set][hit_way].dirty <= 1;
                    end
                end
            end

            MISS: begin
                // if we're writing and we're not a write-allocate cache - who cares?
                if (!read_op && !WRITE_ALLOCATE_POLICY) begin
                    tmp_data <= consumer_if.write_data[grant_idx_reg];
                    state <= WRITE_MEM;
                    then_state <= READY;
                end else if(read_op) begin
                    state <= REFILL_CACHE;
                    then_state <= HIT;
                end else begin
                    // write-allocate
                    state <= WRITE_ALLOCATE;
                end
                

            end
/*          buggy;disabled
            WRITE_ALLOCATE: begin
                cache[addr_components.set][write_way].tag <= addr_components.tag;
                cache[addr_components.set][write_way].dirty <= 1;
                cache[addr_components.set][write_way].data <= memory_if.read_data[0];
                if(WRITE_THROUGH_POLICY) begin
                    // write to memory before we finish
                    // but cache line is valid!
                    cache[addr_components.set][write_way].dirty <= 0;
                    state <= WRITE_MEM;
                    then_state <= READY;
                end else begin
                    // no need to write to memory
                    cache[addr_components.set][write_way].dirty <= 1;
                    state <= READY;
                end
            end
*/

            WRITE_MEM: begin
                memory_if.write_valid[0] <= '1;
                memory_if.write_data[0] <= tmp_data;
                if(hit)
                    // if writing through a hit, write to the requested location
                    memory_if.write_addr[0] <= addr_raw;
                else
                    if(SETS>1)
                        memory_if.write_addr[0] <= {cache[addr_components.set][write_way].tag,addr_components.set} << OFFSET_BITS;
                    else 
                        memory_if.write_addr[0] <= {cache[addr_components.set][write_way].tag} << OFFSET_BITS;
                state <= WRITE_MEM; // stay until memory ready
                if(memory_if.write_ready[0]) begin
                    memory_if.write_valid[0] <= '0;
                    tmp_data <= consumer_if.write_data[grant_idx];
                    state <= then_state;
                end
                    
            end

            REFILL_CACHE: begin
                // request data from memory
                memory_if.read_valid[0] <= 1;
                memory_if.read_addr[0] <= addr_raw;
                state <= REFILL_CACHE; // stay until memory ready
                if (memory_if.read_ready[0]) begin
                    if (read_op)
                        cache[addr_components.set][write_way].data <= memory_if.read_data[0];
                    else
                        cache[addr_components.set][write_way].data <= memory_if.write_data[0];
                    memory_if.read_valid[0] <= 0;
                    // if dirty, and write back - write back
                    if(cache[addr_components.set][write_way].dirty && must_evict) begin
                        state <= WRITE_MEM;
                        then_state <= READY;
                        tmp_data <= cache[addr_components.set][write_way].data;
                    end
                    else
                        state <= READY;

                    cache[addr_components.set][write_way].tag <= addr_components.tag;
                    cache[addr_components.set][write_way].valid <= 1;
                    cache[addr_components.set][write_way].dirty <= 0;
                end
            end

            READY: begin
                // completed transaction, go idle
                if(read_op)
                    consumer_if.read_ready[grant_idx_reg] <= 1;
                else
                    consumer_if.write_ready[grant_idx_reg] <= 1;
                state <= IDLE;
            end

            default: state <= IDLE;
        endcase
    end
end




endmodule