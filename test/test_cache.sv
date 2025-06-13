`timescale 1ns / 1ps

module cache_tb;
    // Test parameters - matching cache defaults
    parameter CACHE_SIZE = 16;
    parameter ADDR_BITS = 8;
    parameter DATA_BITS = 8;
    parameter THREADS_PER_BLOCK = 4;
    parameter TAG_BITS = 4;
    parameter INDEX_BITS = 4;
    
    // Clock and reset
    logic clk;
    logic reset;
    
    // LSU interface signals
    logic [THREADS_PER_BLOCK-1:0] lsu_read_valid;
    logic [ADDR_BITS-1:0] lsu_read_address [THREADS_PER_BLOCK-1:0];
    logic [THREADS_PER_BLOCK-1:0] lsu_read_ready;
    logic [DATA_BITS-1:0] lsu_read_data [THREADS_PER_BLOCK-1:0];
    logic [THREADS_PER_BLOCK-1:0] lsu_write_valid;
    logic [ADDR_BITS-1:0] lsu_write_address [THREADS_PER_BLOCK-1:0];
    logic [DATA_BITS-1:0] lsu_write_data [THREADS_PER_BLOCK-1:0];
    logic [THREADS_PER_BLOCK-1:0] lsu_write_ready;
    
    // Memory interface signals
    logic mem_read_valid;
    logic [ADDR_BITS-1:0] mem_read_address;
    logic mem_read_ready;
    logic [DATA_BITS-1:0] mem_read_data;
    logic mem_write_valid;
    logic [ADDR_BITS-1:0] mem_write_address;
    logic [DATA_BITS-1:0] mem_write_data;
    logic mem_write_ready;
    
    // Cache control
    logic cache_flush;
    
    // Simple memory array for testing
    logic [DATA_BITS-1:0] test_memory [0:255];
    
    // DUT instantiation
    cache #(
        .CACHE_SIZE(CACHE_SIZE),
        .ADDR_BITS(ADDR_BITS),
        .DATA_BITS(DATA_BITS),
        .THREADS_PER_BLOCK(THREADS_PER_BLOCK),
        .TAG_BITS(TAG_BITS),
        .INDEX_BITS(INDEX_BITS)
    ) dut (
        .clk(clk),
        .reset(reset),
        .lsu_read_valid(lsu_read_valid),
        .lsu_read_address(lsu_read_address),
        .lsu_read_ready(lsu_read_ready),
        .lsu_read_data(lsu_read_data),
        .lsu_write_valid(lsu_write_valid),
        .lsu_write_address(lsu_write_address),
        .lsu_write_data(lsu_write_data),
        .lsu_write_ready(lsu_write_ready),
        .mem_read_valid(mem_read_valid),
        .mem_read_address(mem_read_address),
        .mem_read_ready(mem_read_ready),
        .mem_read_data(mem_read_data),
        .mem_write_valid(mem_write_valid),
        .mem_write_address(mem_write_address),
        .mem_write_data(mem_write_data),
        .mem_write_ready(mem_write_ready),
        .cache_flush(cache_flush)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 100MHz clock
    end
    
    // Simple memory model
    always_ff @(posedge clk) begin
        if (reset) begin
            mem_read_ready <= 0;
            mem_write_ready <= 0;
            mem_read_data <= 0;
            // Initialize test memory with pattern
            for (int i = 0; i < 256; i++) begin
                test_memory[i] <= i + 8'h50;
            end
        end else begin
            // Handle memory reads
            if (mem_read_valid && !mem_read_ready) begin
                mem_read_data <= test_memory[mem_read_address];
                mem_read_ready <= 1;
                $display("Memory Read: addr=0x%02h, data=0x%02h", mem_read_address, test_memory[mem_read_address]);
            end else begin
                mem_read_ready <= 0;
            end
            
            // Handle memory writes
            if (mem_write_valid && !mem_write_ready) begin
                test_memory[mem_write_address] <= mem_write_data;
                mem_write_ready <= 1;
                $display("Memory Write: addr=0x%02h, data=0x%02h", mem_write_address, mem_write_data);
            end else begin
                mem_write_ready <= 0;
            end
        end
    end
    
    // Test variables
    int test_count = 0;
    int pass_count = 0;
    
    // Test helper tasks
    task reset_system();
        reset = 1;
        cache_flush = 0;
        lsu_read_valid = '0;
        lsu_write_valid = '0;
        for (int i = 0; i < THREADS_PER_BLOCK; i++) begin
            lsu_read_address[i] = '0;
            lsu_write_address[i] = '0;
            lsu_write_data[i] = '0;
        end
        
        repeat (3) @(posedge clk);
        reset = 0;
        repeat (2) @(posedge clk);
    endtask
    
    task lsu_read(input int lsu_id, input logic [ADDR_BITS-1:0] addr, output logic [DATA_BITS-1:0] data);
        $display("Starting LSU%0d read from addr=0x%02h", lsu_id, addr);
        
        // Start read request
        lsu_read_valid[lsu_id] = 1;
        lsu_read_address[lsu_id] = addr;
        
        // Wait for ready
        while (!lsu_read_ready[lsu_id]) begin
            @(posedge clk);
        end
        
        data = lsu_read_data[lsu_id];
        lsu_read_valid[lsu_id] = 0;
        
        $display("LSU%0d read complete: addr=0x%02h, data=0x%02h", lsu_id, addr, data);
        @(posedge clk);
    endtask
    
    task lsu_write(input int lsu_id, input logic [ADDR_BITS-1:0] addr, input logic [DATA_BITS-1:0] data);
        $display("Starting LSU%0d write to addr=0x%02h, data=0x%02h", lsu_id, addr, data);
        
        // Start write request
        lsu_write_valid[lsu_id] = 1;
        lsu_write_address[lsu_id] = addr;
        lsu_write_data[lsu_id] = data;
        
        // Wait for ready
        while (!lsu_write_ready[lsu_id]) begin
            @(posedge clk);
        end
        
        lsu_write_valid[lsu_id] = 0;
        
        $display("LSU%0d write complete: addr=0x%02h, data=0x%02h", lsu_id, addr, data);
        @(posedge clk);
    endtask
    
    task check_result(input string test_name, input logic [DATA_BITS-1:0] expected, input logic [DATA_BITS-1:0] actual);
        test_count++;
        if (expected == actual) begin
            $display("PASS: %s - Expected: 0x%02h, Got: 0x%02h", test_name, expected, actual);
            pass_count++;
        end else begin
            $display("FAIL: %s - Expected: 0x%02h, Got: 0x%02h", test_name, expected, actual);
        end
    endtask
    
    // Main test sequence
    initial begin
        $display("========================================");
        $display("Starting Simple Cache Testbench");
        $display("========================================");
        
        reset_system();
        
        // Test 1: Simple read miss (should fetch from memory)
        begin
            logic [DATA_BITS-1:0] read_data;
            $display("\n--- Test 1: Read Miss ---");
            lsu_read(0, 8'h10, read_data);
            check_result("Read Miss", 8'h60, read_data); // 0x10 + 0x50 = 0x60
        end
        
        // Test 2: Read hit (same address)
        begin
            logic [DATA_BITS-1:0] read_data;
            $display("\n--- Test 2: Read Hit ---");
            lsu_read(0, 8'h10, read_data);
            check_result("Read Hit", 8'h60, read_data);
        end
        
        // Test 3: Write miss (should write through and allocate)
        begin
            $display("\n--- Test 3: Write Miss ---");
            lsu_write(0, 8'h20, 8'hAB);
            // Verify write went to memory
            if (test_memory[8'h20] == 8'hAB) begin
                $display("PASS: Write Miss - Data written to memory");
                pass_count++;
            end else begin
                $display("FAIL: Write Miss - Data not written to memory (got 0x%02h)", test_memory[8'h20]);
            end
            test_count++;
        end
        
        // Test 4: Write hit (should update cache and mark dirty)
        begin
            logic [DATA_BITS-1:0] read_data;
            $display("\n--- Test 4: Write Hit ---");
            lsu_write(0, 8'h10, 8'hCD); // Same address as test 1&2
            lsu_read(0, 8'h10, read_data);
            check_result("Write Hit", 8'hCD, read_data);
        end
        
        // Test 5: Different LSU access
        begin
            logic [DATA_BITS-1:0] read_data;
            $display("\n--- Test 5: Different LSU Access ---");
            lsu_read(1, 8'h30, read_data);
            check_result("LSU1 Read", 8'h80, read_data); // 0x30 + 0x50 = 0x80
        end
        
        // Test 6: Write from different LSU
        begin
            $display("\n--- Test 6: Write from Different LSU ---");
            lsu_write(2, 8'h40, 8'hEF);
            if (test_memory[8'h40] == 8'hEF) begin
                $display("PASS: LSU2 Write - Data written to memory");
                pass_count++;
            end else begin
                $display("FAIL: LSU2 Write - Data not written to memory");
            end
            test_count++;
        end
        
        // Test 7: Cache flush
        begin
            logic [DATA_BITS-1:0] read_data;
            $display("\n--- Test 7: Cache Flush ---");
            
            // Write some data to cache (creating dirty line)
            lsu_write(0, 8'h50, 8'h55);
            
            // Flush cache
            cache_flush = 1;
            @(posedge clk);
            cache_flush = 0;
            @(posedge clk);
            
            // Read should now miss and fetch from memory
            lsu_read(0, 8'h50, read_data);
            check_result("Post-Flush Read", 8'hA0, read_data); // 0x50 + 0x50 = 0xA0
        end
        
        // Test 8: Fill up cache to test eviction
        begin
            logic [DATA_BITS-1:0] read_data;
            $display("\n--- Test 8: Cache Line Eviction ---");
            
            // Write to many different cache lines to force eviction
            for (int i = 0; i < CACHE_SIZE + 4; i++) begin
                lsu_write(0, i*16, 8'hF0 + i); // Use addresses that map to different cache lines
            end
            
            // Read back first address (should be evicted and refetched from memory)
            lsu_read(0, 8'h00, read_data);
            check_result("Eviction Test", 8'h50, read_data); // Original memory value: 0x00 + 0x50
        end
        
        // Allow some time for final operations
        repeat (10) @(posedge clk);
        
        // Final results
        $display("\n========================================");
        $display("Test Results: %0d/%0d tests passed", pass_count, test_count);
        if (pass_count == test_count) begin
            $display("ALL TESTS PASSED!");
        end else begin
            $display("SOME TESTS FAILED!");
        end
        $display("========================================");
        
        $finish;
    end
    
    // Timeout watchdog
    initial begin
        #50000; // 50us timeout
        $display("ERROR: Test timeout!");
        $finish;
    end
    
    // Optional: Dump waveforms
    initial begin
        $dumpfile("cache_tb.vcd");
        $dumpvars(0, dut);
    end
    
endmodule