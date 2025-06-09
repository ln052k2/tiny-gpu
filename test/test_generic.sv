`include "helpers/memory.sv"
`timescale 1ns/1ns

module test_generic;
    localparam DATA_MEM_ADDR_BITS     = 8;
    localparam DATA_MEM_DATA_BITS     = 8;
    localparam PROGRAM_MEM_ADDR_BITS  = 8;
    localparam PROGRAM_MEM_DATA_BITS  = 16;
    localparam DATA_MEM_CHANNELS      = 4;
    localparam PROGRAM_MEM_CHANNELS   = 1;
    localparam CORES                  = 2;
    localparam THREADS                = 8;
    int cycles;

    logic [DATA_MEM_DATA_BITS-1:0] expected, result;
    logic start, done, reset, clk;
    logic device_control_write_enable;
    logic [7:0] device_control_data;

    // Clock
    initial clk = 0;
    always #5 clk = ~clk;

    // Interfaces
    mem_if #(.ADDR_BITS(PROGRAM_MEM_ADDR_BITS), .DATA_BITS(PROGRAM_MEM_DATA_BITS), .CHANNELS(PROGRAM_MEM_CHANNELS)) program_mem_if();
    mem_if #(.ADDR_BITS(DATA_MEM_ADDR_BITS), .DATA_BITS(DATA_MEM_DATA_BITS), .CHANNELS(DATA_MEM_CHANNELS)) data_mem_if();

    // Memories
    Memory #(.ADDR_BITS(PROGRAM_MEM_ADDR_BITS), .DATA_BITS(PROGRAM_MEM_DATA_BITS), .CHANNELS(PROGRAM_MEM_CHANNELS)) program_memory;
    Memory #(.ADDR_BITS(DATA_MEM_ADDR_BITS), .DATA_BITS(DATA_MEM_DATA_BITS), .CHANNELS(DATA_MEM_CHANNELS)) data_memory;

    logic [PROGRAM_MEM_DATA_BITS-1:0] prog [0:6] = '{
        16'b0111000000010000,  // LDR R0, [R1]      ; load once to hit cache
        16'b0111000000010000,  // LDR R0, [R1]      ; same addr, expect cache hit
        16'b0111000000010000,  // LDR R0, [R1]      ; same addr, expect cache hit
        16'b1000000000000000,  // STR R0, [R1]      ; store back
        16'b0111000000010000,  // LDR R0, [R1]      ; reload, maybe still cached
        16'b1111000000000000,  // RET
        16'b0000000000000000   // padding
    };

    logic [DATA_MEM_DATA_BITS-1:0] data [0:15] = '{
        8'd42, 1, 2, 3, 4, 5, 6, 7,  // Memory A
        0, 1, 2, 3, 4, 5, 6, 7       // Memory B
    };

    gpu #(
        .DATA_MEM_ADDR_BITS(DATA_MEM_ADDR_BITS),
        .DATA_MEM_DATA_BITS(DATA_MEM_DATA_BITS),
        .DATA_MEM_NUM_CHANNELS(DATA_MEM_CHANNELS),
        .PROGRAM_MEM_ADDR_BITS(PROGRAM_MEM_ADDR_BITS),
        .PROGRAM_MEM_DATA_BITS(PROGRAM_MEM_DATA_BITS),
        .PROGRAM_MEM_NUM_CHANNELS(PROGRAM_MEM_CHANNELS),
        .NUM_CORES(CORES),
        .THREADS_PER_BLOCK(THREADS)
    ) dut (
        .clk(clk),
        .reset(reset),
        .start(start),
        .done(done),

        .device_control_write_enable(device_control_write_enable),
        .device_control_data(device_control_data),

        .program_mem_read_valid(program_mem_if.read_valid),
        .program_mem_read_address(program_mem_if.read_address),
        .program_mem_read_ready(program_mem_if.read_ready),
        .program_mem_read_data(program_mem_if.read_data),

        .data_mem_read_valid(data_mem_if.read_valid),
        .data_mem_read_address(data_mem_if.read_address),
        .data_mem_read_ready(data_mem_if.read_ready),
        .data_mem_read_data(data_mem_if.read_data),
        .data_mem_write_valid(data_mem_if.write_valid),
        .data_mem_write_address(data_mem_if.write_address),
        .data_mem_write_data(data_mem_if.write_data),
        .data_mem_write_ready(data_mem_if.write_ready)
    );

    // Debug hooks
    task print_mem_requests();
        for (int ch = 0; ch < DATA_MEM_CHANNELS; ch++) begin
            if (data_mem_if.read_valid[ch])
                $display("Cycle %0d | READ REQ  ch=%0d addr=%0d", cycles, ch, data_mem_if.read_address[ch]);
            if (data_mem_if.write_valid[ch])
                $display("Cycle %0d | WRITE REQ ch=%0d addr=%0d data=%0d", cycles, ch, data_mem_if.write_address[ch], data_mem_if.write_data[ch]);
        end
    endtask

    initial begin
        cycles = 0;
        reset = 1;
        @(posedge clk);
        reset = 0;

        program_memory = new("program", program_mem_if);
        data_memory    = new("data", data_mem_if);

        program_memory.load(prog);
        data_memory.load(data);

        device_control_data = THREADS;
        device_control_write_enable = 1;
        @(posedge clk);
        device_control_write_enable = 0;

        start = 1;
        @(posedge clk);

        while (!done) begin
            program_memory.run();
            data_memory.run();
            print_mem_requests();
            $display("Cycle %0d done=%b", cycles, done);
            cycles++;
            @(posedge clk);
        end

        $display("Completed in %0d cycles", cycles);
        data_memory.display(16);

        for (int i = 0; i < 1; i++) begin
            expected = data[i];  // 42
            result   = data_memory.memory[i];
            if (result !== expected)
                $fatal("Mismatch at index %0d: expected %0d, got %0d", i, expected, result);
        end

        $display("All results correct.");
        $finish;
    end
endmodule
