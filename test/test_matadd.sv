`include "helpers/memory.sv"
// `include "helpers/setup.sv"
`timescale 1ns/1ns

module test_matadd;
    localparam DATA_MEM_ADDR_BITS     = 8;
    localparam DATA_MEM_DATA_BITS     = 8;
    localparam PROGRAM_MEM_ADDR_BITS  = 8;
    localparam PROGRAM_MEM_DATA_BITS  = 16;
    localparam DATA_MEM_CHANNELS      = 4;
    localparam PROGRAM_MEM_CHANNELS   = 1;
    localparam CORES                  = 2;
    localparam THREADS                = 8;
    int cycles;

    // Signals for expected results comparison
    logic [DATA_MEM_DATA_BITS-1:0] expected, result;

    // Signals for DUT
    logic start, done, reset, clk;
    logic device_control_write_enable;
    logic [7:0] device_control_data;

    // Clock generation
    initial clk = 0;
    always #25000 clk = ~clk;

    // Instantiate memory interfaces
    mem_if #(
        .ADDR_BITS(PROGRAM_MEM_ADDR_BITS),
        .DATA_BITS(PROGRAM_MEM_DATA_BITS),
        .CHANNELS(PROGRAM_MEM_CHANNELS)
    ) program_mem_if();

    mem_if #(
        .ADDR_BITS(DATA_MEM_ADDR_BITS),
        .DATA_BITS(DATA_MEM_DATA_BITS),
        .CHANNELS(DATA_MEM_CHANNELS)
    ) data_mem_if();


    // Program Memory
    Memory #(
        .ADDR_BITS(PROGRAM_MEM_ADDR_BITS),
        .DATA_BITS(PROGRAM_MEM_DATA_BITS),
        .CHANNELS(PROGRAM_MEM_CHANNELS)
    ) program_memory;

    logic [PROGRAM_MEM_DATA_BITS-1:0] prog [0:12] = '{
        16'b0101000011011110,
        16'b0011000000001111,
        16'b1001000100000000,
        16'b1001001000001000,
        16'b1001001100010000,
        16'b0011010000010000,
        16'b0111010001000000,
        16'b0011010100100000,
        16'b0111010101010000,
        16'b0011011001000101,
        16'b0011011100110000,
        16'b1000000001110110,
        16'b1111000000000000
    };

    // Data Memory
    Memory #(
        .ADDR_BITS(DATA_MEM_ADDR_BITS),
        .DATA_BITS(DATA_MEM_DATA_BITS),
        .CHANNELS(DATA_MEM_CHANNELS)
    ) data_memory;

    logic [DATA_MEM_DATA_BITS-1:0] data [0:15] = '{
        0, 1, 2, 3, 4, 5, 6, 7,    // Matrix A
        0, 1, 2, 3, 4, 5, 6, 7     // Matrix B
    };

    
    // Instantiate DUT
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

        // Program memory hookup via interface
        .program_mem_if(program_mem_if),

        // Data memory hookup via interface
        .data_mem_if(data_mem_if)
    );

    // always @(posedge clk) begin
 	// $display("T=%0t | reset=%b start=%b done=%b", $time, reset, start, done);
    // 	$display("T=%0t | reset=%b start=%b done=%b | ctrl_we=%b ctrl_data=%0d", 
    //           $time, reset, start, done, device_control_write_enable, device_control_data);
    // end

    initial begin
        cycles = 0;
        // Setup and reset
        reset = 1;
        @(posedge clk);
        reset = 0;

        // // Construct memories
        // program_memory = new("program");
        // data_memory    = new("data");

        // Hook interface signals to class instances
        program_memory = new("program", program_mem_if);

        data_memory = new("data", data_mem_if);

        // Load program and data memory
        program_memory.load(prog);
        data_memory.load(data);

        // Write number of threads to register via device control
        device_control_data = THREADS;
        device_control_write_enable = 1'b1;
        @(posedge clk);
        device_control_write_enable = 1'b0;

        // Start DUT
        start = 1'b1;
        @(posedge clk);
        // start = 1'b0;

        while (done !== 1) begin
            program_memory.run();
            data_memory.run();
            $display("Cycle %0d", cycles++);
            @(posedge clk);
        end

        $display("Completed in %0d cycles", cycles);
        data_memory.display(24);

        // Validate results
        for (int i = 0; i < 8; i++) begin
            expected = data[i] + data[i + 8];
            result   = data_memory.memory[i + 16];
            if (result !== expected) begin
                $fatal("Mismatch at index %0d: expected %0d, got %0d", i, expected, result);
            end
        end

        $display("All results correct.");
        $finish;
    end
endmodule
