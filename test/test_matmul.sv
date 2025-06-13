`include "helpers/memory.sv"
// `include "helpers/setup.sv"
`timescale 1ns/1ns

module test_matmul;
    localparam DATA_MEM_ADDR_BITS     = 8;
    localparam DATA_MEM_DATA_BITS     = 8;
    localparam PROGRAM_MEM_ADDR_BITS  = 8;
    localparam PROGRAM_MEM_DATA_BITS  = 16;
    localparam DATA_MEM_CHANNELS      = 4;
    localparam PROGRAM_MEM_CHANNELS   = 1;
    localparam CORES                  = 2;
    localparam THREADS                = 8;
    int cycles;

    // Signals for DUT
    logic start, done, reset, clk;
    logic device_control_write_enable;
    logic [7:0] device_control_data;

    // Signals for expected results comparison
    logic [DATA_MEM_DATA_BITS-1:0] matrix_a [0:1][0:1];
    logic [DATA_MEM_DATA_BITS-1:0] matrix_b [0:1][0:1];
    logic [DATA_MEM_DATA_BITS*2-1:0] expected_results [0:3]; // Wider bit width to hold multiplication results
    logic [DATA_MEM_DATA_BITS*2-1:0] actual;
    
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
        
    logic [PROGRAM_MEM_DATA_BITS-1:0] prog [0:27] = '{
        16'b0101000011011110, // MUL R0, %blockIdx, %blockDim
        16'b0011000000001111, // ADD R0, R0, %threadIdx         ; i = blockIdx * blockDim + threadIdx
        16'b1001000100000001, // CONST R1, #1                   ; increment
        16'b1001001000000010, // CONST R2, #2                   ; N (matrix inner dimension)
        16'b1001001100000000, // CONST R3, #0                   ; baseA (matrix A base address)
        16'b1001010000000100, // CONST R4, #4                   ; baseB (matrix B base address)
        16'b1001010100001000, // CONST R5, #8                   ; baseC (matrix C base address)
        16'b0110011000000010, // DIV R6, R0, R2                 ; row = i // N
        16'b0101011101100010, // MUL R7, R6, R2
        16'b0100011100000111, // SUB R7, R0, R7                 ; col = i % N
        16'b1001100000000000, // CONST R8, #0                   ; acc = 0
        16'b1001100100000000, // CONST R9, #0                   ; k = 0
                            // LOOP:
        16'b0101101001100010, //   MUL R10, R6, R2
        16'b0011101010101001, //   ADD R10, R10, R9
        16'b0011101010100011, //   ADD R10, R10, R3             ; addr(A[i]) = row * N + k + baseA
        16'b0111101010100000, //   LDR R10, R10                 ; load A[i] from global memory
        16'b0101101110010010, //   MUL R11, R9, R2
        16'b0011101110110111, //   ADD R11, R11, R7
        16'b0011101110110100, //   ADD R11, R11, R4             ; addr(B[i]) = k * N + col + baseB
        16'b0111101110110000, //   LDR R11, R11                 ; load B[i] from global memory
        16'b0101110010101011, //   MUL R12, R10, R11
        16'b0011100010001100, //   ADD R8, R8, R12              ; acc = acc + A[i] * B[i]
        16'b0011100110010001, //   ADD R9, R9, R1               ; increment k
        16'b0010000010010010, //   CMP R9, R2
        16'b0001100000001100, //   BRn LOOP                     ; loop while k < N
        16'b0011100101010000, // ADD R9, R5, R0                 ; addr(C[i]) = baseC + i 
        16'b1000000010011000, // STR R9, R8                     ; store C[i] in global memory
        16'b1111000000000000  // RET                            ; end of kernel
    };

    // Data Memory
    Memory #(
        .ADDR_BITS(DATA_MEM_ADDR_BITS),
        .DATA_BITS(DATA_MEM_DATA_BITS),
        .CHANNELS(DATA_MEM_CHANNELS)
    ) data_memory;

    logic [DATA_MEM_DATA_BITS-1:0] data [0:7] = '{
        1, 2, 3, 4,   // Matrix A
        1, 2, 3, 4     // Matrix B
    };

    // Instantiate DUT
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

        while (done !== 1) begin
            program_memory.run();
            data_memory.run();
            // $display("Cycle %0d", cycles++);
            cycles++;
            @(posedge clk);
        end

        $display("Completed in %0d cycles", cycles);
        data_memory.display(24);

        // Check results
        // Fill matrix_a from data_memory
        matrix_a[0][0] = data_memory.memory[0];
        matrix_a[0][1] = data_memory.memory[1];
        matrix_a[1][0] = data_memory.memory[2];
        matrix_a[1][1] = data_memory.memory[3];

        // Fill matrix_b from data_memory
        matrix_b[0][0] = data_memory.memory[4];
        matrix_b[0][1] = data_memory.memory[5];
        matrix_b[1][0] = data_memory.memory[6];
        matrix_b[1][1] = data_memory.memory[7];

        // Compute expected_results
        expected_results[0] = matrix_a[0][0] * matrix_b[0][0] + matrix_a[0][1] * matrix_b[1][0]; // C[0][0]
        expected_results[1] = matrix_a[0][0] * matrix_b[0][1] + matrix_a[0][1] * matrix_b[1][1]; // C[0][1]
        expected_results[2] = matrix_a[1][0] * matrix_b[0][0] + matrix_a[1][1] * matrix_b[1][0]; // C[1][0]
        expected_results[3] = matrix_a[1][0] * matrix_b[0][1] + matrix_a[1][1] * matrix_b[1][1]; // C[1][1]

        for (int i = 0; i < 4; i++) begin
            actual = data_memory.memory[8 + i];
            if (actual !== expected_results[i]) begin
                $fatal("Result mismatch at index %0d: expected %0d, got %0d", i, expected_results[i], actual);
            end
        end
        $display("All results correct.");
        $finish;
    end

endmodule
