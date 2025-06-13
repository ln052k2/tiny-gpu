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
    localparam PROGRAM_LENGTH         = 32;
    int cycles;

    logic [DATA_MEM_DATA_BITS-1:0] expected, result;
    logic start, done, reset, clk;
    logic device_control_write_enable;
    logic [7:0] device_control_data;

    // Clock
    initial clk = 0;
    always #5 clk = ~clk;

    // Interfaces    // Instantiate memory interfaces
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

    // Memories    
    Memory program_memory;
    Memory data_memory;

    logic [15:0] prog [0:PROGRAM_LENGTH-1] = '{default:0};
    logic [DATA_MEM_DATA_BITS-1:0] data [0:15] = '{default: 0};

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

    // Debug hooks
    task print_mem_requests();
        for (int ch = 0; ch < DATA_MEM_CHANNELS; ch++) begin
            if (data_mem_if.read_valid[ch])
                $display("Cycle %0d | READ REQ  ch=%0d addr=%0d", cycles, ch, data_mem_if.read_address[ch]);
            if (data_mem_if.write_valid[ch])
                $display("Cycle %0d | WRITE REQ ch=%0d addr=%0d data=%0d", cycles, ch, data_mem_if.write_address[ch], data_mem_if.write_data[ch]);
        end
    endtask

    import instruction_pkg::*;
    instr_fields_t instr;
    InstrCoverage coverage;

    initial begin
        program_memory = new("program", program_mem_if);
        data_memory    = new("data", data_mem_if);
        
        instr = new();
        coverage = new();
        // Fill program memory with randomized instructions
        for (int i = 0; i < PROGRAM_LENGTH; i++) begin
            // Randomize fields and get encoded instruction
            prog[i] = instr.generate_instr();
            coverage.sample(instr);

            instr.print_instr();
            $display("Encoded prog[%0d] = %h", i, prog[i]);
        end

        $display();

        cycles = 0;
        reset = 1;
        @(posedge clk);
        reset = 0;

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

        coverage.print_coverage();

        $finish;
    end
endmodule
