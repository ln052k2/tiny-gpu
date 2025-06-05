class Memory #(
    parameter int ADDR_BITS = 8,
    parameter int DATA_BITS = 16,
    parameter int CHANNELS  = 1
);
    string name;

    typedef logic [ADDR_BITS-1:0] addr_t;
    typedef logic [DATA_BITS-1:0] data_t;
    data_t memory [0:2**ADDR_BITS-1];

    // This must match the declared port name exactly
    virtual mem_if #(
        .ADDR_BITS(ADDR_BITS),
        .DATA_BITS(DATA_BITS),
        .CHANNELS(CHANNELS)
    ) mem;

    // Constructor
    function new(string name__, virtual mem_if #(
        .ADDR_BITS(ADDR_BITS),
        .DATA_BITS(DATA_BITS),
        .CHANNELS(CHANNELS)
    ) mem__);
        this.name = name__;
        this.mem  = mem__;

        // Initialize memory contents to zero
        foreach (memory[i]) memory[i] = '0;
    endfunction

    // Simulates one clock cycle of memory activity
    task run();
        for (int i = 0; i < CHANNELS; i++) begin
            // READ handling (pulse read_ready)
            if (mem.read_valid[i] && !mem.read_ready[i]) begin
                mem.read_data[i]  = memory[mem.read_address[i]];
                mem.read_ready[i] = 1;
                $display("[%s] Read ch%0d addr=%0d -> data=%0d",
                        name, i, mem.read_address[i], mem.read_data[i]);
            end else begin
                mem.read_ready[i] = 0; // Deassert after one cycle
            end

            // WRITE handling (pulse write_ready)
            if (mem.write_valid[i] && !mem.write_ready[i]) begin
                memory[mem.write_address[i]] = mem.write_data[i];
                mem.write_ready[i] = 1;
                $display("[%s] Write ch%0d addr=%0d <- data=%0d",
                        name, i, mem.write_address[i], mem.write_data[i]);
            end else begin
                mem.write_ready[i] = 0; // Deassert after one cycle
            end
        end
    endtask


    // Manual memory write (bypasses interface)
    task write(addr_t address, data_t data);
        if (address < (1 << ADDR_BITS)) begin
            memory[address] = data;
        end
    endtask

    // Load memory with an array
    task load(input data_t data[]);
        foreach (data[i]) memory[i] = data[i];
    endtask

    // Display memory contents
    task display(int rows = 16);
        $display("\n=== %s MEMORY DUMP ===", name);
        for (int i = 0; i < rows; i++) begin
            $display("Addr %0d: 0x%0h", i, memory[i]);
        end
        $display("========================\n");
    endtask
endclass

