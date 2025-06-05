// DUT Signals
// Memory read signals
// - Read valid
// - Read ready
// - Read address
// - Read data

// Memory write signals
// - Write valid
// - Write ready
// - Write address
// - Write data

// Memory class
class Memory #(parameter int ADDR_BITS = 8, 
                parameter int DATA_BITS = 16, 
                parameter int CHANNELS = 1);

string name;

logic [CHANNELS-1:0] mem_read_valid;
logic [ADDR_BITS-1:0] mem_read_address [CHANNELS];
logic [DATA_BITS-1:0] mem_read_data [CHANNELS];
logic [CHANNELS-1:0] mem_read_ready;

logic [CHANNELS-1:0] mem_write_valid;
logic [ADDR_BITS-1:0] mem_write_address [CHANNELS];
logic [DATA_BITS-1:0] mem_write_data [CHANNELS];
logic [CHANNELS-1:0] mem_write_ready;

typedef logic [ADDR_BITS-1:0] addr_t;
typedef logic [DATA_BITS-1:0] data_t;
data_t memory [0:2**ADDR_BITS-1];

function new(string name__);
    this.name = name__;
    // Initialize memory to zero
    foreach (memory[i]) memory[i] = '0;
endfunction

// Run function:
// Run function:
task run();
    data_t read_data[CHANNELS];
    bit read_ready[CHANNELS];
    bit write_ready[CHANNELS];

    // READ logic
    for (int i = 0; i < CHANNELS; i++) begin
        if (mem_read_valid[i]) begin
            read_data[i]  = memory[mem_read_address[i]];
            read_ready[i] = 1;
        end else begin
            read_data[i]  = '0;
            read_ready[i] = 0;
        end
        mem_read_data[i]  = read_data[i];
        mem_read_ready[i] = read_ready[i];
    end

    // WRITE logic
    for (int i = 0; i < CHANNELS; i++) begin
        if (mem_write_valid[i]) begin
            memory[mem_write_address[i]] = mem_write_data[i];
            write_ready[i] = 1;
        end else begin
            write_ready[i] = 0;
        end
        mem_write_ready[i] = write_ready[i];
    end
endtask


// Write function (bypasses the run function)
function void write(addr_t address, data_t data);
    if (address < (1 << ADDR_BITS)) begin
        memory[address] = data;
    end
endfunction

// Load function
task load(input data_t data[]);
    foreach (data[i]) begin
        memory[i] = data[i];
    end
endtask

// Display function:
// TODO: revisit after logger function is implemented
// Displays memory contents in a readable format
task display(int rows = 16);
    $display("\n=== %s MEMORY DUMP ===", name);
    for (int i = 0; i < rows; i++) begin
        $display("Addr %0d: 0x%0h", i, memory[i]);
    end
    $display("========================\n");
endtask
endclass