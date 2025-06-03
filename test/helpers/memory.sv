// Memory class for testing
// Consists of attributes:
// - DUT
// - Address bits (parameter)
// - Data bits (parameter)
// - Memory size (based on address bits)
// - Channels (parameter)
// - Name
class Memory;
    typedef bit [ADDR_BITS-1:0] addr_t;
    typedef bit [DATA_BITS-1:0] data_t;

    // Parameters
    int unsigned ADDR_BITS;
    int unsigned DATA_BITS;
    int unsigned CHANNELS;
    string NAME;

    data_t mem[];
       
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

    // Constructor
    function new(int unsigned addr_bits, int unsigned data_bits, int unsigned channels, string name);
        ADDR_BITS = addr_bits;
        DATA_BITS = data_bits;
        CHANNELS = channels;
        NAME = name;

        // Calculate memory size based on address bits
        int unsigned mem_size = 1 << ADDR_BITS;
        mem = new[CHANNELS][mem_size];
    endfunction

// Run function:
// Parse read valid bits (converts each bit to an integer)
// Parse read address bits (converts each bit to an integer)
// Read ready and read data are both initialized to 0
// For each channel, if the read valid bit is 1, read data from the given memory read address. Else, set read ready to 0;
// Combine read data from all channels into a single read data signal
// Combine read ready from all channels into a single read ready signal
// If non-program memory:
    // Parse write valid, address and data for each channel.
    // If write valid is 1, write data to the given memory address. Else, set write ready to 0;
    // Combine write ready from all channels into a single write ready signal

// Write function (bypasses the run function)
// Load function

// Display function:
// TODO: revisit after logger function is implemented
// Displays memory contents in a readable format