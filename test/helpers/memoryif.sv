interface mem_if #(
    parameter int ADDR_BITS = 8,
    parameter int DATA_BITS = 16,
    parameter int CHANNELS  = 1
);
    logic [CHANNELS-1:0]         read_valid;
    logic [ADDR_BITS-1:0]        read_address [CHANNELS];
    logic [DATA_BITS-1:0]        read_data    [CHANNELS];
    logic [CHANNELS-1:0]         read_ready;

    logic [CHANNELS-1:0]         write_valid;
    logic [ADDR_BITS-1:0]        write_address [CHANNELS];
    logic [DATA_BITS-1:0]        write_data    [CHANNELS];
    logic [CHANNELS-1:0]         write_ready;

    modport ro (
        input  read_valid, read_address,
        output read_data, read_ready
    );

    modport rw (
        input  read_valid, read_address,
               write_valid, write_address, write_data,
        output read_data, read_ready, write_ready
    );
endinterface