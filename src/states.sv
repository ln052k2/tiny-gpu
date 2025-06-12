package states_pkg;
    // Since core state is shared between multiple submodules of core,
    // moved into package
    typedef enum logic [2:0] {
        IDLE    = 3'b000, // Waiting to start
        FETCH   = 3'b001, // Fetch instructions from program memory
        DECODE  = 3'b010, // Decode instructions into control signals
        REQUEST = 3'b011, // Request data from registers or memory
        WAIT    = 3'b100, // Wait for response from memory if necessary
        EXECUTE = 3'b101, // Execute ALU and PC calculations
        UPDATE  = 3'b110, // Update registers, NZP, and PC
        DONE    = 3'b111  // Done executing this block
    } core_state_t;

    typedef enum logic [2:0] {
        IDLE     = 3'b000, // Fetcher is idle
        FETCHING = 3'b001, // Actively fetching an instruction
        FETCHED  = 3'b010  // Instruction fetched, waiting to be consumed
    } fetcher_state_t;

    typedef enum logic [1:0] {
        IDLE       = 2'b00, // LSU is idle
        REQUESTING = 2'b01, // LSU has issued a memory request
        WAITING    = 2'b10, // LSU is waiting for memory response
        DONE       = 2'b11  // LSU transaction complete
    } lsu_state_t;

    typedef enum logic [2:0] {
        IDLE           = 3'b000, // No current transaction
        READ_WAITING   = 3'b010, // Read request issued, waiting for memory response
        WRITE_WAITING  = 3'b011, // Write request issued, waiting for acknowledgment
        READ_RELAYING  = 3'b100, // Read data is being sent to requestor
        WRITE_RELAYING = 3'b101  // Write acknowledgment is being sent
    } controller_state_t;
endpackage