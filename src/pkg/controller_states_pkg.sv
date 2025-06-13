package controller_states_pkg;
    typedef enum logic [2:0] {
        IDLE = 3'b000, 
        READ_WAITING = 3'b010, 
        WRITE_WAITING = 3'b011,
        READ_RELAYING = 3'b100,
        WRITE_RELAYING = 3'b101
    } controller_state_e;
endpackage