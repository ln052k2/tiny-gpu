package lsu_states_pkg;
    typedef enum logic [1:0] {
        IDLE = 2'b00,
        REQUESTING = 2'b01,
        WAITING = 2'b10,
        DONE = 2'b11
    } lsu_state_e;
endpackage
