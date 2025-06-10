package fetcher_states_pkg;
    typedef enum logic [2:0] {
        IDLE = 3'b000, 
        FETCHING = 3'b001, 
        FETCHED = 3'b010
    } fetcher_state_e;
endpackage
