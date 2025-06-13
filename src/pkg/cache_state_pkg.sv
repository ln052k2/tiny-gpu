package cache_state_pkg;
typedef enum {
    IDLE, 
    WAIT_ARBITRATION,
    LOOKUP,
    HIT,
    MISS,
    WRITE_MEM,
    REFILL_CACHE, 
    READY
} cache_state_e;
endpackage