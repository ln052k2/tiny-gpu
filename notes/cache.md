# Context
* One cache per core, with each core having multiple LSUs that may read/write to memory within one cycle
* One data memory controller for all cores of the GPU
# Cache Structure
### Direct Mapped Cache
* Each memory address maps exactly to one cache line
* Index is the lower bits of the address
* Cache is has parameterizable CACHE_LINE entries
* Each cache line contains valid bit, tag and data
* Adress is split into {tag, index} bits
## Components
### Arbitration Logic
* Round robin arbiter selects which channel gets serviced next
* Prioritizes channels with pending read/write requests
### Cache Memory
* Array of cache lines, one central one for every LSU in the core
### Interface
* cache_if faces the consumer side (LSUs)
* data_mem_if faces the global/main memory controller

# Operation Flow
## Read Operations
* Check if requested address hits in cache -> valid + tag match
* If cache hit, return data immediately and assert the ready signal
* If cache miss, forward request to main memory
## Write Operations
* Use write through policy: always writes to both cache and main memory
* Updates cache line immediately
* Forwards write to main memory and waits for acknowledgement

# Possible Issues
### Arbitration Bottleneck
* Since multiple parallel requests are made but only one memory request can be handled at a time across all channels, this results in a bottleneck through serialization
* Threads are stalled waiting for their turn in the arbitration queue

# Issues with Initial Implementation
### Arbiter
* Arbiter cycles through channels in a fixed order
* Channel only gets granted if it has a pending request, but the current_grant pointer always advances to the next requesting channel
* HOWEVER:
    * If channel 0 makes a request right after it's serviced, it goes to the back of the queue
    * If channel 1 makes a request before its turn, it gets serviced almost immediately

### State Management
* The cache doesn't track which channel is waiting for a memory response
* If a memory response takes several cycles
* Other channels can't be serviced during the wait
* The system doesn't remember which channel initiated the request
* The arbiter might switch to another channel before the memory responds

# NEW CACHE
