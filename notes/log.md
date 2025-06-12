**05/17/2025**
* Simulate on current toolchain (QuestaSim) instead of using project toolchain to convert SV code to V code
* Original used this toolchain in order to employ Python testbenches, but we plan on porting the testbenches to SystemVerilog anyways

**06/03/2025**
* Done: as direct of translation as possible with memory.py > memory.sv
* TODO: port logger.py and format.py, may integrate into test bench instead of making it a separate class/module (?)

**06/03/2025**
* Removed the interface from memory, setup and test* modules since the current gpu code does not use it (yet ?) since it was originally written for Verilog
* GPU modules may be refactored in the future to use interfaces since many modules connect via the same signals
* Added SystemVerilog port for test_matadd
* Added sources.f file for quick compilation (use ```vlog -lint -source -file sources.f```)
* Changed signals that used input reg -> input logic/wires to move from Verilog to SystemVerilog

## Cache
* Write through, direct mapped
* Cache hits served instantly
* Cache misses trigger memory read -> requesting LSU is stalled until completion

[GPU cores]
     lsu_if (multi-channel)
     [cache]   ← arbitration + tag/data store + mem_if interface
  data_mem_if (external memory)

* Cache requests are serialized, not served in parallel
* Other requests are stalled until arbitration grants them access
* BUT fixed priority arbitration, and fetcher always fetches in blocks