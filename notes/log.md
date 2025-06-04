**05/17/2025**
* Simulate on current toolchain (QuestaSim) instead of using project toolchain to convert SV code to V code
* Original used this toolchain in order to employ Python testbenches, but we plan on porting the testbenches to SystemVerilog anyways

**06/04/2025**
* Done: as direct of translation as possible with memory.py > memory.sv
* TODO: port logger.py and format.py, may integrate into test bench instead of making it a separate class/module (?)