# 06.04.2025
```
diemhan@mo:~/Documents/tiny-gpu$ vlog -lint -source -file sources.f
QuestaSim-64 vlog 2024.2 Compiler 2024.05 May 20 2024
Start time: 19:20:12 on Jun 04,2025
vlog -lint -source -file sources.f
-- Compiling module alu
###### src/alu.sv(14):     input reg [2:0] core_state,
** Error (suppressible): src/alu.sv(14): (vlog-2892) Net type of 'core_state' was not explicitly declared.
###### src/alu.sv(16):     input reg [1:0] decoded_alu_arithmetic_mux,
** Error (suppressible): src/alu.sv(16): (vlog-2892) Net type of 'decoded_alu_arithmetic_mux' was not explicitly declared.
###### src/alu.sv(17):     input reg decoded_alu_output_mux,
** Error (suppressible): src/alu.sv(17): (vlog-2892) Net type of 'decoded_alu_output_mux' was not explicitly declared.
###### src/alu.sv(19):     input reg [7:0] rs,
** Error (suppressible): src/alu.sv(19): (vlog-2892) Net type of 'rs' was not explicitly declared.
###### src/alu.sv(20):     input reg [7:0] rt,
** Error (suppressible): src/alu.sv(20): (vlog-2892) Net type of 'rt' was not explicitly declared.
-- Compiling module controller
```

There are two ways to get rid of this error: remove the ```\`default_nettype none``` declaration at the top of every file, or to change all the input reg to just input logic/wires. I decided to go with the latter, since ```\`default_nettype none``` can be useful for detecting typos (by preventing new signals from be implicitly created). We're also aiming to port this from Python/Verilog to SystemVerilog, anyways.

