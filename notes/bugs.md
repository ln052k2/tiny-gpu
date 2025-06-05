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

To get rid of these errors, remove the ```\`default_nettype none``` declaration at the top of every file. Note that this can be useful for detecting typos (by preventing new signals from be implicitly created), so we may loop back to find a better fix for these errors in the future.

I assumed this error would appear for other files, so I went ahead and changed all the input reg declarations in other files as well once I was able to verify that doing so with alu.sv resolved all errors with that message.

