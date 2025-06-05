# 06.04.2025
```
diemhan@mo:~/Documents/tiny-gpu$ vlog -lint -source -file sources.f
QuestaSim-64 vlog 2024.2 Compiler 2024.05 May 20 2024
Start time: 19:20:12 on Jun 04,2025
vlog -lint -source -file sources.f
-- Compiling module alu
###### src/alu.sv(14):     input reg [2:0] core_state,
** Error (suppressible): src/alu.sv(14): (vlog-2892) Net type of 'core_state' was not explicitly declared.
```

To get rid of these errors, remove the ```\`default_nettype none``` declaration at the top of every file. Note that this can be useful for detecting typos (by preventing new signals from be implicitly created), so we may loop back to find a better fix for these errors in the future.

I assumed this error would appear for other files, so I went ahead and changed all the input reg declarations in other files as well once I was able to verify that doing so with alu.sv resolved all errors with that message. That effectively took us from 63 errors to 26 errors/7 warnings.

```
###### src/controller.sv(52):             mem_read_address <= 0;
** Error (suppressible): src/controller.sv(52): (vlog-2997) Cannot assign a packed type 'bit signed[31:0]' to an unpacked type 'reg[ADDR_BITS-1:0] $[NUM_CHANNELS-1:0]'.
```

Multiple of these errors for the reset branch in the controller.sv module assigning 0s to arrays of arrays. Use aggregate assignment to initialize these unpacked arrays.
* BEFORE: ```mem_read_address <= 0;```
* AFTER: ```mem_read_address <= '{default: '0};```

```
###### src/core.sv(116):     ) scheduler_instance (
** Error: (vlog-13069) src/core.sv(116): near ")": syntax error, unexpected ')', expecting '.'.
```
