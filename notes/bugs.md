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
There are a couple more of these errors in various files that have to do with an I/O or parameter list ending with a comma. I went through each of the module declarations and deleted trailing commas, which resolved 5 of these errors.

```
** Error (suppressible): src/scheduler.sv(79): (vlog-2244) Variable 'any_lsu_waiting' is implicitly static. You must either explicitly declare it as static or automatic
or remove the initialization in the declaration of variable.
```
The variable any_lsu_waiting is declared in the same line it is initialized. To fix this, I declared it at the beginning of the module
* BEFORE: ```logic any_lsu_waitin = 1'b0;```
* AFTER: ```logic any lsu_waiting; ... any_lsu_waitin = 1'b0;```

```
###### test/test_matadd.sv(27):     Memory #(
** Error (suppressible): test/test_matadd.sv(27): (vlog-13071) Illegal parameter specification for non-parameterized class type 'Memory'.
```
Memory class was not declared to be parameterizable, so I moved the parameters to the class header.
* BEFORE: ```class Memory; parameter int ADDR_BITS = 8; ... endclass```
* AFTER: ```class Memory #(parameter int ADDDR_BITS = 8)```

```
###### test/test_matadd.sv(93):         .data_mem_write_ready(data_memory.mem_write_ready)
# ** Error: test/test_matadd.sv(93): (vopt-2898) A dynamic or an automatic variable reference (data_memory) is not allowed.
```
I shouldn't be using the memory object itself, but the associated interface.
* BEFORE: ```.data_mem_write_ready(data_memory.mem_write_ready)```
* AFTER: ```.data_mem_write_ready(data_mem_if.mem_write_ready)```

