BEFORE:
Core executes each instruction of the kernel in lockstep per-thread.
* All threads share a scheduler which determines core state
* Every cycle, scheduler advances one thread through the full cycle serially
* Core state cycle: FETCH -> DECODE -> READ -> EXECUTE -> MEMORY -> WB
* ALU works during EXECUTE stage
* LSU operates during MEMORY stage
* Register writes happen at WRITEBACK stage
* PC update logic uses signals at WRITEBACK stage

PIPELINE:
* Pipeline register for each stage of each thread in core.sv
* Need to edit scheduler.sv, fetcher.sv and decoder.sv to work with multiple concurrent threads
* Scheduler has to states of multiple threads (and corresponding outputs i.e done and core_state)

