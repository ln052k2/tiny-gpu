`timescale 1ns/1ns
`include "helpers/memory.sv"
import opcodes_pkg::*;

module test_compare;

  localparam DATA_MEM_ADDR_BITS    = 8;
  localparam DATA_MEM_DATA_BITS    = 8;
  localparam PROGRAM_MEM_ADDR_BITS = 8;
  localparam PROGRAM_MEM_DATA_BITS = 16;
  localparam CORES                 = 2;
  localparam THREADS_PER_BLOCK     = 4;
  localparam PROGRAM_LEN           = 64;
  localparam DATA_MEM_CHANNELS     = CORES * THREADS_PER_BLOCK;
  localparam PROGRAM_MEM_CHANNELS  = CORES;  

  logic clk;
  always #5 clk = ~clk;

  logic reset;
  logic start;
  logic done1, done2;

  logic device_control_write_enable;
  logic [7:0] device_control_data;

// create two sets of interfaces, memory modules, etc
  mem_if #(
    .ADDR_BITS(PROGRAM_MEM_ADDR_BITS),
    .DATA_BITS(PROGRAM_MEM_DATA_BITS),
    .CHANNELS(PROGRAM_MEM_CHANNELS)
  ) prog_if1(), prog_if2();

  mem_if #(
    .ADDR_BITS(DATA_MEM_ADDR_BITS),
    .DATA_BITS(DATA_MEM_DATA_BITS),
    .CHANNELS(DATA_MEM_CHANNELS)
  ) data_if1(), data_if2();

  Memory #(
    .ADDR_BITS(PROGRAM_MEM_ADDR_BITS),
    .DATA_BITS(PROGRAM_MEM_DATA_BITS),
    .CHANNELS(PROGRAM_MEM_CHANNELS)
  ) program_memory1, program_memory2;

  Memory #(
    .ADDR_BITS(DATA_MEM_ADDR_BITS),
    .DATA_BITS(DATA_MEM_DATA_BITS),
    .CHANNELS(DATA_MEM_CHANNELS)
  ) data_memory1, data_memory2;

//instantiate both new and baseline gpus
  gpu #(
    .DATA_MEM_ADDR_BITS   (DATA_MEM_ADDR_BITS),
    .DATA_MEM_DATA_BITS   (DATA_MEM_DATA_BITS),
    .DATA_MEM_NUM_CHANNELS(DATA_MEM_CHANNELS),
    .PROGRAM_MEM_ADDR_BITS(PROGRAM_MEM_ADDR_BITS),
    .PROGRAM_MEM_DATA_BITS(PROGRAM_MEM_DATA_BITS),
    .PROGRAM_MEM_NUM_CHANNELS(PROGRAM_MEM_CHANNELS),
    .NUM_CORES            (CORES),
    .THREADS_PER_BLOCK    (THREADS_PER_BLOCK)
  ) dut1 (
    .clk(clk), .reset(reset), .start(start), .done(done1),
    .device_control_write_enable(device_control_write_enable),
    .device_control_data(device_control_data),
    .program_mem_if(prog_if1),
    .data_mem_if   (data_if1)
  );

  gpu_baseline #(
    .DATA_MEM_ADDR_BITS   (DATA_MEM_ADDR_BITS),
    .DATA_MEM_DATA_BITS   (DATA_MEM_DATA_BITS),
    .DATA_MEM_NUM_CHANNELS(DATA_MEM_CHANNELS),
    .PROGRAM_MEM_ADDR_BITS(PROGRAM_MEM_ADDR_BITS),
    .PROGRAM_MEM_DATA_BITS(PROGRAM_MEM_DATA_BITS),
    .PROGRAM_MEM_NUM_CHANNELS(PROGRAM_MEM_CHANNELS),
    .NUM_CORES            (CORES),
    .THREADS_PER_BLOCK    (THREADS_PER_BLOCK)
  ) dut2 (
    .clk(clk), .reset(reset), .start(start), .done(done2),
    .device_control_write_enable(device_control_write_enable),
    .device_control_data(device_control_data),
    .program_mem_if(prog_if2),
    .data_mem_if   (data_if2)
  );

// create a class so that we can use constraints to generate valid instructions
  class InstrGen;
    rand logic [3:0] opcode, rd, rs, rt;
    // Only generate register‐register arithmetic and compare
    constraint op_c { opcode inside {ADD, SUB, MUL, DIV, CMP}; }
    // Only use registers 0–12 (R0–R12 are writable)
    constraint reg_c { rd < 13; rs < 13; rt < 13; }

    function logic [15:0] instr();
      instr = {opcode, rd, rs, rt};
    endfunction
  endclass

// fill buffer with random instructions
  logic [PROGRAM_MEM_DATA_BITS-1:0] prog [0:PROGRAM_LEN-1];
  initial begin
    static InstrGen gen = new();
    foreach (prog[i]) begin
        // ensure the last instruction is RET so the program terminates
      if (i == PROGRAM_LEN-1) begin
        prog[i] = RET;
      end else begin
        if (!gen.randomize()) 
          $fatal("***ERROR: Could not generate a random valid instruction.");
        prog[i] = gen.instr();
      end
    end
  end

  initial begin
    // initialize
    clk = 0;
    reset = 1;
    start = 0;
    device_control_write_enable = 0;
    device_control_data = THREADS_PER_BLOCK;
    program_memory1 = new("prog1", prog_if1);
    program_memory2 = new("prog2", prog_if2);
    data_memory1    = new("data1", data_if1);
    data_memory2    = new("data2", data_if2);

    // load memories
    program_memory1.load(prog);
    program_memory2.load(prog);
    // zero‐initialize data memories
    data_memory1.load('{default: 8'h00});
    data_memory2.load(data_memory1.memory);

    // apply reset
    @(posedge clk);
    reset = 0;

    // write thread‐count
    device_control_write_enable = 1;
    @(posedge clk);
    device_control_write_enable = 0;

    // start both DUTs
    start = 1;
    @(posedge clk);
    start = 0;

    // Run until both designs assert done
    while (!(done1 && done2)) begin
      program_memory1.run();
      program_memory2.run();
      data_memory1.run();
      data_memory2.run();
      @(posedge clk);
    end

    $display("Both designs finished. Test PASSED.");
    $finish;
  end

// at every cycle, ensure every signal from both test benches match
  always @(posedge clk) begin
    // done signal
    assert (done1 === done2)
      else $fatal("Done mismatch at time %0t: dut1=%b dut2=%b", $time, done1, done2);

    // program‐mem interface
    for (int i = 0; i < PROGRAM_MEM_CHANNELS; i++) begin
      assert (prog_if1.read_valid[i]  === prog_if2.read_valid[i])  
        else $fatal("prog_if.read_valid[%0d] mismatch", i);
      assert (prog_if1.read_address[i] === prog_if2.read_address[i]) 
        else $fatal("prog_if.read_address[%0d] mismatch", i);
      assert (prog_if1.read_ready[i]  === prog_if2.read_ready[i])  
        else $fatal("prog_if.read_ready[%0d] mismatch", i);
      assert (prog_if1.read_data[i]   === prog_if2.read_data[i])   
        else $fatal("prog_if.read_data[%0d] mismatch", i);
    end

    // data‐mem interface
    for (int i = 0; i < DATA_MEM_CHANNELS; i++) begin
      assert (data_if1.read_valid[i]   === data_if2.read_valid[i])   
        else $fatal("data_if.read_valid[%0d] mismatch", i);
      assert (data_if1.read_address[i] === data_if2.read_address[i]) 
        else $fatal("data_if.read_address[%0d] mismatch", i);
      assert (data_if1.read_ready[i]   === data_if2.read_ready[i])   
        else $fatal("data_if.read_ready[%0d] mismatch", i);
      assert (data_if1.read_data[i]    === data_if2.read_data[i])    
        else $fatal("data_if.read_data[%0d] mismatch", i);

      assert (data_if1.write_valid[i]   === data_if2.write_valid[i])   
        else $fatal("data_if.write_valid[%0d] mismatch", i);
      assert (data_if1.write_address[i] === data_if2.write_address[i]) 
        else $fatal("data_if.write_address[%0d] mismatch", i);
      assert (data_if1.write_data[i]    === data_if2.write_data[i])    
        else $fatal("data_if.write_data[%0d] mismatch", i);
      assert (data_if1.write_ready[i]   === data_if2.write_ready[i])   
        else $fatal("data_if.write_ready[%0d] mismatch", i);
    end
  end

endmodule
