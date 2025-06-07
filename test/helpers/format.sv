// debug_utils_pkg.sv
package debug_utils;

  // Enable this at compile time with +define+DEBUG
  `ifdef DEBUG
    bit DEBUG_ENABLE = 1;
  `else
    bit DEBUG_ENABLE = 0;
  `endif

  // Runtime checkable debug print
  task automatic debug_info(string msg);
    if (DEBUG_ENABLE)
      $display(msg);
  endtask

  // Format register name
  // TODO: figure out how to handle blockIdx, blockDim, threadIdx
  function string format_register(input int reg);
    if (reg < 13) return $sformatf("R%0d", reg);
    else if (reg == 13) return "blockIdx";
    else if (reg == 14) return "blockDim";
    else if (reg == 15) return "threadIdx";
    else return "INVALID";
  endfunction

  // Format instruction (16-bit binary)
  function string format_instruction(input logic [15:0] instr);
    string op;
    string rd = format_register(instr[11:8]);
    string rs = format_register(instr[7:4]);
    string rt = format_register(instr[3:0]);
    string imm = $sformatf("#%0d", instr[7:0]);

    case (instr[15:12])
      4'b0000: op = "NOP";
      4'b0001: op = $sformatf("BRnzp %s%s%s, %s",
                              instr[11] ? "N" : "",
                              instr[10] ? "Z" : "",
                              instr[9] ? "P" : "",
                              imm);
      4'b0010: op = $sformatf("CMP %s, %s", rs, rt);
      4'b0011: op = $sformatf("ADD %s, %s, %s", rd, rs, rt);
      4'b0100: op = $sformatf("SUB %s, %s, %s", rd, rs, rt);
      4'b0101: op = $sformatf("MUL %s, %s, %s", rd, rs, rt);
      4'b0110: op = $sformatf("DIV %s, %s, %s", rd, rs, rt);
      4'b0111: op = $sformatf("LDR %s, %s", rd, rs);
      4'b1000: op = $sformatf("STR %s, %s", rs, rt);
      4'b1001: op = $sformatf("CONST %s, %s", rd, imm);
      4'b1111: op = "RET";
      default: op = "UNKNOWN";
    endcase
    return op;
  endfunction

  // FILE: src/core.sv
  // Format core state
  function string format_core_state(input logic [2:0] state);
    string state_str;

    case (state)
      3'b000: state_str = "IDLE";
      3'b001: state_str = "FETCH";
      3'b010: state_str = "DECODE";
      3'b011: state_str = "REQUEST";
      3'b100: state_str = "WAIT";
      3'b101: state_str = "EXECUTE";
      3'b110: state_str = "UPDATE";
      3'b111: state_str =  "DONE";
      default: return $sformatf("INVALID (%b)", state);
    endcase

    return $sformatf("Core State: %s", state_str);
  endfunction

  // FILE: src/fetcher.sv
  // Format fetcher state
  function string format_fetcher_state(input logic [2:0] state);
    string state_str;

    case (state)
      3'b000: state_str = "IDLE";
      3'b001: state_str = "FETCHING";
      3'b010: state_str = "FETCHED";
      default: return $sformatf("INVALID (%b)", state);
    endcase

    return $sformatf("Fetcher State: %s", state_str);
  endfunction


  // FILE: src/lsu.sv
  // Format LSU state
  function string format_lsu_state(input logic [1:0] state);
    string state_str;

    case (state)
      2'b00: state_str = "IDLE";
      2'b01: state_str = "REQUESTING";
      2'b10: state_str = "WAITING";
      2'b11: state_str = "DONE";
      default: return $sformatf("INVALID (%b)", state);
    endcase

    return $sformatf("LSU State: %s", state_str);
  endfunction


  // FILE: src/controller.sv
  // Format memory controller state
  function string format_memctrl_state(input logic [2:0] state);
    string state_str;
    case (state)
      3'b000: state_str = "IDLE";
      3'b010: state_str =  "READ_WAITING";
      3'b011: state_str =  "WRITE_WAITING";
      3'b100: state_str =  "READ_RELAYING";
      3'b101: state_str =  "WRITE_RELAYING";
      default: return $sformatf("INVALID (%b)", state);
    endcase

    return $sformatf("Memory Controller State: %s", state_str);
  endfunction

endpackage
