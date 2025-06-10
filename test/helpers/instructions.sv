package instruction_pkg;

// Instruction field struct
typedef struct packed {
    randc logic [3:0] opcode;
    rand logic [3:0] rd;
    rand logic [3:0] rs;
    rand logic [3:0] rt;
    rand logic [7:0] imm8;
    rand logic [2:0] nzp;

    // Constraint block for legal opcodes only
    constraint opcode_c {
        opcode inside {4'b0000, 4'b0001, 4'b0010, 4'b0011, 4'b0100, 4'b0101, 
                       4'b0110, 4'b0111, 4'b1000, 4'b1001, 4'b1111};
    }
} instr_fields_t;


// Instruction encoder function
function logic [15:0] encode(instr_fields_t f);
    case (f.opcode)
        4'b0000: return 16'b0000_0000_0000_0000; // NOP
        4'b0001: return {4'b0001, f.nzp, f.imm8}; // BRnzp
        4'b0010: return {4'b0010, 4'b0000, f.rs, f.rt}; // CMP
        4'b0011, 4'b0100, 4'b0101, 4'b0110:
            return {f.opcode, f.rd, f.rs, f.rt}; // ADD, SUB, MUL, DIV
        4'b0111: return {f.opcode, f.rd, f.rs, 4'b0000}; // LDR
        4'b1000: return {f.opcode, 4'b0000, f.rs, f.rt}; // STR
        4'b1001: return {f.opcode, f.rd, f.imm8}; // CONST
        4'b1111: return 16'b1111_0000_0000_0000; // RET
        default: return 16'hDEAD;
    endcase
endfunction

function instr_fields_t generate_instr();
    instr_fields_t f;
    assert(f.randomize()) else
        $fatal("Failed to randomize instruction fields");
    return encode(f);
endfunction

task automatic print_instr(instr_fields_t f);
    $display("OP: %b RD: %0d RS: %0d RT: %0d IMM: %0d NZP: %b",
            f.opcode, f.rd, f.rs, f.rt, f.imm8, f.nzp);
endtask

// Instruction coverage group class
class InstrCoverage;
    instr_fields_t f;

    covergroup cg @(posedge clk);
        coverpoint f.opcode {
            bins nop    = {4'b0000};
            bins br     = {4'b0001};
            bins add    = {4'b0011};
            bins sub    = {4'b0100};
            bins mul    = {4'b0101};
            bins div    = {4'b0110};
            bins ldr    = {4'b0111};
            bins str    = {4'b1000};
            bins const  = {4'b1001};
            bins ret    = {4'b1111};
        }

        coverpoint f.rd {
            bins rd_vals[] = {[0:15]};
        }
        coverpoint f.rs {
            bins rs_vals[] = {[0:15]};
        }
        coverpoint f.rt {
            bins rt_vals[] = {[0:15]};
        }
        coverpoint f.imm8 {
            bins zero  = {8'd0};
            bins max   = {8'd255};
            bins imm   = {[1:254]}
        }
        coverpoint f.nzp {
            bins none  = {3'b000};
            bins n     = {3'b100};
            bins z     = {3'b010};
            bins p     = {3'b001};
            bins combo[] = {[1:6]};
            bins all   = {3'b111};
        }

        opcode_rd_cross: cross f.opcode, f.rd;
    endgroup

    function new();
        cg = new();
    endfunction

    function void sample(instr_fields_t in);
        f = in;
        cg.sample();
    endfunction
endclass

endpackage