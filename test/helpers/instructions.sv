package instruction_pkg;

class instr_fields_t;
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

    // Encode instruction fields into 16-bit instruction
    function logic [15:0] encode();
        case (opcode)
            4'b0000: return 16'b0000_0000_0000_0000; // NOP
            4'b0001: return {4'b0001, nzp, imm8};    // BRnzp
            4'b0010: return {4'b0010, 4'b0000, rs, rt}; // CMP
            4'b0011, 4'b0100, 4'b0101, 4'b0110:
                return {opcode, rd, rs, rt};          // ADD, SUB, MUL, DIV
            4'b0111: return {opcode, rd, rs, 4'b0000}; // LDR
            4'b1000: return {opcode, 4'b0000, rs, rt}; // STR
            4'b1001: return {opcode, rd, imm8};      // CONST
            4'b1111: return 16'b1111_0000_0000_0000; // RET
            default: return 16'hDEAD;
        endcase
    endfunction

    // Randomize fields and return encoded instruction
    function logic [15:0] generate_instr();
        if (!this.randomize())
            $fatal("Failed to randomize instruction fields");
        return encode();
    endfunction

    // Print human-readable fields
    task print_instr();
        $display("OP: %b RD: %0d RS: %0d RT: %0d IMM: %0d NZP: %b",
                opcode, rd, rs, rt, imm8, nzp);
    endtask
endclass


// Instruction coverage group class
class InstrCoverage;
    instr_fields_t f;
    logic [3:0] prev_opcode;

    covergroup cg;
        coverpoint f.opcode {
            bins nop    = {4'b0000};
            bins br     = {4'b0001};
            bins add    = {4'b0011};
            bins sub    = {4'b0100};
            bins mul    = {4'b0101};
            bins div    = {4'b0110};
            bins ldr    = {4'b0111};
            bins str    = {4'b1000};
            bins constant = {4'b1001};
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
            bins imm   = {[1:254]};
        }
        coverpoint f.nzp {
            bins none  = {3'b000};
            bins n     = {3'b100};
            bins z     = {3'b010};
            bins p     = {3'b001};
            bins combo[] = {[1:6]};
            bins all   = {3'b111};
        }


        opcode_rd_cross: cross f.opcode, f.rd; // test all opcodes w/ possible rd
        opcode_rs_cross: cross f.opcode, f.rs; // test all opcodes w/ possible rs
        opcode_imm_cross: cross f.opcode, f.imm8 {
            ignore_bins ignore_non_imm = opcode_imm_cross with 
                (f.opcode != 4'b0001 && f.opcode != 4'b1001);
        } // tracks combinations of opcode and immediate values

        // Track instruction sequences
        coverpoint f.opcode {
            bins load_store_seq = (4'b0111 => 4'b1000); // LDR followed by STR
            bins arith_seq = (4'b0011, 4'b0100, 4'b0101, 4'b0110 => 4'b0010); // Math then CMP
        }

        // Simulate "realistic" program
        constraint opcode_c {
        opcode dist {
            4'b0011 := 20,
            4'b0100 := 20,
            4'b0111 := 15,
            4'b1000 := 15,
            [4'b0000:4'b0010] := 5,
            4'b1111 := 1
        };
    }


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