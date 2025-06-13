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

    // Simulate "realistic" program with weighted distribution
    constraint opcode_weight_c {
        opcode dist {
            4'b0011 := 20,  // ADD more common
            4'b0100 := 20,  // SUB more common
            4'b0101 := 10,  // MUL less common
            4'b0110 := 10,  // DIV less common
            4'b0111 := 15,  // LDR common
            4'b1000 := 15,  // STR common
            4'b1001 := 8,   // CONST moderate
            4'b0000 := 1,   // NOP rare
            4'b0001 := 3,   // BR uncommon
            4'b0010 := 2,   // CMP uncommon
            4'b1111 := 1    // RET rare
        };
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
        f_opcode: coverpoint f.opcode {
            bins nop    = {4'b0000};
            bins br     = {4'b0001};
            bins cmp    = {4'b0010};
            bins add    = {4'b0011};
            bins sub    = {4'b0100};
            bins mul    = {4'b0101};
            bins div    = {4'b0110};
            bins ldr    = {4'b0111};
            bins str    = {4'b1000};
            bins constant = {4'b1001};
            bins ret    = {4'b1111};
            
            // Transition bins for instruction sequences
            bins load_store_seq = (4'b0111 => 4'b1000); // LDR followed by STR
            bins arith_then_cmp = (4'b0011, 4'b0100, 4'b0101, 4'b0110 => 4'b0010); // Math then CMP
            bins const_then_arith = (4'b1001 => 4'b0011, 4'b0100); // CONST then arithmetic
        }

        f_rd: coverpoint f.rd {
            bins rd_vals[] = {[0:15]};
        }
        
        f_rs: coverpoint f.rs {
            bins rs_vals[] = {[0:15]};
        }
        
        f_rt: coverpoint f.rt {
            bins rt_vals[] = {[0:15]};
        }
        
        f_imm8: coverpoint f.imm8 {
            bins zero  = {8'd0};
            bins max   = {8'd255};
            bins middle   = {[1:254]};
        }
        
        f_nzp: coverpoint f.nzp {
            bins none  = {3'b000};
            bins n     = {3'b100};
            bins z     = {3'b010};
            bins p     = {3'b001};
            bins nz    = {3'b110};
            bins np    = {3'b101};
            bins zp    = {3'b011};
            bins all   = {3'b111};
        }

        // Cross coverage for opcode and destination register
        opcode_rd_cross: cross f.opcode, f.rd {
            // Only track cross coverage for opcodes that use rd
            ignore_bins ignore_no_rd = binsof(f.opcode) intersect {4'b0000, 4'b0001, 4'b0010, 4'b1000, 4'b1111};
        }
        
        // Cross coverage for opcode and source register
        opcode_rs_cross: cross f.opcode, f.rs {
            // Only track cross coverage for opcodes that use rs
            ignore_bins ignore_no_rs = binsof(f.opcode) intersect {4'b0000, 4'b1001, 4'b1111};
        }
        
        // Cross coverage for opcode and immediate values
        opcode_imm_cross: cross f.opcode, f.imm8 {
            // Only track for opcodes that actually use immediate values
            ignore_bins ignore_non_imm = binsof(f.opcode) intersect {
                4'b0000, 4'b0010, 4'b0011, 4'b0100, 4'b0101, 4'b0110, 4'b0111, 4'b1000, 4'b1111
            };
        }
        
        // Cross coverage for branch opcodes and NZP flags
        opcode_nzp_cross: cross f.opcode, f.nzp {
            // Only track for branch instructions
            ignore_bins ignore_non_branch = binsof(f.opcode) intersect {
                4'b0000, 4'b0010, 4'b0011, 4'b0100, 4'b0101, 4'b0110, 4'b0111, 4'b1000, 4'b1001, 4'b1111
            };
        }
    endgroup

    function new();
        cg = new();
        prev_opcode = 4'b0000;
    endfunction

    function void sample(instr_fields_t in);
        f = in;
        cg.sample();
        prev_opcode = f.opcode;  // Track for potential future use
    endfunction
    
    // Get coverage report
    function real get_coverage();
        return cg.get_inst_coverage();
    endfunction
    
    // Print detailed coverage report
    task print_coverage();
        $display("=== INSTRUCTION COVERAGE REPORT ===");
        $display("Overall Coverage: %.2f%%", cg.get_inst_coverage());
        $display("Opcode Coverage: %.2f%%", cg.f_opcode.get_coverage());
        $display("Register RD Coverage: %.2f%%", cg.f_rd.get_coverage());
        $display("Register RS Coverage: %.2f%%", cg.f_rs.get_coverage());
        $display("Register RT Coverage: %.2f%%", cg.f_rt.get_coverage());
        $display("Immediate Coverage: %.2f%%", cg.f_imm8.get_coverage());
        $display("NZP Coverage: %.2f%%", cg.f_nzp.get_coverage());
        $display("Opcode-RD Cross: %.2f%%", cg.opcode_rd_cross.get_coverage());
        $display("Opcode-RS Cross: %.2f%%", cg.opcode_rs_cross.get_coverage());
        $display("Opcode-IMM Cross: %.2f%%", cg.opcode_imm_cross.get_coverage());
        $display("Opcode-NZP Cross: %.2f%%", cg.opcode_nzp_cross.get_coverage());
        $display("====================================");
    endtask
endclass

endpackage