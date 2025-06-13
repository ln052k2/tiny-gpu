package opcodes_pkg;    
    typedef enum logic [3:0] { 
            NOP = 4'b0000,
            BRnzp = 4'b0001,
            CMP = 4'b0010,
            ADD = 4'b0011,
            SUB = 4'b0100,
            MUL = 4'b0101,
            DIV = 4'b0110,
            LDR = 4'b0111,
            STR = 4'b1000,
            CONST = 4'b1001,
            RET = 4'b1111
    } opcode_e;
endpackage

