package alu_ops_pkg;
  // only these are implemented thusfar
  typedef enum logic [1:0] {
    ADD = 2'b00,
    SUB = 2'b01,
    MUL = 2'b10,
    DIV = 2'b11
  } alu_op_e;
endpackage