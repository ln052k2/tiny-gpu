module lsu_assertions (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [2:0] core_state,
    input logic decoded_mem_read_enable,
    input logic decoded_mem_write_enable,
    input logic [7:0] rs,
    input logic [7:0] rt,
    input logic mem_read_ready,
    input logic [7:0] mem_read_data,
    input logic mem_write_ready,
    input logic [1:0] lsu_state,
    input logic [7:0] lsu_out,
    input logic mem_read_valid,
    input logic [7:0] mem_read_address,
    input logic mem_write_valid,
    input logic [7:0] mem_write_address,
    input logic [7:0] mem_write_data
);

    property read_write_exclusive;
        @(posedge clk) disable iff (reset)
        mem_read_valid && mem_write_valid |-> 0;
    endproperty
    assert property (read_write_exclusive)
        else $error("mem_read_valid and mem_write_valid both active — illegal state.");

endmodule
