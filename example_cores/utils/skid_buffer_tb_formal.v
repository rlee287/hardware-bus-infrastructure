`default_nettype none

`define DATA_WIDTH_TEST 8
module skid_buffer_tb_formal #(
    parameter USE_ASYNC_RESET = 1'b0
) (
    input wire clk,
    input wire reset,

    input wire [`DATA_WIDTH_TEST-1:0] in_data,
    input wire in_valid,
    output wire in_ready,

    output wire [`DATA_WIDTH_TEST-1:0] out_data,
    output wire out_valid,
    input wire out_ready
);
    // We use a smaller width to speed proofs up
    skid_buffer #(
        .USE_ASYNC_RESET(USE_ASYNC_RESET),
        .DATA_WIDTH(`DATA_WIDTH_TEST)
    ) DUT (
        .clk(clk),
        .reset(reset),
        .in_data(in_data),
        .in_valid(in_valid),
        .in_ready(in_ready),
        .out_data(out_data),
        .out_valid(out_valid),
        .out_ready(out_ready)
    );

    // These are generified AXI-Stream ports, so use those properties here
    wire resetn;
    wire [0:0] tstrb_const;
    wire tlast_const;
    assign resetn = !reset;
    // Set all bits to 1's
    assign tstrb_const = ~0;
    assign tlast_const = 1'b1;
    
    axi_stream_master_monitor #(
        .byte_width(`DATA_WIDTH_TEST/8),
        .id_width(0),
        .dest_width(0),
        .user_width(0),
        .USE_ASYNC_RESET(USE_ASYNC_RESET),
        .MAX_DELAY_TREADY_NO_TVALID(0) // disable
    ) axis_out_properties (
        .aclk(clk),
        .aresetn(resetn),
        .tvalid(out_valid),
        .tready(out_ready),
        .tdata(out_data),
        .tstrb(tstrb_const),
        .tkeep(tstrb_const),
        .tlast(tlast_const)
    );
    axi_stream_slave_monitor #(
        .byte_width(`DATA_WIDTH_TEST/8),
        .id_width(0),
        .dest_width(0),
        .user_width(0),
        .USE_ASYNC_RESET(USE_ASYNC_RESET)
    ) axis_in_properties (
        .aclk(clk),
        .aresetn(resetn),
        .tvalid(in_valid),
        .tready(in_ready),
        .tdata(in_data),
        .tstrb(tstrb_const),
        .tkeep(tstrb_const),
        .tlast(tlast_const)
    );
endmodule
`undef DATA_WIDTH_TEST
