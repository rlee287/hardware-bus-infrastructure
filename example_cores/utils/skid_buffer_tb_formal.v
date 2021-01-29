`default_nettype none

`define DATA_WIDTH_TEST 8
module skid_buffer_tb_formal (
    input wire clk,
    //input wire resetn, // needed?

    input wire [`DATA_WIDTH_TEST-1:0] in_data,
    input wire in_valid,
    output wire in_ready,

    output wire [`DATA_WIDTH_TEST-1:0] out_data,
    output wire out_valid,
    input wire out_ready
);
    // We use a smaller width to speed proofs up
    skid_buffer #(
        .DATA_WIDTH(`DATA_WIDTH_TEST)
    ) DUT (
        .clk(clk),
        //.resetn(resetn)
        .in_data(in_data),
        .in_valid(in_valid),
        .in_ready(in_ready),
        .out_data(out_data),
        .out_valid(out_valid),
        .out_ready(out_ready)
    );

    reg past_valid = 1'b0;
    always @(posedge clk)
        past_valid <= 1'b1;

    // psl assert !out_valid until in_valid;
    reg in_ever_valid = 1'b0;
    reg out_ever_valid = 1'b0;
    always @(posedge clk)
    begin
        if (in_valid)
            in_ever_valid <= 1'b1;
        if (out_valid)
            out_ever_valid <= 1'b1;
    end
    always @(posedge clk)
    begin
        if (past_valid && !in_ever_valid)
            assert(!out_ever_valid);
    end

    // Make traces slightly easier to read
    /*always @(posedge clk)
        if (!(in_valid && !in_ready))
            assume(!$stable(in_data));*/

    wire rx_data;
    wire tx_data;
    assign rx_data = in_valid && in_ready;
    assign tx_data = out_valid && out_ready;
    reg [3:0] rx_count = 0;
    reg [3:0] tx_count = 0;
    always @(posedge clk)
    begin
        if (rx_data)
            rx_count <= rx_count + 1;
        if (tx_data)
            tx_count <= tx_count + 1;
    end
    wire [3:0] rx_tx_diff;
    assign rx_tx_diff = rx_count - tx_count;

    // Cover example run
    always @(posedge clk)
        cover(tx_count == 3 && $past(!tx_data,2));

    // These are generified AXI-Stream ports, so use those properties here
    wire resetn_const;
    wire [0:0] tstrb_const;
    wire tlast_const;
    assign resetn_const = 1'b1;
    // Set all bits to 1's
    assign tstrb_const = ~0;
    assign tlast_const = 1'b1;
    
    axi_stream_master_monitor #(
        .byte_width(`DATA_WIDTH_TEST/8),
        .id_width(0),
        .dest_width(0),
        .user_width(0),
        .USE_ASYNC_RESET(1'b0),
        .MAX_DELAY_TREADY_NO_TVALID(0) // disable
    ) axis_out_properties (
        .aclk(clk),
        .aresetn(resetn_const),
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
        .USE_ASYNC_RESET(1'b0)
    ) axis_in_properties (
        .aclk(clk),
        .aresetn(resetn_const),
        .tvalid(in_valid),
        .tready(in_ready),
        .tdata(in_data),
        .tstrb(tstrb_const),
        .tkeep(tstrb_const),
        .tlast(tlast_const)
    );
endmodule
`undef DATA_WIDTH_TEST
