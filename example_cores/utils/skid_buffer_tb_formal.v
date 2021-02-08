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

    reg past_valid = 1'b0;
    always @(posedge clk)
        past_valid <= 1'b1;

    // psl assert !out_valid until in_valid;
    reg in_ever_valid = 1'b0;
    reg out_ever_valid = 1'b0;
    always @(posedge clk)
    begin
        if (reset)
        begin
            in_ever_valid <= 1'b0;
            out_ever_valid <= 1'b0;
        end
        else
        begin
            if (in_valid)
                in_ever_valid <= 1'b1;
            if (out_valid)
                out_ever_valid <= 1'b1;
        end
    end
    always @(posedge clk)
    begin
        if (past_valid && !in_ever_valid)
            assert(!out_ever_valid);
    end

    wire rx_occured;
    wire tx_occured;
    assign rx_occured = in_valid && in_ready;
    assign tx_occured = out_valid && out_ready;
    reg [3:0] rx_count = 4'h0;
    reg [3:0] tx_count = 4'h0;
    always @(posedge clk)
    begin
        if (reset)
        begin
            rx_count <= 0;
            tx_count <= 0;
        end
        else
        begin
            if (rx_occured)
                rx_count <= rx_count + 1;
            if (tx_occured)
                tx_count <= tx_count + 1;
        end
    end
    wire [3:0] rx_tx_diff;
    assign rx_tx_diff = rx_count - tx_count;


    // Make traces easier to read for cover
    reg in_data_was_never_stable = 1'b1;
    always @(posedge clk)
        if (past_valid && !(in_valid && !in_ready) && $stable(in_data))
            in_data_was_never_stable <= 1'b0;
    // Cover example run
    always @(posedge clk)
        cover(in_data_was_never_stable
                && tx_count == 3 && $past(in_valid && !in_ready,2));

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
