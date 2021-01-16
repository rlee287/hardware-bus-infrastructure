`default_nettype none

module axis_ctr_tx_tb_formal #(
    parameter byte_width = 4,
    parameter USE_CORRECT_RESETN = 1'b1
) (
    input wire clk,
    input wire resetn,
    output wire tvalid,
    input wire tready,
    output reg [(8*byte_width-1):0] tdata
);
    wire [(byte_width-1):0] tstrb_const;
    wire tlast_const;
    // Set all bits to 1's
    assign tstrb_const = ~0;
    assign tlast_const = 1'b1;

    /*(* gclk *) reg formal_timestep;

    // Assume clock toggles every other formal timestep
    always @(posedge formal_timestep)
        assume(!$stable($stable(clk)));
    
    always @(posedge formal_timestep)
        if (!$rose(clk))
        begin
            assume($stable(tready));
        end*/

    axis_ctr_tx #(
        .byte_width(byte_width),
        .USE_CORRECT_RESETN(USE_CORRECT_RESETN)
    ) DUT (
        .clk(clk),
        .resetn(resetn),
        .tvalid(tvalid),
        .tready(tready),
        .tdata(tdata)
    );

    axi_stream_master_monitor #(
        .byte_width(4),
        .id_width(0),
        .dest_width(0),
        .user_width(0),
        .USE_ASYNC_RESET(1'b1)
    ) axis_out_properties (
        .aclk(clk),
        .aresetn(resetn),
        .tvalid(tvalid),
        .tready(tready),
        .tdata(tdata),
        .tstrb(tstrb_const),
        .tkeep(tstrb_const),
        .tlast(tlast_const)
    );
    // Cast the constant "1" to the appropriate type (argh...)
    localparam [(8*byte_width-1):0] incr_size = 1;

    reg past_valid = 1'b0;
    always @(posedge clk)
        past_valid <= 1'b1;

    always @(posedge clk)
    begin
        if (!resetn)
            assert(tdata == 0);
        else
            if (past_valid && $past(tvalid && tready))
                assert(tdata == $past(tdata)+incr_size);
    end
endmodule