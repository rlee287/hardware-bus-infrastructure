`default_nettype none

module axis_ctr_tx #(
    parameter byte_width = 4,
    parameter USE_CORRECT_RESETN = 1'b1
) (
    input wire clk,
    input wire resetn,
    output wire tvalid,
    input wire tready,
    output reg [(8*byte_width-1):0] tdata
);
    wire tx_transfer;
    assign tx_transfer = tvalid && tready;

    // Good: use async-reset FF to allow tvalid one cycle after resetn release
    // Bad: allow tvalid combinationally with resetn
    reg not_in_reset;
    generate
    if (USE_CORRECT_RESETN)
        always @(posedge clk or negedge resetn)
        begin
            if (!resetn)
                not_in_reset <= 1'b0;
            else // if rising_edge(clk)
                not_in_reset <= 1'b1;
        end
    else
        assign not_in_reset = resetn;
    endgenerate

    assign tvalid = not_in_reset;

    always @(posedge clk or negedge resetn)
    begin
        if (!resetn)
            tdata <= 0;
        else if (tx_transfer)
            tdata <= tdata + 1;
    end
endmodule