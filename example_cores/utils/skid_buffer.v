`default_nettype none

/*
 * A skid buffer for buffering data in valid/ready handshakes
 * Useful for writing high-throughput AXI/AXI-Lite/AXI-Stream cores
 * Based on the design of http://fpgacpu.ca/fpga/Pipeline_Skid_Buffer.html
 */
module skid_buffer #(
    parameter USE_ASYNC_RESET = 1'b0,
    parameter DATA_WIDTH = 32
) (
    input wire clk,
    input wire reset,

    input wire [DATA_WIDTH-1:0] in_data,
    input wire in_valid,
    output wire in_ready,

    output wire [DATA_WIDTH-1:0] out_data,
    output wire out_valid,
    input wire out_ready
);
    generate
        if (USE_ASYNC_RESET)
            skid_buffer_async #(
                .DATA_WIDTH(DATA_WIDTH)
            ) inst_async_module (
                .clk(clk),
                .reset(reset),
                .in_data(in_data),
                .in_valid(in_valid),
                .in_ready(in_ready),
                .out_data(out_data),
                .out_valid(out_valid),
                .out_ready(out_ready)
            );
        else
            skid_buffer_sync #(
                .DATA_WIDTH(DATA_WIDTH)
            ) inst_sync_module (
                .clk(clk),
                .reset(reset),
                .in_data(in_data),
                .in_valid(in_valid),
                .in_ready(in_ready),
                .out_data(out_data),
                .out_valid(out_valid),
                .out_ready(out_ready)
            );
    endgenerate
endmodule