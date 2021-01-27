`default_nettype none

/*
 * A skid buffer for buffering data in valid/ready handshakes
 * Useful for writing high-throughput AXI/AXI-Lite/AXI-Stream cores
 */
module skid_buffer #(
    parameter DATA_WIDTH = 32
) (
    input wire clk,
    //input wire resetn, // needed?

    input wire [DATA_WIDTH-1:0] in_data,
    input wire in_valid,
    output reg in_ready = 1'b0,

    output reg [DATA_WIDTH-1:0] out_data,
    output reg out_valid = 1'b0,
    input wire out_ready
);

    reg [DATA_WIDTH-1:0] data_buffer;
    reg in_valid_delayed = 1'b0;

    always @(posedge clk)
    begin
        if (in_valid)
        begin
            data_buffer <= in_data;
        end
        in_valid_delayed <= in_valid;
        // Always delay in_ready from out_ready by a clock cycle
        in_ready <= out_ready;
    end

    reg past_valid = 1'b0;
    always @(posedge clk)
        past_valid <= 1'b1;
    always @(posedge clk)
    begin
        if (past_valid)
        begin
            assert(in_valid_delayed == $past(in_valid));
            assert(in_ready == $past(out_ready));
        end
    end

    reg use_data_in_buffer_prev = 1'b1;
    reg use_data_in_buffer;
    always @(*)
    begin
        if (in_ready && out_ready)
            use_data_in_buffer = 1'b0;
        else if (in_ready ^ out_ready) // Was in && !out
            use_data_in_buffer = 1'b1;
        else
            use_data_in_buffer = use_data_in_buffer_prev;
    end
    always @(posedge clk)
        use_data_in_buffer_prev <= use_data_in_buffer;
    always @(posedge clk)
    begin
        if (past_valid)
        begin
            assert(use_data_in_buffer_prev == $past(use_data_in_buffer));
        end
    end

    /*always @(posedge clk)
    begin
        if (in_ready && out_ready)
            use_data_in_buffer <= 1'b0;
        else if (in_ready && !out_ready)
            use_data_in_buffer <= 1'b1;
    end*/

    // Mux the data and valid signal
    always @(*)
    begin
        if (use_data_in_buffer)
        begin
            out_valid = in_valid_delayed;
            out_data = data_buffer;
        end
        else
        begin
            out_valid = in_valid;
            out_data = in_data;
        end
    end
endmodule