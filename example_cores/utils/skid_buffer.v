`default_nettype none

/*
 * A skid buffer for buffering data in valid/ready handshakes
 * Useful for writing high-throughput AXI/AXI-Lite/AXI-Stream cores
 * Based on the design of http://fpgacpu.ca/fpga/Pipeline_Skid_Buffer.html
 */
module skid_buffer #(
    parameter DATA_WIDTH = 32
) (
    input wire clk,
    input wire reset,

    input wire [DATA_WIDTH-1:0] in_data,
    input wire in_valid,
    output wire in_ready,

    output reg [DATA_WIDTH-1:0] out_data,
    output wire out_valid,
    input wire out_ready
);
`ifdef FORMAL
    reg past_valid = 1'b0;
    always @(posedge clk)
        past_valid <= 1'b1;
`endif

    wire rx_data;
    wire tx_data;
    assign rx_data = (in_valid && in_ready);
    assign tx_data = (out_valid && out_ready);

    // Hand-optimized FSM encoding
    localparam [1:0] EMPTY = 2'b10;
    localparam [1:0] BUSY = 2'b11;
    localparam [1:0] FULL = 2'b01;

    reg [1:0] state = EMPTY;
    reg [1:0] state_next = EMPTY;

    always @(posedge clk)
        state <= state_next;

    // Sanity-check assertions to avoid breakage when refactoring
`ifdef FORMAL
    always @(*)
    begin
        assert(state != 2'b00);
        assert(state_next != 2'b00);
    end
    always @(posedge clk)
        if (past_valid)
            assert(state == $past(state_next));
`endif

    // Each wire is a particular edge in the state machine
    wire load; // Empty datapath inserts data into output register.
    wire flow; // New inserted data into output register as the old data is removed.
    wire fill; // New inserted data into buffer register. Data not removed from output register.
    wire flush; // Move data from buffer register into output register. Remove old data. No new data inserted.
    wire unload; // Remove data from output register, leaving the datapath empty.

    assign load = (state == EMPTY) && (rx_data == 1'b1) && (tx_data == 1'b0);
    assign flow = (state == BUSY) && (rx_data == 1'b1) && (tx_data == 1'b1);
    assign fill = (state == BUSY) && (rx_data == 1'b1) && (tx_data == 1'b0);
    assign flush = (state == FULL) && (rx_data == 1'b0) && (tx_data == 1'b1);
    assign unload = (state == BUSY) && (rx_data == 1'b0) && (tx_data == 1'b1);

`ifdef FORMAL
    wire [4:0] fsm_aggregate;
    assign fsm_aggregate = {load, flow, fill, flush, unload};
    always @(*)
        //assert($onehot0({load, flow, fill, flush, unload}));
        assert(fsm_aggregate == 5'b00000
            || fsm_aggregate == 5'b10000
            || fsm_aggregate == 5'b01000
            || fsm_aggregate == 5'b00100
            || fsm_aggregate == 5'b00010
            || fsm_aggregate == 5'b00001);
`endif

    always @(*)
    begin
        state_next = state; // Default: keep current state
        case (state)
            EMPTY:
                if (load)
                    state_next = BUSY;
            BUSY:
                if (fill)
                    state_next = FULL;
                else if (unload)
                    state_next = EMPTY;
            FULL:
                if (flush)
                    state_next = BUSY;
            // default should never happen, by assert above
        endcase
    end

    // Custom state encoding implies these should be simple wire connects
    assign in_ready = (state != FULL);
    assign out_valid = (state != EMPTY);

    //reg [DATA_WIDTH-1:0] out_data_buffer;
    reg [DATA_WIDTH-1:0] stall_data_buffer;

`ifdef FORMAL
    reg stall_buffer_written = 1'b0;
`endif

    always @(posedge clk)
    begin
        if (flush)
        begin
            out_data <= stall_data_buffer;
        end
        else if (load || flow)
            out_data <= in_data;
    end
    always @(posedge clk)
    begin
        if (fill)
        begin
            stall_data_buffer <= in_data;
        end
    end

`ifdef FORMAL
    always @(posedge clk)
    begin
        if (fill)
            stall_buffer_written <= 1'b1;
        else if (flush)
            assert(stall_buffer_written);
    end

    always @(posedge clk)
    begin
        if (past_valid && !rx_data && !tx_data)
            assert($stable(state_next));
    end

    always @(*)
    begin
        if (state == EMPTY)
            assert(!tx_data);
        else if (state == FULL)
            assert(!rx_data);
    end
`endif
endmodule