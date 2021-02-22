`default_nettype none

/*
 * A skid buffer for buffering data in valid/ready handshakes
 * Useful for writing high-throughput AXI/AXI-Lite/AXI-Stream cores
 * Based on the design of http://fpgacpu.ca/fpga/Pipeline_Skid_Buffer.html
 */
module skid_buffer_async #(
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

    reg past_reset = 1'b0;
    always @(posedge clk or posedge reset)
    begin
        if (reset)
            past_reset <= 1'b1;
        else
            past_reset <= reset;
    end

    wire rx_occured;
    wire tx_occured;
    assign rx_occured = (in_valid && in_ready);
    assign tx_occured = (out_valid && out_ready);

    // Hand-optimized FSM encoding
    localparam [1:0] EMPTY = 2'b10;
    localparam [1:0] BUSY = 2'b11;
    localparam [1:0] FULL = 2'b01;

    reg [1:0] state = EMPTY;
    reg [1:0] state_next = EMPTY;

    always @(posedge clk or posedge reset)
    begin
        if (reset)
            state <= EMPTY;
        else
            state <= state_next;
    end

    // Sanity-check assertions to avoid breakage when refactoring
`ifdef FORMAL
    always @(*)
    begin
        assert(state != 2'b00);
        assert(state_next != 2'b00);
    end
    always @(posedge clk)
        if (past_valid && $past(!reset) && !reset)
            assert(state == $past(state_next));
`endif

    // Each wire is a particular edge in the state machine
    wire load; // Empty datapath inserts data into output register.
    wire flow; // New inserted data into output register as the old data is removed.
    wire fill; // New inserted data into buffer register. Data not removed from output register.
    wire flush; // Move data from buffer register into output register. Remove old data. No new data inserted.
    wire unload; // Remove data from output register, leaving the datapath empty.

    assign load = (state == EMPTY) && (rx_occured == 1'b1) && (tx_occured == 1'b0);
    assign flow = (state == BUSY) && (rx_occured == 1'b1) && (tx_occured == 1'b1);
    assign fill = (state == BUSY) && (rx_occured == 1'b1) && (tx_occured == 1'b0);
    assign flush = (state == FULL) && (rx_occured == 1'b0) && (tx_occured == 1'b1);
    assign unload = (state == BUSY) && (rx_occured == 1'b0) && (tx_occured == 1'b1);

`ifdef FORMAL
    wire [4:0] fsm_aggregate;
    assign fsm_aggregate = {load, flow, fill, flush, unload};
    // Sanity check: assert that at most one edge is active
    // Yosys doesn't support $onehot0 so we expand it manually
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
    assign in_ready = (state != FULL) && !past_reset;
    assign out_valid = (state != EMPTY);

    //reg [DATA_WIDTH-1:0] out_data_buffer;
    reg [DATA_WIDTH-1:0] stall_data_buffer;

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
    // Assert that reset causes appropriate state change and non-ready
    always @(*)
    begin
        if (past_reset)
        begin
            assert(state == EMPTY);
            assert(!in_ready);
        end
    end
    
    // psl assert !out_valid until in_valid; + reset after reset;
    reg in_ever_valid = 1'b0;
    reg out_ever_valid = 1'b0;
    always @(posedge clk or posedge reset)
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

    // Assert that there is no state change when no data flows
    always @(posedge clk)
    begin
        if (past_valid && $past(!rx_occured && !tx_occured) && $past(!reset) && !reset)
            assert($stable(state));
    end

    // Assert that empty/full states stall the correct channels
    always @(*)
    begin
        if (state == EMPTY)
        begin
            assert(!tx_occured);
        end
        else
        if (state == FULL)
        begin
            assert(!rx_occured);
        end
    end

    reg [3:0] rx_count = 0;
    reg [3:0] tx_count = 0;
    always @(posedge clk or posedge reset)
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
            else
                rx_count <= rx_count;
            if (tx_occured)
                tx_count <= tx_count + 1;
            else
                tx_count <= tx_count;
        end
    end

    wire [3:0] rx_tx_diff;
    assign rx_tx_diff = rx_count - tx_count;

    always @(*)
    begin
        // Signed overflow means maximum diff value, which triggers assert
        // No need to make diff signed and assert >= 0
        assert(rx_tx_diff <= 2);
        case (rx_tx_diff)
            0: assert(state == EMPTY);
            1: assert(state == BUSY);
            2: assert(state == FULL);
        endcase
    end

    (* anyconst *) reg [3:0] handshake_index;
    reg [DATA_WIDTH-1:0] data_recv;
    reg [1:0] verification_state = 2'b00;
    reg [1:0] verification_state_next = 2'b00;

    // Record nth data packet input (where n is an arbitrary constant)
    // n being arbitrary should also enforce ordering constraints
    always @(*)
    begin
        // Default assign
        verification_state_next = verification_state;
        case (verification_state)
            2'b00:
            begin
                if (handshake_index == rx_count && rx_occured)
                begin
                    // Do assign in separate clocked process
                    //data_recv <= in_data;
                    if (fill)
                        verification_state_next = 2'b01;
                    else
                    begin
                        assert(load || flow);
                        verification_state_next = 2'b10;
                    end
                end
            end
            2'b01:
            begin
                assert(state == FULL);
                assert(stall_data_buffer == data_recv);
                if (flush)
                    verification_state_next = 2'b10;
            end
            2'b10:
            begin
                if (out_valid)
                begin
                    assert(out_data == data_recv);
                    if (tx_occured)
                        verification_state_next = 2'b00;
                end
            end
        endcase
        assert(verification_state <= 2'b10);
        assert(verification_state_next <= 2'b10);
    end

    always @(posedge clk)
        if (verification_state == 2'b00 && (fill || flow || load))
            data_recv <= in_data;

    always @(posedge clk)
    begin
        if (past_valid && verification_state == 2'b10)
            if($past(!reset) && !reset)
            begin
                if ($past(verification_state != 2'b10))
                begin
                    assert(state == BUSY);
                end
                else
                begin
                    assert(state == BUSY || state == FULL);
                end
            end
            else
                assert(state == EMPTY);
    end

    always @(posedge clk or posedge reset)
    begin
        if (reset)
            verification_state <= 2'b00;
        else
            verification_state <= verification_state_next;
    end

    // Cover
    // Make traces easier to read for cover
    reg in_data_cover_readable = 1'b1;
    localparam [DATA_WIDTH-1:0] incr_sized = 1;
    always @(posedge clk)
        if (past_valid && !(in_valid && !in_ready)
                && in_data != $past(in_data+incr_sized))
            in_data_cover_readable <= 1'b0;
    reg [3:0] cover_state = 4'h0;
    reg invalid_cover_state_happened = 1'b0;

    always @(posedge clk or posedge reset)
    begin
        if (reset)
            cover_state <= 4'h0;
        else
        begin
            case (cover_state)
                4'h0:
                begin
                    if (fill)
                        cover_state <= 4'h1;
                    else if (unload)
                        cover_state <= 4'h8;
                end
                4'h1:
                    if (flush)
                        cover_state <= 4'h2;
                4'h2:
                    if (flow)
                        cover_state <= 4'h3;
                4'h3:
                    if (flow)
                        cover_state <= 4'h0;
                4'h8:
                    if (unload)
                        cover_state <= 4'h9;
                4'h9:
                    if (load)
                        cover_state <= 4'ha;
                4'ha:
                    if (flow)
                        cover_state <= 4'h0;
                default: invalid_cover_state_happened <= 1'b1;
            endcase
        end
    end

    always @(posedge clk)
    begin
        assert(!invalid_cover_state_happened);
        if (past_valid && $past(!reset) && !reset && cover_state == 4'h0)
        begin
            cover($past(cover_state == 4'h3) && in_data_cover_readable);
            cover($past(cover_state == 4'ha) && in_data_cover_readable);
        end
    end
`endif
endmodule