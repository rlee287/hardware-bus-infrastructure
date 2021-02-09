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

    output reg [DATA_WIDTH-1:0] out_data,
    output wire out_valid,
    input wire out_ready
);
`ifdef FORMAL
    reg past_valid = 1'b0;
    always @(posedge clk)
        past_valid <= 1'b1;
`endif

    reg reset_asserted = 1'b0;
    generate
        if (USE_ASYNC_RESET)
            always @(posedge clk or posedge reset)
                if (reset)
                    reset_asserted <= 1'b1;
                else
                    reset_asserted <= reset;
        else
            always @(posedge clk)
                reset_asserted <= reset;
    endgenerate

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

    generate
        if (USE_ASYNC_RESET)
            // Correct reset behavior is done in comb process below
            always @(posedge clk or posedge reset)
            begin
                if (reset)
                    state <= EMPTY;
                else
                    state <= state_next;
            end
        else
            always @(posedge clk)
                state <= state_next;
    endgenerate

    // Sanity-check assertions to avoid breakage when refactoring
`ifdef FORMAL
    always @(*)
    begin
        assert(state != 2'b00);
        assert(state_next != 2'b00);
    end
    always @(posedge clk)
        // Avoid checking if async reset and reset asserted
        // That case is verified elsewhere
        if (past_valid && (!USE_ASYNC_RESET && !reset))
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
        if (reset)
            state_next = EMPTY;
        else
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
    end

    // Custom state encoding implies these should be simple wire connects
    assign in_ready = (state != FULL) && !reset_asserted;
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
    // Assert that valid data is flushed from stall buffer
    // Probably unneeded given verification state machine below
    /*reg stall_buffer_written = 1'b0;
    always @(posedge clk)
    begin
        if (fill)
            stall_buffer_written <= 1'b1;
        else if (flush || state == FULL)
            assert(stall_buffer_written);
    end*/

    // Assert that reset causes appropriate state change and non-ready
    always @(*)
    begin
        if (reset_asserted)
        begin
            assert(state == EMPTY);
            if (USE_ASYNC_RESET)
                assert(state_next == EMPTY);
            assert(!in_ready);
        end
    end
    
    // psl assert !out_valid until in_valid; + reset after reset;
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

    // Assert that there is no state change when no data flows
    always @(posedge clk)
    begin
        if (past_valid && !rx_occured && !tx_occured && !reset)
            assert($stable(state_next));
    end

    // Assert that empty/full states stall the correct channels
    always @(*)
    begin
        if (state == EMPTY)
            assert(!tx_occured);
        else if (state == FULL)
            assert(!rx_occured);
    end

    reg [3:0] rx_count = 0;
    reg [3:0] tx_count = 0;
    reg [3:0] rx_count_next = 0;
    reg [3:0] tx_count_next = 0;
    always @(*)
    begin
        if (reset)
        begin
            rx_count_next <= 0;
            tx_count_next <= 0;
        end
        else
        begin
            if (rx_occured)
                rx_count_next <= rx_count + 1;
            if (tx_occured)
                tx_count_next <= tx_count + 1;
        end
    end

    generate
        if (USE_ASYNC_RESET)
            // Correct reset behavior is done in comb process below
            always @(posedge clk or posedge reset)
            begin
                if (reset)
                begin
                    rx_count <= 0;
                    tx_count <= 0;
                    assert(rx_count_next == 0);
                    assert(tx_count_next == 0);
                end
                else
                begin
                    rx_count <= rx_count_next;
                    tx_count <= tx_count_next;
                end
            end
        else
            always @(posedge clk)
            begin
                rx_count <= rx_count_next;
                tx_count <= tx_count_next;
            end
    endgenerate

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
    // TODO: check that ordering is properly enforced
    always @(*)
    begin
        if (reset)
            verification_state_next <= 2'b00;
        else
        begin
            case (verification_state)
                2'b00:
                begin
                    if (handshake_index == rx_count && rx_occured)
                    begin
                        data_recv <= in_data;
                        if (fill)
                            verification_state_next <= 2'b01;
                        else
                        begin
                            assert(load || flow);
                            verification_state_next <= 2'b10;
                        end
                    end
                end
                2'b01:
                begin
                    assert(state == FULL);
                    assert(stall_data_buffer == data_recv);
                    if (flush)
                        verification_state_next <= 2'b10;
                end
                2'b10:
                begin
                    if (out_valid)
                    begin
                        assert(out_data == data_recv);
                        if (tx_occured)
                            verification_state_next <= 2'b00;
                    end
                end
            endcase
        end
        assert(verification_state <= 2'b10);
        assert(verification_state_next <= 2'b10);
    end

    always @(posedge clk)
    begin
        if (past_valid && verification_state == 2'b10)
            if($past(!reset) || (USE_ASYNC_RESET && !reset))
            begin
                if ($past(verification_state != 2'b10))
                    assert(state == BUSY);
                else
                    assert(state == BUSY || state == FULL);
            end
            else
                assert(state == EMPTY);
    end

    generate
        if (USE_ASYNC_RESET)
            // Correct reset behavior is done in comb process below
            always @(posedge clk or posedge reset)
            begin
                if (reset)
                begin
                    verification_state <= 2'b00;
                    assert(verification_state_next == 2'b00);
                end
                else
                    verification_state <= verification_state_next;
            end
        else
            always @(posedge clk)
                verification_state <= verification_state_next;
    endgenerate

    // Cover (only do cover in sync mode)
    // Make traces easier to read for cover
    reg in_data_cover_readable = 1'b1;
    localparam [DATA_WIDTH-1] incr_sized = 1;
    always @(posedge clk)
        if (past_valid && !(in_valid && !in_ready)
                && in_data != $past(in_data+incr_sized))
            in_data_cover_readable <= 1'b0;
    reg [3:0] cover_state = 4'h0;
    reg invalid_cover_state_happened = 1'b0;

    always @(posedge clk)
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