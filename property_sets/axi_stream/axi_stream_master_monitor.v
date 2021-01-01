`default_nettype none

/*
 * A set of formal properties for the master port of AXI-Stream.
 * AXI4-Stream, Version 1.0, Issue A
 */

/*
 * Section 2.1 Signal list
 * Section 3.1 Default value signaling
 * Notes on defaults for specific signals in port list below
 */
module axi_stream_master_monitor #(
    parameter byte_width = 4,
    parameter id_width = 0,
    parameter dest_width = 0,
    parameter user_width = 0,
    // Section 3.1.5 Optional TDATA
    // no TDATA -> no TSTRB (but TKEEP can still exist)
    // TKEEP width when byte_width=0
    parameter keep_width = 0,

    parameter USE_ASYNC_RESET = 1'b0,
    // Section 2.2.1 Handshake process
    // Master cannot wait on TREADY to signal TVALID
    // Cycle count for TREADY to be kept low initially, after which TVALID should be high
    parameter MAX_DELAY_TREADY_NO_TVALID = 16
) (
    input wire clk,
    input wire resetn,

    input wire tvalid,
    // Section 3.1.1 Optional TREADY
    // Having a tready port is recommended
`ifndef VERILATOR
    input wire tready = 1'b1,
`else
    input wire tready,
`endif

    input wire [(8*byte_width-1):0] tdata,
    // Section 3.1.2 Optional TKEEP and TSTRB
    // TODO: fix optional value declarations
    input wire [(byte_width-1):0] tstrb,// = tkeep,
    input wire [(byte_width>0 ? (byte_width-1) : keep_width):0] tkeep,// = {(byte_width-1){1'b1}},

    // Section 3.1.3 Optional TLAST
    // Recommended default TLAST value situation-dependent
    input wire tlast,

    // Section 3.1.4 Optional TID, TDEST, and TUSER
    // Signals omitted by setting widths to 0
    input wire [(id_width-1):0] tid,
    input wire [(dest_width-1):0] tdest,
    input wire [(user_width-1):0] tuser

    // TODO add output signals for byte counts, etc.
);
`define TX_ASSERT assert
`define NOT_RESET_FOR_REGISTERED ($past(resetn) && (!USE_ASYNC_RESET || resetn))

    reg past_valid = 1'b0;
    always @(posedge clk)
        past_valid <= 1'b1;

    reg not_in_reset;

    /* 
     * If in async mode, reset is registered by async flip flop
     * If in sync mode, reset is registered by sync flip flop
     *
     * WARNING: Only use this in combinational blocks
     * Use in registered blocks makes this incorrect by a clock cycle delay
     * Use `NOT_RESET_FOR_REGISTERED for registered blocks
     */
    generate
        if (USE_ASYNC_RESET)
            always @(posedge clk or negedge resetn)
            begin
                if (!resetn)
                    not_in_reset <= 1'b0;
                else
                    not_in_reset <= resetn;
            end
        else
            always @(posedge clk)
            begin
                not_in_reset <= resetn;
            end
    endgenerate

    // TODO handle an asynchronous aresetn

    // Section 2.2.1 Handshake process

    // Once TVALID is asserted it must be held until TVALID && TREADY
    always @(posedge clk)
    begin
        // Write this as (TVALID falls implies previous data transfer or reset)
        if (past_valid && $fell(tvalid))
        begin
            `TX_ASSERT($past(tvalid && tready) || !`NOT_RESET_FOR_REGISTERED);
        end
    end

    // Master cannot wait on TREADY to signal TVALID
    // Property below modified from @awygle's suggestion
    generate
    if (MAX_DELAY_TREADY_NO_TVALID < 4096)
    begin
        reg f_ever_ready = 1'b0;
        reg [11:0] delay_counter = 0;
        always @(posedge clk)
        begin
            if (!resetn)
                f_ever_ready <= 1'b0;
            else if (tready)
                f_ever_ready <= 1'b1;
        end
        always @(posedge clk)
        begin
            // Else if check to prevent weirdness with overflow
            // 4096 cycles should be plenty enough though
            if (!resetn)
                delay_counter <= 0;
            else if (delay_counter < 12'hfff)
                delay_counter <= delay_counter + 1;
        end

        // Check that TVALID has been raised even if TREADY has been held low
        // In isolation, this checks the required property
        // In a full system (where TREADY may be tied high) a false hypothesis allows the property to pass vacuously
        always @(*)
        begin
            if (delay_counter == MAX_DELAY_TREADY_NO_TVALID
                    && !f_ever_ready)
                assert(tvalid);
        end
    end
    else
        $error("MAX_DELAY_TREADY_NO_TVALID too large");
    endgenerate

    // When TVALID && !TREADY, data signals must be stable
    always @(posedge clk)
    begin
        if (past_valid && `NOT_RESET_FOR_REGISTERED && $past(tvalid && !tready))
        begin
            if (byte_width > 0)
            begin
                `TX_ASSERT($stable(tdata));
                `TX_ASSERT($stable(tstrb));
            end
            if (byte_width > 0 || keep_width > 0)
                `TX_ASSERT($stable(tkeep));

            `TX_ASSERT($stable(tlast));

            if (id_width > 0)
                `TX_ASSERT($stable(tid));
            if (dest_width > 0)
                `TX_ASSERT($stable(tdest));
            if (user_width > 0)
                `TX_ASSERT($stable(tuser));
        end
    end

    // Section 2.7.1 Clock
    // Unlike regular AXI there is no requirement for no combinational paths

    // Section 2.7.2 Reset
    // "A master interface must only begin driving TVALID at a rising ACLK edge following a rising edge at which ARESETn is asserted HIGH."
    // This timing is handled by the definition of !not_in_reset above
    always @(*)
    begin
        if (!not_in_reset)
        begin
            `TX_ASSERT(!tvalid);
        end
    end

    // Section 2.4.3 TKEEP and TSTRB combinations
    // TSTRB can be asserted only if TKEEP is asserted
    always @(*)
    begin
        if (tvalid)
        begin
            `TX_ASSERT(!(~tkeep & tstrb));
        end
    end
endmodule
`undef TX_ASSERT
`undef NOT_RESET_FOR_REGISTERED