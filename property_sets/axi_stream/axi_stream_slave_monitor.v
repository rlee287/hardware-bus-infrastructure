`default_nettype none

/*
 * Section 2.1 Signal list
 * Section 3.1 Default value signaling
 * Notes on defaults for specific signals in port list below
 */
module axi_stream_slave_monitor #(
    parameter byte_width = 4,
    parameter id_width = 0,
    parameter dest_width = 0,
    parameter user_width = 0,
    parameter USE_ASYNC_RESET = 1'b0
) (
    input wire clk,
    input wire resetn,

    input wire tvalid,
    // Section 3.1.1 Optional TREADY:
    // Having a tready port is recommended
    input wire tready = 1'b1,

    input wire [(8*byte_width-1):0] tdata,
    // Section 3.1.2 Optional TKEEP and TSTRB
    // TODO: fix optional value declarations
    input wire [(byte_width-1):0] tstrb,// = tkeep,
    input wire [(byte_width-1):0] tkeep,// = {(byte_width-1){1'b1}},

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
    reg past_valid = 1'b0;
    always @(posedge clk)
        past_valid <= 1'b1;

    wire in_reset;
    reg resetn_delayed;
    always @(posedge clk)
        resetn_delayed <= resetn;

    generate
        if (USE_ASYNC_RESET)
            assign in_reset = !resetn;
        else
            assign in_reset = !resetn_delayed;
    endgenerate

`define TX_ASSERT assume

    // TODO handle an asynchronous aresetn

    // Section 2.2.1 Handshake process

    // Once TVALID is asserted it must be held until TVALID && TREADY
    always @(posedge clk)
    begin
        // Write this as (TVALID falls implies previous data transfer or reset)
        if (past_valid && $fell(tvalid))
        begin
            `TX_ASSERT($past(tvalid && tready) || in_reset);
        end
    end

    // Master cannot wait on TREADY to signal TVALID
    // TODO write out the below statement in Yosys-readable SVA
    // `TX_ASSERT possible((always !tready) && (eventually tvalid))

    // When TVALID && !TREADY, data signals must be stable
    always @(posedge clk)
    begin
        if (past_valid && !in_reset && $past(tvalid && !tready))
        begin
            `TX_ASSERT($stable(tdata));
            `TX_ASSERT($stable(tstrb));
            `TX_ASSERT($stable(tkeep));
            `TX_ASSERT($stable(tlast));
            // TODO may need to check nonzero widths first
            `TX_ASSERT($stable(tid));
            `TX_ASSERT($stable(tdest));
            `TX_ASSERT($stable(tuser));
        end
    end

    // Section 2.7.1 Clock
    // Unlike regular AXI there is no requirement for no combinational paths

    // Section 2.7.2 Reset
    always @(posedge clk)
    begin
        if (past_valid)
        begin
            `TX_ASSERT(in_reset || !tvalid); // aresetn asserted -> tvalid deasserted
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
    
    // Section 3.1.5 Optional TDATA
    // no TDATA -> no TSTRB
    // XXX: this isn't really representable as a formal property
endmodule
`undef TX_ASSERT