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
    parameter user_width = 0
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
);
    reg past_valid = 1'b0;
    always @(posedge clk)
        past_valid = 1'b1;

    // Section 2.2.1 Handshake process

    // Once TVALID is asserted it must be held until TVALID && TREADY
    always @(posedge clk)
    begin
        // Write this as (TVALID falls implies previous data transfer)
        if ($fell(tvalid))
        begin
            assume($past(tvalid && tready))
        end
    end

    // Master cannot wait on TREADY to signal TVALID
    // TODO write out the below statement in Yosys-readable SVA
    // assume possible((always !tready) && (eventually tvalid))

    // When TVALID && !TREADY, data signals must be stable
    always @(posedge clk)
    begin
        if (past_valid && $past(tvalid && !tready))
        begin
            assume($stable(tdata));
            assume($stable(tstrb));
            assume($stable(tkeep));
            assume($stable(tlast));
            // TODO may need to check nonzero widths first
            assume($stable(tid));
            assume($stable(tdest));
            assume($stable(tuser));
        end
    end

    // Section 2.7.1 Clock
    // Unlike regular AXI there is no requirement for no combinational paths

    // Section 2.7.2 Reset
    // TODO handle an asynchronous aresetn
    always @(posedge clk)
    begin
        assume(resetn || !tvalid); // aresetn asserted -> tvalid deasserted
    end

    // Section 2.4.3 TKEEP and TSTRB combinations
    // TSTRB can be asserted only if TKEEP is asserted
    always @(*)
    begin
        if (tvalid)
        begin
            assume(!(~tkeep & tstrb));
        end
    end
    
    // Section 3.1.5 Optional TDATA
    // no TDATA -> no TSTRB
    // XXX: this isn't really representable as a formal property
endmodule