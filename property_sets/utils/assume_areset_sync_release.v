`default_nettype none

module assume_areset_sync_release #(
    parameter reset_inverted = 1'b1
) (
    input wire clk,
    input wire async_reset
);
    wire reset_asserted;
    generate
        if (reset_inverted)
            assign reset_asserted = !async_reset;
        else
            assign reset_asserted = async_reset;
    endgenerate

    (* gclk *) reg formal_timestep;

    always @(posedge formal_timestep)
    begin
        if ($fell(reset_asserted))
        begin
            assume($rose(clk));
        end
    end
endmodule