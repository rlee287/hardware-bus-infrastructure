#!/bin/sh
diff_output=$(diff axi_stream_master_monitor.v axi_stream_slave_monitor.v)
echo "$diff_output" | diff - axis_m_to_s_diff.diff > /dev/null

# Use true and false to avoid exiting the shell if this script is sourced
if [ $? -eq 0 ]; then
    echo "AXI-Stream property pairs match"
    true
else
    echo "AXI-Stream property pairs differ"
    echo "$diff_output"
    false
fi
