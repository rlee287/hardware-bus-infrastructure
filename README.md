# Hardware Bus Infrastructure

## Introduction

The goal of this project is to develop formal verification properties for various bus standards, write documents to assist people in using these busses, and create verified example cores and infrastructure (e.g. interconnects) based on these properties. Lowering the entry barrier for formal verification will allow more people to write HDL modules with the guarantee that they will work properly.

## Status Table

Key to emojis:

 * :x: : Item is not started
 * :heavy_minus_sign: : Item is in progress
 * :heavy_plus_sign: : Item is completed but has not been 
 * :heavy_check_mark: : Item is completed and has been tested sufficiently

All entries may contain an issue number tracking progress on the item.

Item | Wishbone 4 Classic | Wishbone 4 Pipelined | AXI4-Stream | AXI4-Lite | AXI4
---- | ------------------ | -------------------- | ----------- | --------- | ----
Formal Property Set (SVA) | :x: | :x: | :heavy_plus_sign: (#1, #3, #4) | :x: | :x:
Formal Property Set (PSL) | :x: | :x: | :heavy_minus_sign: (#1, awaiting #3 merge) | :x: | :x:
Bus Summary | :x: | :x: | :x: | :x: | :x:
Example Cores (expand list later) | :x: | :x: | :x: (#5) | :x: | :x:

## Bus Standards

This repository has (or will have) the following busses:

 * [Wishbone 4](https://cdn.opencores.org/downloads/wbspec_b4.pdf)
 * [AXI4-Stream](https://static.docs.arm.com/ihi0051/a/IHI0051A_amba4_axi4_stream_v1_0_protocol_spec.pdf)
 * [AXI4-Lite and AXI4](https://static.docs.arm.com/ihi0022/fb/IHI0022F_b_amba_axi_protocol_spec.pdf)

## Document Types

### Formal Property Sets

Formal property sets use a "monitor" type bus in which all bus signals are inputs, and assert properties over the inputs. These check whether an implementation of a bus is standards-compliant, so all assertions and assumptions must have a comment next to them pointing to the clause in the standards document justifying them. These modules may also have outputs tracking useful bus data (e.g. number of bytes transferred).

In order to support open source projects, SVA properties should work with the open-source version of Yosys, and PSL properties should work with GHDL. (PSL units should be written to work with other open-source tools that supports PSL, but I am not currently aware of any open-source tools besides GHDL that use PSL.)

### Bus Summary

Bus summaries are non-code documents that summarize the signals of a bus and the properties that should hold on them, as well as recommendations on using the bus effectively. They are a quick reference document and should be easier to read than the original standards document. To ensure accuracy, descriptions of the bus should have a reference to the original specification.

### Example Cores

Example cores demonstrate how to implement a core with bus interface(s) and must be formally verified using a formal property set. Because their goal is to help other developers use these bus standards, they should be written for readability. Example cores should be written for highest bus performance, but may also have options to trade performance against simplicity. For example, an AXI example core should be written for 100% throughput, but it can have a parameter to limit it to 50% throughput and remove the need for skid buffers.
