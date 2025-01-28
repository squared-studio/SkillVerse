# Task 7 : Xilinx Vivado

## Introduction
**AMD Vivado** is a comprehensive design software suite for synthesis and analysis of hardware description language (HDL) designs. It is specifically designed for AMD adaptive SoCs and FPGAs. The suite includes various tools for **Design Entry**, **Synthesis**, **Place and Route**, and **Verification/Simulation**. These tools enable faster design iterations and help in quickly meeting your FMAX targets. Vivado brings unique features such as **Report QoR Assessment (RQA)**, **Report QoR Suggestions (RQS)**, and **Intelligent Design Runs (IDR)**. These features help you close timing and converge on your performance goals in days instead of weeks, resulting in significant productivity gains. Moreover, Vivado supports design entry in traditional HDL like VHDL and Verilog. It also supports a graphical user interface-based tool called the **IP Integrator (IPI)** that allows for a Plug-and-Play IP Integration Design Environment.
In summary, AMD Vivado is a powerful tool that helps hardware designers reduce compile times and design iterations, while more accurately estimating power for AMD adaptive SoCs and FPGAs.

## Install
**`TODO`** : Ubuntu Example

## Simple Exercise
Reuse the `and_gate.v` and `and_gate_tb.v` for previous Task 5 and run it using Vivado Simulator

**Compile and Run the Simulation**
```bash
xvlog and_gate.v and_gate_tb.v
xelab and_gate_tb -s top
xsim top -runall
```
The `xvlog` command compiles the Verilog files and does lint check. Add `-sv` flag to the `xvlog` command if there are SystemVerilog file. Then the `xelab` command elaborates the top module and prepares executable. Finally the `xsim` command runs the simulation executable.

More command arguments are available. Add `-help` to the respective command for details.
