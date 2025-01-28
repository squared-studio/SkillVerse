# Icarus Verilog

## Introduction
**Icarus Verilog** is an open-source implementation of the Verilog hardware description language. It is a compiler that generates netlists in the desired format (EDIF) and a simulator. It supports the 1995, 2001, and 2005 versions of the standard, portions of SystemVerilog, and some extensions.

The Icarus Verilog compiler, `iverilog`, reads and interprets the source file, then generates a compiled result. The compiled form may be selected by command-line switches, but the default is the `vvp` format, which is run later, as needed. The `vvp` command is the simulation runtime engine.

A Verilog program for simulation is often divided into two major parts: the device under test and the test bench. The test bench is mostly Verilog code that stimulates the device under test and observes the behavior of the simulation.

Icarus Verilog does the practical work of using Verilog; it collects all the written source code of the Verilog design, checks for coding errors, and writes compiled design files. It helps access source files collected into libraries, link together modules spread throughout source files, and write compiled results.

## Install
```bash
sudo apt update
sudo apt-get -y install iverilog
```

## Simple Exercise

**Create the AND gate (and_gate.v)**
```SV
module and_gate (input wire a, b, output wire out);
    assign out = a & b;
endmodule
```
This is a simple AND gate with two inputs a and b, and one output out. The output is the result of the bitwise AND operation on the inputs.

**Create the Testbench (and_gate_tb.v)**
```SV
module and_gate_tb;
    reg a, b;
    wire out;

    // Instantiate the AND gate
    and_gate u1 (.a(a), .b(b), .out(out));

    initial begin
        // Test all possible input combinations
        a = 0; b = 0; #10;
        a = 0; b = 1; #10;
        a = 1; b = 0; #10;
        a = 1; b = 1; #10;

        // Finish the simulation
        $finish;
    end

    initial begin
        $monitor("a = %b, b = %b, out = %b", a, b, out);
    end
endmodule
```
This is a testbench for the AND gate. It applies all possible combinations of inputs to the AND gate and monitors the output.

**Compile and Run the Simulation**
```bash
iverilog -o and_gate_tb.vvp and_gate.v and_gate_tb.v
vvp and_gate_tb.vvp
```
This will compile the Verilog files into a format that can be executed by the vvp command. Add `-g2012` to the `iverilog` command if you add SystemVerilog files. The vvp command runs the simulation and prints the output to the console.

More command arguments are available. Add `-help` to the respective command for details.
