# Task 6 : GNU Make

## Introduction
GNU Make is a powerful tool that automates the process of building executable programs and libraries from source code. It's a build automation tool that was designed to manage dependencies in your project. 

The `make` utility reads a file (commonly referred to as a `Makefile`) that describes the relationships among files in your program, and the commands needed to derive the target program from its source files. When a source file has been changed, `make` uses the rules specified in the `Makefile` to determine which parts of the program need to be recompiled, and then it recompiles only those parts.

GNU Make is a standard part of most Unix-like operating systems, but it's also available for Windows and other systems. It's widely used in software development for tasks such as compiling large programs, but it can also be used to manage and automate many other types of tasks.

One of the key advantages of GNU Make is that it allows developers to compile only those files that have changed since the last compile, saving a significant amount of time on large projects. It's also highly flexible and configurable, which makes it a powerful tool for managing complex projects.

## Install
```bash
sudo apt update
sudo apt-get -y install make
```

## Simple Exercise

**A simple Makefile for compiling and running the previous Icarus Verilog simulation**
```mk
# Variables
MODULES = and_gate.v and_gate_tb.v
OUTPUT = and_gate_tb.vvp

# Default target
all: $(OUTPUT)

# Compile the Verilog files
$(OUTPUT): $(MODULES)
	iverilog -o $(OUTPUT) $(MODULES)

# Run the simulation
run: $(OUTPUT)
	vvp $(OUTPUT)

# Clean the output files
clean:
	rm -f $(OUTPUT)

.PHONY: all run clean
```

This `Makefile` has three targets: `all`, `run`, and `clean`. The `all` target is the default target, which compiles the Verilog files into a format that can be executed by the `vvp` command. The `run` target runs the simulation and prints the output to the console. The `clean` target removes the output files.

You can use the following commands to compile and run the simulation:

- To compile the Verilog files, use the command `make`.
- To run the simulation, use the command `make run`.
- To clean the output files, use the command `make clean`.
