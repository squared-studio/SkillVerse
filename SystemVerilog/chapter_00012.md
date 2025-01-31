# Modules

## Introduction
Modules in SystemVerilog are the basic building blocks of a design. They encapsulate functionality and can be instantiated to create hierarchical designs.

## Module Definition
Modules are defined using the `module` keyword.

### Example
```SV
module simple_module;
  // Module contents
endmodule
```

## Ports and Parameters
Modules can have ports for input and output signals, and parameters for configuration.

### Example
```SV
module parameterized_module #(parameter WIDTH = 8) (
  input logic clk,
  input logic rst,
  input logic [WIDTH-1:0] data_in,
  output logic [WIDTH-1:0] data_out
);
  // Module contents
endmodule
```

## Instantiating Modules
Modules can be instantiated within other modules to create hierarchical designs.

### Example
```SV
module top;
  logic clk;
  logic rst;
  logic [7:0] data_in;
  logic [7:0] data_out;

  parameterized_module #(.WIDTH(8)) uut (
    .clk(clk),
    .rst(rst),
    .data_in(data_in),
    .data_out(data_out
  );

  initial begin
    clk = 0;
    rst = 1;
    #5 rst = 0;
    forever #5 clk = ~clk;
  end
endmodule
```

## Hierarchical Design
Modules can be connected to create complex hierarchical designs.

### Example
```SV
module submodule (
  input logic clk,
  input logic rst,
  input logic [7:0] data_in,
  output logic [7:0] data_out
);
  always_ff @(posedge clk or posedge rst) begin
    if (rst)
      data_out <= 8'b0;
    else
      data_out <= data_in;
  end
endmodule

module top;
  logic clk;
  logic rst;
  logic [7:0] data_in;
  logic [7:0] data_out;

  submodule sub (
    .clk(clk),
    .rst(rst),
    .data_in(data_in),
    .data_out(data_out)
  );

  initial begin
    clk = 0;
    rst = 1;
    #5 rst = 0;
    forever #5 clk = ~clk;
  end
endmodule
```

## Exercises
1. Define a simple module with input and output ports.
2. Create a parameterized module and instantiate it with different parameter values.
3. Connect multiple modules to create a hierarchical design.
4. Use an initial block to generate a clock signal and reset signal for the modules.

