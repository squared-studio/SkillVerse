# RTL Modeling Techniques

## Combinational Logic in SystemVerilog
Combinational logic in SystemVerilog is modeled using continuous assignments and procedural blocks. The `assign` statement is used for continuous assignments, while `always_comb` blocks are used for procedural assignments.

## Sequential Logic in SystemVerilog
Sequential logic is modeled using `always_ff` blocks in SystemVerilog. These blocks are triggered by clock edges and are used to describe flip-flops and registers.

## Synchronous vs Asynchronous Design
- **Synchronous Design**: All operations are synchronized with a clock signal. This approach simplifies timing analysis and ensures predictable behavior.
- **Asynchronous Design**: Operations are not synchronized with a clock signal. This approach can lead to faster designs but requires careful handling of timing issues.

## Examples

### Example 1: Combinational Logic in SystemVerilog
```SV
module mux_2to1 (
    input logic a,
    input logic b,
    input logic sel,
    output logic y
);
    assign y = sel ? b : a;
endmodule
```

### Example 2: Sequential Logic in SystemVerilog
```SV
module shift_register (
    input logic clk,
    input logic reset,
    input logic d,
    output logic [3:0] q
);
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            q <= 4'b0000;
        else
            q <= {q[2:0], d};
    end
endmodule
```

### Example 3: Synchronous vs Asynchronous Design
#### Synchronous Design
```SV
module sync_reset (
    input logic clk,
    input logic reset,
    output logic q
);
    always_ff @(posedge clk) begin
        if (reset)
            q <= 1'b0;
        else
            q <= ~q;
    end
endmodule
```

#### Asynchronous Design
```SV
module async_reset (
    input logic clk,
    input logic reset,
    output logic q
);
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            q <= 1'b0;
        else
            q <= ~q;
    end
endmodule
```

## Exercises

1. Write a SystemVerilog module to implement a 4-bit adder using combinational logic.
2. Design a 4-bit register using sequential logic in SystemVerilog.
3. Compare the advantages and disadvantages of synchronous and asynchronous design.
