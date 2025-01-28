# Procedural Blocks

## Introduction
Procedural blocks in SystemVerilog are used to describe the behavior of hardware. They include initial blocks, final blocks, and always blocks.

## Initial Blocks
Initial blocks are used to execute code once at the beginning of the simulation.

```SV
module initial_example;
  initial begin
    $display("This is an initial block.");
  end
endmodule
```

## Final Blocks
Final blocks are used to execute code once at the end of the simulation.

```SV
module final_example;
  final begin
    $display("This is a final block.");
  end
endmodule
```

## Always Blocks
Always blocks are used to describe behavior that should be executed repeatedly.

### `always`
The `always` block executes code continuously.

```SV
module always_example;
  logic clk;
  always begin
    #5 clk = ~clk;
  end
endmodule
```

### `always_comb`
The `always_comb` block is used to describe combinational logic.

```SV
module always_comb_example;
  logic a, b, c;
  always_comb begin
    c = a & b;
  end
endmodule
```

### `always_ff`
The `always_ff` block is used to describe sequential logic.

```SV
module always_ff_example;
  logic clk, reset, q, d;
  always_ff @(posedge clk or posedge reset) begin
    if (reset)
      q <= 0;
    else
      q <= d;
  end
endmodule
```

### `always_latch`
The `always_latch` block is used to describe latch behavior.

```SV
module always_latch_example;
  logic enable, q, d;
  always_latch begin
    if (enable)
      q <= d;
  end
endmodule
```

## Assignments
Assignments in SystemVerilog can be blocking or non-blocking.

### Blocking Assignments
Blocking assignments are executed sequentially.

```SV
module blocking_example;
  int a, b;
  initial begin
    a = 1;
    b = a + 1;
    $display("a: %0d, b: %0d", a, b);
  end
endmodule
```

### Non-blocking Assignments
Non-blocking assignments are executed concurrently.

```SV
module nonblocking_example;
  int a, b;
  initial begin
    a <= 1;
    b <= a + 1;
    #1 $display("a: %0d, b: %0d", a, b);
  end
endmodule
```

## Exercises
1. Use an initial block to display a message at the beginning of the simulation.
2. Use a final block to display a message at the end of the simulation.
3. Use an always block to generate a clock signal.
4. Use an always_comb block to describe combinational logic.
5. Use an always_ff block to describe a flip-flop.
6. Use an always_latch block to describe a latch.
7. Use blocking assignments to perform sequential operations.
8. Use non-blocking assignments to perform concurrent operations.

## Conclusion
Procedural blocks in SystemVerilog provide powerful tools for describing the behavior of hardware. Understanding these blocks is essential for writing efficient and effective hardware models and testbenches.
