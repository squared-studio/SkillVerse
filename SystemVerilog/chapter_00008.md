# Procedural Blocks

## Introduction
Procedural blocks form the core of behavioral modeling in SystemVerilog, enabling description of hardware operations, testbench initialization, and simulation control. Unlike continuous assignments, these blocks execute **sequentially** (top-to-bottom) and are essential for modeling registers, state machines, and complex digital logic.


## Initial Blocks
Execute code **once at simulation start** (time 0). Primarily used for:
- Testbench initialization
- Signal stimulation
- One-time configuration

**Key Characteristics**:
- Multiple initial blocks execute **concurrently**
- Not synthesizable (testbench-only)

```SV
module tb;
  logic start;
  initial begin
    start = 0;
    #10 start = 1;       // Toggle after 10 time units
    $display("Simulation started at t=%0t", $time);
  end
endmodule
```


## Final Blocks
Execute code **once at simulation termination**. Used for:
- Reporting final results
- Closing files
- Cleaning up resources

**Key Characteristics**:
- Runs after all initial blocks complete
- Not synthesizable

```SV
module stats;
  int error_count;
  final begin
    $display("\nSimulation ended with %0d errors", error_count);
    $fclose(log_file);
  end
endmodule
```


## Always Blocks
Execute code **repeatedly** based on sensitivity lists. Critical for RTL design.

### 1. General `always` Block
- **Continuous execution** (use with timing controls)
- Primarily for testbench clock generation

```SV
module clock_gen;
  logic clk = 0;
  always #5 clk = ~clk;  // 10-unit period clock
endmodule
```

### 2. `always_comb` Block
- **Combinational logic** inference
- Auto-generates sensitivity list
- Executes once at time 0

```SV
module alu(
  input  logic [3:0] a, b,
  output logic [3:0] result
);
  always_comb begin
    result = a + b;      // Recomputed when a or b changes
  end
endmodule
```

### 3. `always_ff` Block
- **Flip-flop/register** inference
- Requires explicit sensitivity list
- Use non-blocking assignments (`<=`)

```SV
module d_ff(
  input  logic clk, rst_n, d,
  output logic q
);
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) q <= 0;   // Async reset
    else        q <= d;   // Clock-driven update
  end
endmodule
```

### 4. `always_latch` Block
- **Latch** inference
- Requires conditional assignments
- Use sparingly (latches can cause timing issues)

```SV
module latch(
  input  logic enable, data,
  output logic q
);
  always_latch begin
    if (enable) q = data;  // Transparent when enabled
  end
endmodule
```


## Assignment Types

### Blocking Assignments (`=`)
- **Sequential execution**
- Immediate value update
- Use in combinational logic and testbenches

```SV
module blocking_ex;
  int x, y;
  initial begin
    x = 5;        // x updated immediately
    y = x + 3;    // Uses x=5 → y=8
  end
endmodule
```

### Non-Blocking Assignments (`<=`)
- **Concurrent execution**
- Updates scheduled after time step
- Use in sequential logic

```SV
module nonblocking_ex;
  logic [1:0] a, b;
  initial begin
    a <= 2'b10;   // Scheduled update
    b <= a;       // Uses original a value
    #1 $display("a=%b, b=%b", a, b);  // Output: a=10, b=00
  end
endmodule
```


## Best Practices & Pitfalls

1. **Synthesis Guidelines**:
   - Use `always_comb` for combinational logic
   - Use `always_ff` for flip-flops
   - Avoid general `always` in RTL design

2. **Latch Prevention**:
   ```SV
   // Bad: Inferred latch (missing else)
   always_comb begin
     if (enable) q = data;
   end

   // Good: Full combinational logic
   always_comb begin
     q = (enable) ? data : '0;
   end
   ```

3. **Sensitivity Lists**:
   - `always_ff`: Include all async signals (reset/clock)
   - `always_comb`: No manual sensitivity list needed

4. **Assignment Mixing**:
   - Never mix blocking/non-blocking in same block
   - Non-blocking for sequential, blocking for combinational


## Exercises

1. **Initial Block Message**:
   Print "System Initializing..." at simulation start.

2. **Final Block Summary**:
   Report total simulation time at end using `$time`.

3. **Clock Generator**:
   Create a 100MHz clock (50% duty cycle) using `always`.

4. **Combinational Multiplier**:
   Implement 8-bit multiplication with `always_comb`.

5. **Synchronous Counter**:
   Design a 4-bit counter with `always_ff` and async reset.

6. **Latch Implementation**:
   Create a transparent latch with `always_latch`.

7. **Blocking vs Non-blocking**:
   Demonstrate value swapping using both assignment types.

