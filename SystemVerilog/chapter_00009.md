# Tasks and Functions

## Introduction
Tasks and functions enable code encapsulation and reuse, critical for:
- **Modular design** (break complex operations into manageable units)
- **Testbench development** (create reusable verification components)
- **RTL abstraction** (improve code readability and maintainability)


## Key Differences: Tasks vs Functions
| Feature                | Tasks                      | Functions                  |
|------------------------|----------------------------|----------------------------|
| **Timing Controls**    | Allowed (`#`, `@`, `wait`) | Prohibited                 |
| **Return Value**       | None (use output args)     | Mandatory (single value)   |
| **Call Hierarchy**     | Can call tasks & functions | Can only call functions    |
| **Execution Time**     | Can consume simulation time| Zero-time (combinational)  |
| **Typical Use**        | Testbench sequences        | Calculations, RTL logic    |


## Task Implementation

### Basic Structure
```SV
task [automatic] task_name (arguments);
  // Inputs: input [type] arg
  // Outputs: output [type] arg
  // Inouts: inout [type] arg
  begin
    // Code with optional timing controls
  end
endtask
```

### Example: Testbench Stimulus
```SV
module bus_controller;
  task generate_transaction(input logic [31:0] data, output logic ack);
    begin
      $display("[%0t] Sending data: 0x%h", $time, data);
      #10 ack = 1;        // Timing control allowed
      #5  ack = 0;
    end
  endtask

  initial begin
    logic acknowledgment;
    generate_transaction(32'hDEADBEEF, acknowledgment);  // Task call
  end
endmodule
```


## Function Implementation

### Basic Structure
```SV
function [automatic] [return_type] function_name (arguments);
  // Inputs: input [type] arg (default direction)
  // No output/inout allowed (except via return)
  begin
    // Pure calculation code
    return = expression;  // Alternative: function_name = expression
  end
endfunction
```

### Example: RTL Calculation
```SV
module alu;
  function automatic int parity_calc(input logic [7:0] data);
    // Returns 1 if odd number of 1s in data
    parity_calc = ^data;  // XOR reduction operator
  endfunction

  initial begin
    $display("Parity: %0d", parity_calc(8'b10110011));  // Output: 0
  end
endmodule
```


## Storage Classes: Static vs Automatic

| Characteristic       | Static                   | Automatic                 |
|----------------------|--------------------------|---------------------------|
| **Memory Allocation**| Persistent (global)      | Stack-based (per call)    |
| **Recursion Support**| No                       | Yes                       |
| **Default Behavior** | Tasks in modules         | Functions in classes      |

### Static Variable Pitfall
```SV
task counter();
  static int count = 0;  // Shared across all calls
  begin
    count++;
    $display("Call count: %0d", count);
  end
endtask

// First call: 1, Second call: 2 (Value persists)
```

### Automatic Task for Recursion
```SV
function automatic int factorial(input int n);
  if (n <= 1) factorial = 1;
  else        factorial = n * factorial(n-1);
endfunction

initial $display("5! = %0d", factorial(5));  // 120
```


## Advanced Features

### 1. Void Functions
```SV
function void print_status(input logic error);
  if (error) $display("Error detected!");
endfunction
```

### 2. Argument Directions
```SV
task automatic swap(ref int x, ref int y);  // Pass by reference
  int temp = x;
  x = y;
  y = temp;
endtask
```

### 3. Default Arguments
```SV
function int increment(input int val, input int delta=1);
  increment = val + delta;
endfunction

initial begin
  $display(increment(5));    // 6 (uses default delta)
  $display(increment(5,3));  // 8
end
```


## Best Practices

1. **RTL Design**
   - Use functions for combinational logic
   - Avoid tasks in synthesizable code

2. **Testbenches**
   - Use automatic storage for concurrent operations
   - Use tasks for protocol generation with timing

3. **Debugging**
   ```SV
   function int checksum(input bit [63:0] data);
     checksum = data ^ (data >> 32);
     $debug("Checksum calc: 0x%h", checksum);  // Special debug message
   endfunction
   ```


## Exercises

1. **Sum Task**
   Create a task that prints the sum of two integers.
   ```SV
   task sum_task(input int a, b);
     $display("Sum: %0d", a + b);
   endtask
   ```

2. **Product Function**
   Implement a function returning the product of two integers.
   ```SV
   function int multiply(input int x, y);
     multiply = x * y;
   endfunction
   ```

3. **Recursive Factorial**
   Create an automatic task calculating factorial.
   ```SV
   task automatic factorial_task(input int n, output int result);
     if (n <= 1) result = 1;
     else begin
       factorial_task(n-1, result);
       result *= n;
     end
   endtask
   ```

4. **Circle Area Function**
   Implement real-number area calculation (A = πr²).
   ```SV
   function real circle_area(input real radius);
     real PI = 3.1415926535;
     circle_area = PI * radius ** 2;
   endfunction
   ```

