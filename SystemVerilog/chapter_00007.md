# Control Flow

## Introduction
Control flow statements in SystemVerilog dictate the order in which statements are executed, enabling dynamic decision-making and repetitive operations. These constructs are fundamental for creating testbenches, modeling hardware behavior, and implementing algorithms. Proper use of control flow ensures efficient and readable code, critical for both simulation and synthesis.


## Conditional Statements
Conditional statements execute code blocks based on boolean conditions.

### `if-else` Statement
Executes a block if a condition is `true`, with optional `else if` and `else` clauses.

**Key Points**:
- Use `else if` for multiple mutually exclusive conditions.
- Braces `begin` `end` are optional for single-line blocks but recommended for clarity.

```SV
module if_else_example;
  int num = 42;
  initial begin
    if (num > 50) begin
      $display("%0d is greater than 50", num);
    end else if (num > 30) begin
      $display("%0d is between 31 and 50", num);  // This block executes
    end else begin
      $display("%0d is 30 or lower", num);
    end
  end
endmodule
```


## Case Statements
Select one branch from multiple options based on a variable's value.

### 1. `case`
- Matches **exact values** (no wildcards).
- Always include a `default` case to avoid unintended latches in synthesis.

```SV
module case_example;
  logic [2:0] day = 3'd3;
  initial begin
    case (day)
      3'd1: $display("Monday");
      3'd2: $display("Tuesday");
      3'd3: $display("Wednesday");  // Matches this case
      default: $display("Invalid day");
    endcase
  end
endmodule
```

### 2. `casez`
- Treats `z` and `?` as don't-care values.
- Useful for pattern matching with wildcards.

```SV
module casez_example;
  logic [3:0] opcode = 4'b1x0z;
  initial begin
    casez (opcode)
      4'b1??1: $display("Pattern A");   // ? matches x/z
      4'b10?z: $display("Pattern B");   // Matches this case
      default: $display("No match");
    endcase
  end
endmodule
```

### 3. `casex`
- Treats `x`, `z`, and `?` as don't-care values.
- Use cautiously in RTL design due to aggressive wildcard handling.

```SV
module casex_example;
  logic [3:0] data = 4'b10x1;
  initial begin
    casex (data)
      4'b101?: $display("Case 1");      // ? and x are ignored
      4'b10x1: $display("Case 2");      // Direct match
      default: $display("No match");    // This executes (exact match has priority)
    endcase
  end
endmodule
```


## Loop Constructs
Execute code blocks repeatedly under specified conditions.

### 1. `repeat` Loop
- Runs a block **fixed** number of times.

```SV
module repeat_example;
  initial begin
    repeat (3) begin
      $display("Hello (repeat)");  // Prints 3 times
    end
  end
endmodule
```

### 2. `while` Loop
- Runs while a condition is `true`.

```SV
module while_example;
  int count = 0;
  initial begin
    while (count < 3) begin
      $display("Count = %0d", count);  // Prints 0, 1, 2
      count++;
    end
  end
endmodule
```

### 3. `for` Loop
- Compact syntax with initialization, condition, and increment.

```SV
module for_example;
  initial begin
    for (int i=0; i<3; i++) begin
      $display("i = %0d", i);  // Prints 0, 1, 2
    end
  end
endmodule
```

### 4. `foreach` Loop
- Iterates over array elements.
**Syntax**: `foreach(array[index])`

```SV
module foreach_example;
  int nums[4] = '{10, 20, 30, 40};
  initial begin
    foreach (nums[i]) begin
      $display("nums[%0d] = %0d", i, nums[i]);  // Prints all elements
    end
  end
endmodule
```

### 5. `forever` Loop
- Runs indefinitely (used in testbenches).
**Always include a delay** (`#`) or `disable` statement to prevent simulation hangs.

```SV
module forever_example;
  initial begin : main_block
    int cycles = 0;
    forever begin
      $display("Cycle %0d", cycles);
      cycles++;
      #10;  // Delay for 10 time units
      if (cycles == 5) disable main_block;  // Exit after 5 cycles
    end
  end
endmodule
```


## Best Practices
1. **Case Statements**:
   - Use `unique case` to enforce single-branch execution.
   - Use `priority case` to prioritize branches.
   - Always include `default` unless all cases are covered.

2. **Loops in RTL**:
   - Ensure loops have **static bounds** for synthesis.
   - Avoid infinite loops without exit conditions.

3. **`forever` Loops**:
   - Use only in testbenches with timing controls (`#`).


## Exercises
1. **Positive/Negative Check**: Use `if-else` to classify an integer variable as positive, negative, or zero.

2. **Day Name Printer**: Implement a `case` statement that prints the weekday name for a number (1=Monday, ..., 7=Sunday).

3. **Repeat Loop Counter**: Use `repeat` to print numbers from 1 to 10.

4. **Array Traversal with `while`**: Print all elements of an integer array using a `while` loop.

5. **Factorial Calculator**: Compute the factorial of a number using a `for` loop.

6. **Array Summation**: Use `foreach` to calculate the sum of an integer array.

7. **Controlled `forever` Loop**: Print "Simulating..." indefinitely but terminate after 10 iterations using `disable`.

