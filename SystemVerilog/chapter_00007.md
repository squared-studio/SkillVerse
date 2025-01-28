# Control Flow

## Introduction
Control flow statements in SystemVerilog are used to control the execution of code based on certain conditions. They include conditional statements, case statements, and loops.

## Conditional Statements
Conditional statements are used to execute code based on a condition.

### `if-else`
The `if-else` statement executes code if a condition is true, and optionally executes different code if the condition is false.

```SV
module if_else_if_example;
  int a = 10;
  initial begin
    if (a > 10) begin
      $display("a is greater than 10");
    end else if (a == 10) begin
      $display("a is equal to 10");
    end else begin
      $display("a is less than 10");
    end
  end
endmodule
```

## Case Statements
Case statements are used to execute code based on the value of a variable.

### `case`
The `case` statement selects one of several blocks of code to execute based on the value of a variable.

```SV
module case_example;
  int a = 2;
  initial begin
    case (a)
      1: $display("a is 1");
      2: $display("a is 2");
      3: $display("a is 3");
      default: $display("a is not 1, 2, or 3");
    endcase
  end
endmodule
```

### `casez`
The `casez` statement treats `z` and `?` as don't-care values.

```SV
module casez_example;
  logic [3:0] a = 4'b1010;
  initial begin
    casez (a)
      4'b1?10: $display("a matches 1?10");
      default: $display("a does not match 1?10");
    endcase
  end
endmodule
```

### `casex`
The `casex` statement treats `x`, `z`, and `?` as don't-care values.

```SV
module casex_example;
  logic [3:0] a = 4'b10x0;
  initial begin
    casex (a)
      4'b10?0: $display("a matches 10?0");
      default: $display("a does not match 10?0");
    endcase
  end
endmodule
```

## Loops
Loops are used to execute a block of code multiple times.

### `repeat`
The `repeat` loop executes a block of code a fixed number of times.

```SV
module repeat_example;
  int i;
  initial begin
    repeat (5) begin
      $display("Iteration: %0d", i);
      i++;
    end
  end
endmodule
```

### `while`
The `while` loop executes a block of code as long as a condition is true.

```SV
module while_example;
  int i = 0;
  initial begin
    while (i < 5) begin
      $display("Iteration: %0d", i);
      i++;
    end
  end
endmodule
```

### `for`
The `for` loop executes a block of code a fixed number of times, with an initialization, condition, and increment.

```SV
module for_example;
  initial begin
    for (int i = 0; i < 5; i++) begin
      $display("Iteration: %0d", i);
    end
  end
endmodule
```

### `foreach`
The `foreach` loop iterates over the elements of an array.

```SV
module foreach_example;
  int array[5] = {0, 1, 2, 3, 4};
  initial begin
    foreach (array[i]) begin
      $display("Element %0d: %0d", i, array[i]);
    end
  end
endmodule
```

### `forever`
The `forever` loop executes a block of code indefinitely.

```SV
module forever_example;
  int i = 0;
  initial begin
    forever begin
      $display("Iteration: %0d", i);
      i++;
      if (i == 5) disable forever_example;
    end
  end
endmodule
```

## Exercises
1. Use an `if-else` statement to check if a variable is positive, negative, or zero.
2. Use a `case` statement to print the name of a day based on a variable representing the day number.
3. Use a `repeat` loop to print numbers from 1 to 10.
4. Use a `while` loop to print the elements of an array.
5. Use a `for` loop to calculate the factorial of a number.
6. Use a `foreach` loop to sum the elements of an array.
7. Use a `forever` loop to print a message indefinitely, and break the loop after 10 iterations.

## Conclusion
Control flow statements in SystemVerilog provide powerful tools for controlling the execution of code. Understanding these statements is essential for writing efficient and effective hardware models and testbenches.
