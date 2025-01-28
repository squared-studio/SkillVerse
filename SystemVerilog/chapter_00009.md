# Chapter 9: Tasks and Functions

## Introduction
Tasks and functions in SystemVerilog are used to encapsulate and reuse code. They help in creating modular and maintainable designs.

## Differences between Tasks and Functions
- **Tasks**: Can contain timing controls, can call other tasks and functions, and do not return a value.
- **Functions**: Cannot contain timing controls, can call other functions but not tasks, and must return a value.

## Defining and Using Tasks
Tasks are defined using the `task` keyword and are called using their name.

### Example
```systemverilog
module task_example;
  task display_message(input string message);
    $display("%s", message);
  endtask

  initial begin
    display_message("Hello, SystemVerilog!");
  end
endmodule
```

## Defining and Using Functions
Functions are defined using the `function` keyword and are called using their name.

### Example
```systemverilog
module function_example;
  function int add(input int a, input int b);
    add = a + b;
  endfunction

  initial begin
    int result;
    result = add(5, 3);
    $display("Result: %0d", result);
  end
endmodule
```

## Static and Automatic
- **Static**: Variables are shared across all calls to the task or function.
- **Automatic**: Variables are unique to each call to the task or function.

### Example
```systemverilog
module automatic_example;
  task automatic increment(input int a, output int b);
    begin
      b = a + 1;
    end
  endtask

  initial begin
    int result;
    increment(5, result);
    $display("Result: %0d", result);
  end
endmodule
```

## Return Type
Functions must have a return type, which specifies the type of value they return.

### Example
```systemverilog
module return_type_example;
  function int multiply(input int a, input int b);
    multiply = a * b;
  endfunction

  initial begin
    int result;
    result = multiply(4, 2);
    $display("Result: %0d", result);
  end
endmodule
```

## Exercises
1. Define a task that takes two integers as input and displays their sum.
2. Define a function that takes two integers as input and returns their product.
3. Use an automatic task to calculate the factorial of a number.
4. Define a function with a return type of `real` that calculates the area of a circle given its radius.

## Conclusion
Tasks and functions in SystemVerilog provide powerful tools for creating modular and reusable code. Understanding these constructs is essential for writing efficient and maintainable hardware models and testbenches.
