# Randomization

## Introduction
Randomization in SystemVerilog is used to generate random values for variables, which is essential for creating effective testbenches. SystemVerilog provides built-in support for randomization, including random variables, constraints, and randomization methods.

## Random Variables
Random variables are declared using the `rand` or `randc` keywords.

### Example
```SV
module random_variable_example;
  rand int a;
  initial begin
    if (!$urandom(a))
      $display("Random value: %0d", a);
  end
endmodule
```

## Constraints
Constraints are used to restrict the range or values of random variables.

### Example
```SV
module constraint_example;
  rand int a;
  constraint a_constraint { a > 0 && a < 100; }
  initial begin
    if (!$urandom(a))
      $display("Random value: %0d", a);
  end
endmodule
```

## Randomization Methods
Randomization methods are used to generate random values for variables.

### `randomize()`
The `randomize()` method generates random values for all random variables in the scope.

### Example
```SV
module randomize_example;
  rand int a;
  rand int b;
  initial begin
    if (randomize())
      $display("Random values: a = %0d, b = %0d", a, b);
  end
endmodule
```

### `srandom()`
The `srandom()` method sets the seed for the random number generator.

### Example
```SV
module srandom_example;
  rand int a;
  initial begin
    srandom(12345);
    if (randomize())
      $display("Random value: %0d", a);
  end
endmodule
```

## Exercises
1. Declare a random variable and generate a random value for it.
2. Define a constraint to restrict the range of a random variable.
3. Use the `randomize()` method to generate random values for multiple variables.
4. Use the `srandom()` method to set the seed for the random number generator and generate a random value.

## Conclusion
Randomization in SystemVerilog provides powerful tools for generating random values and creating effective testbenches. Understanding how to use random variables, constraints, and randomization methods is essential for writing efficient and effective hardware models and testbenches.
