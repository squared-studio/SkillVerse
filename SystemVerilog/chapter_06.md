# Chapter 6: Operators

## Introduction
Operators in SystemVerilog are used to perform various operations on data. They can be classified into several categories, including arithmetic, logical, bitwise, reduction, and comparison operators.

## Arithmetic Operators
Arithmetic operators are used to perform mathematical operations.

| Operator | Description | Example |
|----------|-------------|---------|
| `+`      | Addition    | `a + b` |
| `-`      | Subtraction | `a - b` |
| `*`      | Multiplication | `a * b` |
| `/`      | Division    | `a / b` |
| `%`      | Modulus     | `a % b` |

### Example
```systemverilog
module arithmetic_example;
  int a = 10;
  int b = 5;
  initial begin
    $display("Addition: %0d", a + b);
    $display("Subtraction: %0d", a - b);
    $display("Multiplication: %0d", a * b);
    $display("Division: %0d", a / b);
    $display("Modulus: %0d", a % b);
  end
endmodule
```

## Logical Operators
Logical operators are used to perform logical operations.

| Operator | Description | Example |
|----------|-------------|---------|
| `&&`     | Logical AND | `a && b` |
| `||`     | Logical OR  | `a || b` |
| `!`      | Logical NOT | `!a`     |

### Example
```systemverilog
module logical_example;
  bit a = 1;
  bit b = 0;
  initial begin
    $display("Logical AND: %0b", a && b);
    $display("Logical OR: %0b", a || b);
    $display("Logical NOT: %0b", !a);
  end
endmodule
```

## Bitwise Operators
Bitwise operators are used to perform bit-level operations.

| Operator | Description | Example |
|----------|-------------|---------|
| `&`      | Bitwise AND | `a & b` |
| `|`      | Bitwise OR  | `a | b` |
| `^`      | Bitwise XOR | `a ^ b` |
| `~`      | Bitwise NOT | `~a`    |
| `<<`     | Left Shift  | `a << b` |
| `>>`     | Right Shift | `a >> b` |
| `<<<`    | Arithmetic Left Shift | `a <<< b` |
| `>>>`    | Arithmetic Right Shift | `a >>> b` |

### Example
```systemverilog
module bitwise_example;
  logic [3:0] a = 4'b1100;
  logic [3:0] b = 4'b1010;
  initial begin
    $display("Bitwise AND: %0b", a & b);
    $display("Bitwise OR: %0b", a | b);
    $display("Bitwise XOR: %0b", a ^ b);
    $display("Bitwise NOT: %0b", ~a);
    $display("Left Shift: %0b", a << 1);
    $display("Right Shift: %0b", a >> 1);
    $display("Arithmetic Left Shift: %0b", a <<< 1);
    $display("Arithmetic Right Shift: %0b", a >>> 1);
  end
endmodule
```

## Reduction Operators
Reduction operators are used to perform bitwise reduction operations.

| Operator | Description | Example |
|----------|-------------|---------|
| `&`      | Reduction AND | `&a` |
| `|`      | Reduction OR  | `|a` |
| `^`      | Reduction XOR | `^a` |

### Example
```systemverilog
module reduction_example;
  logic [3:0] a = 4'b1100;
  initial begin
    $display("Reduction AND: %0b", &a);
    $display("Reduction OR: %0b", |a);
    $display("Reduction XOR: %0b", ^a);
  end
endmodule
```

## Comparison Operators
Comparison operators are used to compare two values.

| Operator | Description | Example |
|----------|-------------|---------|
| `==`     | Equal to    | `a == b` |
| `!=`     | Not equal to| `a != b` |
| `<`      | Less than   | `a < b`  |
| `<=`     | Less than or equal to | `a <= b` |
| `>`      | Greater than| `a > b`  |
| `>=`     | Greater than or equal to | `a >= b` |
| `===`    | Case equality | `a === b` |
| `!==`    | Case inequality | `a !== b` |

### Example
```systemverilog
module comparison_example;
  int a = 10;
  int b = 5;
  initial begin
    $display("Equal to: %0b", a == b);
    $display("Not equal to: %0b", a != b);
    $display("Less than: %0b", a < b);
    $display("Less than or equal to: %0b", a <= b);
    $display("Greater than: %0b", a > b);
    $display("Greater than or equal to: %0b", a >= b);
    $display("Case equality: %0b", a === b);
    $display("Case inequality: %0b", a !== b);
  end
endmodule
```

## Exercises
1. Use arithmetic operators to perform addition, subtraction, multiplication, division, and modulus operations on two variables.
2. Use logical operators to perform logical AND, OR, and NOT operations on two variables.
3. Use bitwise operators to perform bitwise AND, OR, XOR, NOT, left shift, right shift, arithmetic left shift, and arithmetic right shift operations on two variables.
4. Use reduction operators to perform reduction AND, OR, and XOR operations on a variable.
5. Use comparison operators to compare two variables using equal to, not equal to, less than, less than or equal to, greater than, greater than or equal to, case equality, and case inequality.

## Conclusion
Operators in SystemVerilog provide powerful tools for performing various operations on data. Understanding these operators is essential for efficient hardware modeling and simulation.
