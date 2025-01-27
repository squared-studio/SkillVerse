# Operators & Assignments

SystemVerilog provides a variety of operators and assignment types to describe hardware behavior. Understanding these operators and assignments is essential for writing efficient and correct hardware descriptions.

## Operators

### Arithmetic Operators
Arithmetic operators perform mathematical operations.
- `+` : Addition
- `-` : Subtraction
- `*` : Multiplication
- `/` : Division
- `%` : Modulus

### Example
```systemverilog
module arithmetic_example;
    int a = 10, b = 5;
    int sum, diff, prod, quot, mod;
    initial begin
        sum = a + b;
        diff = a - b;
        prod = a * b;
        quot = a / b;
        mod = a % b;
    end
endmodule
```

### Relational Operators
Relational operators compare two values.
- `==` : Equal to
- `!=` : Not equal to
- `<` : Less than
- `<=` : Less than or equal to
- `>` : Greater than
- `>=` : Greater than or equal to
- `===` : Case equality (compares including X and Z values)
- `!==` : Case inequality (compares including X and Z values)

### Example
```systemverilog
module relational_example;
    int a = 10, b = 5;
    bit result;
    initial begin
        result = (a == b);  // result is 0
        result = (a != b);  // result is 1
        result = (a < b);   // result is 0
        result = (a <= b);  // result is 0
        result = (a > b);   // result is 1
        result = (a >= b);  // result is 1
        result = (a === b); // result is 0
        result = (a !== b); // result is 1
    end
endmodule
```

### Logical Operators
Logical operators perform logical operations.
- `&&` : Logical AND
- `||` : Logical OR
- `!` : Logical NOT

### Example
```systemverilog
module logical_example;
    bit a = 1, b = 0;
    bit result;
    initial begin
        result = a && b; // result is 0
        result = a || b; // result is 1
        result = !a;     // result is 0
    end
endmodule
```

### Bitwise Operators
Bitwise operators perform bit-level operations.
- `&` : Bitwise AND
- `|` : Bitwise OR
- `^` : Bitwise XOR
- `~` : Bitwise NOT

### Example
```systemverilog
module bitwise_example;
    bit [3:0] a = 4'b1010, b = 4'b0101;
    bit [3:0] result;
    initial begin
        result = a & b; // result is 4'b0000
        result = a | b; // result is 4'b1111
        result = a ^ b; // result is 4'b1111
        result = ~a;    // result is 4'b0101
    end
endmodule
```

### Shift Operators
Shift operators shift bits left or right.
- `<<` : Logical left shift
- `>>` : Logical right shift
- `<<<` : Arithmetic left shift
- `>>>` : Arithmetic right shift

### Example
```systemverilog
module shift_example;
    bit [3:0] a = 4'b1010;
    bit [3:0] result;
    initial begin
        result = a << 1;  // result is 4'b0100
        result = a >> 1;  // result is 4'b0101
        result = a <<< 1; // result is 4'b0100
        result = a >>> 1; // result is 4'b0101
    end
endmodule
```

## Assignments

### Blocking Assignments
Blocking assignments use the `=` operator and execute sequentially. Each statement must complete before the next one begins.

### Syntax
```systemverilog
variable = expression;
```

### Example
```systemverilog
module blocking_example;
    reg a, b, c;
    initial begin
        a = 1;
        b = a;
        c = b;
    end
endmodule
```

### Non-blocking Assignments
Non-blocking assignments use the `<=` operator and execute concurrently. All right-hand side expressions are evaluated first, and then the assignments are made.

### Syntax
```systemverilog
variable <= expression;
```

### Example
```systemverilog
module nonblocking_example;
    reg a, b, c;
    initial begin
        a <= 1;
        b <= a;
        c <= b;
    end
endmodule
```

### Choosing Between Blocking and Non-blocking
Choosing the correct type of assignment is crucial for the correct behavior of your design.

- **Blocking Assignments (`=`)**:
  - Use in combinational logic within `always_comb` blocks.
  - Execute sequentially, making them suitable for describing operations that must occur in a specific order.
  - Example: Assigning values in a combinational logic block.

- **Non-blocking Assignments (`<=`)**:
  - Use in sequential logic within `always_ff` blocks.
  - Execute concurrently, making them suitable for describing operations that occur simultaneously.
  - Example: Assigning values in a clocked process, such as flip-flops.

### Example
```systemverilog
module example;
    reg clk, reset;
    reg [3:0] a, b, c;

    // Combinational logic using blocking assignments
    always_comb begin
        a = b + c;
    end

    // Sequential logic using non-blocking assignments
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            b <= 4'b0000;
        else
            b <= a;
    end
endmodule
```

## Exercise
1. Create a module that uses arithmetic operators to perform addition, subtraction, multiplication, division, and modulus operations.
2. Create a module that uses relational operators to compare two values.
3. Create a module that uses logical operators to perform logical operations.
4. Create a module that uses bitwise operators to perform bit-level operations.
5. Create a module that uses shift operators to shift bits left and right.
6. Create a module that uses blocking assignments to describe combinational logic.
7. Create a module that uses non-blocking assignments to describe sequential logic.
