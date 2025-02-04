# Operators

## Introduction
Operators form the building blocks of hardware description and verification in SystemVerilog. Understanding their behavior is crucial for RTL design, verification, and modeling hardware-software interactions. This guide covers essential operators with hardware-centric considerations.

## Arithmetic Operators
Used for mathematical computations. **Critical for datapath design and calculations.**

| Operator | Description          | Hardware Equivalent           | Notes                                 |
|----------|----------------------|-------------------------------|---------------------------------------|
| `+`      | Addition             | Combinational adder           | Supports signed/unsigned              |
| `-`      | Subtraction          | Combinational subtractor      | 2's complement handling               |
| `*`      | Multiplication       | Multiplier block              | Resource-intensive in synthesis       |
| `/`      | Division             | Complex sequential logic      | Avoid in RTL (non-synthesizable)      |
| `%`      | Modulus              | Remainder logic               | Useful for address wrapping           |

### Example with Real-World Application
```SV
module address_calc;
  logic [31:0] base_addr = 32'h4000_0000;
  logic [15:0] offset = 16'hFFFC;
  logic [31:0] final_addr;

  assign final_addr = base_addr + (offset << 2);  // Common address calculation
endmodule
```

**Key Considerations:**
- Division/modulus with zero causes simulation errors
- Integer division truncates (no rounding)
- Use `always_comb` for pure combinational logic

## Logical vs Bitwise Operators
### Logical Operators (Boolean Context)
| Operator | Description          | Example             | Result Type |
|----------|----------------------|---------------------|-------------|
| `&&`     | Logical AND          | `(a > 5) && (b < 3)`| 1-bit bool  |
| `\|\|`   | Logical OR           | `x \|\| y`          | 1-bit bool  |
| `!`      | Logical NOT          | `!enable`           | 1-bit bool  |

### Bitwise Operators (Vector Operations)
| Operator | Description          | Example (4-bit)      | Result      |
|----------|----------------------|----------------------|-------------|
| `&`      | Bitwise AND          | `4'b1100 & 4'b1010`  | 4'b1000     |
| `\|`     | Bitwise OR           | `4'b1100 \| 4'b1010` | 4'b1110     |
| `^`      | Bitwise XOR          | `4'b1100 ^ 4'b1010`  | 4'b0110     |
| `~`      | Bitwise NOT          | `~4'b0011`           | 4'b1100     |
| `<<`     | Logical Left Shift   | `4'b0001 << 2`       | 4'b0100     |
| `>>`     | Logical Right Shift  | `4'b1000 >> 1`       | 4'b0100     |
| `<<<`    | Arithmetic Left Shift| `4'sb1000 <<< 1`     | 4'sb0000    |
| `>>>`    | Arithmetic Right Shift| `4'sb1000 >>> 1`    | 4'sb1100    |

**Shift Operator Differences:**
```SV
logic [3:0] a = 4'b1000;
$display(a >> 1);   // Logical:    0100
$display(a >>> 1);  // Arithmetic: 1100 (sign-extended)
```

## Reduction Operators
Operate on all bits of a vector:

| Operator | Description          | Example (4'b1100) | Result |
|----------|----------------------|-------------------|--------|
| `&`      | Reduction AND        | `&4'b1100`        | 0      |
| `\|`     | Reduction OR         | `\|4'b1100`       | 1      |
| `^`      | Reduction XOR        | `^4'b1100`        | 0      |
| `~&`     | Reduction NAND       | `~&4'b1100`       | 1      |
| `~\|`    | Reduction NOR        | `~\|4'b1100`      | 0      |
| `~^`     | Reduction XNOR       | `~^4'b1100`       | 1      |

**Practical Use Case - Parity Check:**
```SV
logic [7:0] data = 8'hA5;
logic parity = ^data;  // XOR all bits → parity bit
```

## Comparison Operators
### Basic Comparisons
| Operator | Description          | X/Z Handling       |
|----------|----------------------|--------------------|
| `==`     | Equality             | X/Z → X            |
| `!=`     | Inequality           | X/Z → X            |
| `>`      | Greater than         | X/Z → X            |
| `<`      | Less than            | X/Z → X            |
| `>=`     | Greater or equal     | X/Z → X            |
| `<=`     | Less or equal        | X/Z → X            |

### 4-State Logic Comparisons
| Operator | Description          | X/Z Handling       |
|----------|----------------------|--------------------|
| `===`    | Case equality         | X/Z match exactly  |
| `!==`    | Case inequality       | X/Z match exactly  |

**Critical Difference:**
```SV
logic a = 1'bz;
logic b = 1'bx;

$display(a == b);   // X (unknown)
$display(a === b);  // 0 (exact match)
```

## Operator Precedence
Order of operations (highest to lowest):
1. `()` `[]` `::`
2. `!` `~` `&` `|` `^` `~^` (unary)
3. `*` `/` `%`
4. `+` `-` (binary)
5. `<<` `>>` `<<<` `>>>`
6. `<` `<=` `>` `>=`
7. `==` `!=` `===` `!==`
8. `&` (binary)
9. `^` `~^`
10. `|`
11. `&&`
12. `||`
13. `?:` (conditional)

**Always use parentheses for complex expressions!**

## Practical Exercises
1. **ALU Design**: Implement a 4-bit ALU supporting AND/OR/XOR/ADD operations
2. **Parity Generator**: Create reduction-based even/odd parity generator
3. **Barrel Shifter**: Design 8-bit barrel shifter using shift operators
4. **X Detection**: Use case equality to detect X/Z values in data bus
5. **Operator Precedence**: Solve `a = 3 + 4 << 2;` vs `a = (3 + 4) << 2;`

## Common Pitfalls
1. **Bitwise vs Logical Confusion**:
   ```SV
   if (enable & reset)  // Bitwise AND (vector)
   if (enable && reset) // Logical AND (scalar)
   ```

2. **Shift Operator Misuse**:
   ```SV
   logic signed [7:0] a = -8;
   a >> 2;   // Logical shift: 00111110 (62)
   a >>> 2;  // Arithmetic shift: 11111110 (-2)
   ```

3. **Comparison with X Values**:
   ```SV
   if (unknown_signal == 1'bx)  // Always false!
   if (unknown_signal === 1'bx) // Correct check
   ```
