# Chapter 3: Data Types

## Built-in Data Types
SystemVerilog provides a rich set of built-in data types for modeling hardware.

### `reg`
A register data type used to store values. (4-state, unsigned)

```systemverilog
reg [3:0] a;
```

### `wire`
A wire data type used to connect different components. (4-state, unsigned)

```systemverilog
wire b;
```

### `integer`
A general-purpose integer data type. (4-state, signed)

```systemverilog
integer count;
```

### `real`
A real number data type. (signed)

```systemverilog
real pi = 3.14;
```

### `time`
A 64-bit time data type. (unsigned)

```systemverilog
time t;
```

### `realtime`
A real number time data type. (unsigned)

```systemverilog
realtime rt;
```

### `logic`
A 4-state data type that can represent 0, 1, X, and Z. (4-state, unsigned)

```systemverilog
logic [7:0] data;
```

### `bit`
A 2-state data type that can represent 0 and 1. (2-state, unsigned)

```systemverilog
bit flag;
```

### `byte`
An 8-bit data type. (2-state, signed)

```systemverilog
byte b;
```

### `shortint`
A 16-bit signed integer. (2-state, signed)

```systemverilog
shortint si;
```

### `int`
A 32-bit signed integer. (2-state, signed)

```systemverilog
int i;
```

### `longint`
A 64-bit signed integer. (2-state, signed)

```systemverilog
longint li;
```

### `shortreal`
A 32-bit real number. (signed)

```systemverilog
shortreal sr;
```

## Advanced Built-in Data Types
SystemVerilog also provides advanced built-in data types for specific purposes.

### `tri`
A tri-state data type. (4-state, unsigned)

```systemverilog
tri t;
```

### `tri0`
A tri-state data type with a default value of 0. (3-state, unsigned)

```systemverilog
tri0 t0;
```

### `tri1`
A tri-state data type with a default value of 1. (3-state, unsigned)

```systemverilog
tri1 t1;
```

### `wand`
A wired-AND data type. (4-state, unsigned)

```systemverilog
wand wa;
```

### `wor`
A wired-OR data type. (4-state, unsigned)

```systemverilog
wor wo;
```

## User-defined Data Types
SystemVerilog allows users to define their own data types.

### `enum`
An enumerated type. (depends on base type)

```systemverilog
typedef enum {RED, GREEN, BLUE} color_t;
color_t color;
```

### `struct`
A structure type. (depends on member types)

```systemverilog
typedef struct {
  int x;
  int y;
} point_t;
point_t p;
```

### `union`
A union type. (depends on member types)

```systemverilog
typedef union {
  int i;
  real r;
} data_t;
data_t d;
```

### `typedef`
A type definition. (depends on base type)

```systemverilog
typedef int my_int;
my_int a;
```

## Packed and Unpacked
SystemVerilog supports both packed and unpacked arrays.

### Packed Array
A packed array is a contiguous set of bits.

```systemverilog
logic [7:0] packed_array;
```

### Unpacked Array
An unpacked array is an array of elements.

```systemverilog
int unpacked_array [0:3];
```

## Exercises
1. Declare a `reg` variable and assign it a value.
2. Create a `wire` and connect it to a `reg`.
3. Define an `integer` variable and use it in a simple arithmetic operation.
4. Declare a `real` variable and assign it a value.
5. Use the `time` data type to store the current simulation time.
6. Create a `logic` vector and perform bitwise operations on it.
7. Define a `struct` type and create an instance of it.
8. Use an `enum` type to represent different states in a state machine.
9. Declare a packed array and initialize it with a value.
10. Create an unpacked array and iterate over its elements.

## Conclusion
Understanding the various data types in SystemVerilog is crucial for effectively modeling and simulating digital systems. Built-in data types provide the foundation, while user-defined types offer flexibility and customization.
