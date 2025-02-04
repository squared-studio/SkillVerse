# Data Types

SystemVerilog offers a comprehensive set of **data types** to model hardware behavior and verification environments effectively. Below is a detailed breakdown of these types, categorized for clarity and enhanced with practical examples.

## **Built-in Data Types**
SystemVerilog provides **2-state** (binary) and **4-state** (0, 1, X, Z) data types for hardware modeling and verification.

### **4-State Types (for RTL Design)**
Used for modeling hardware with **unknown (X)** and **high-impedance (Z)** states.

| Type      | Description                          | Example                     |
|-----------|--------------------------------------|-----------------------------|
| `reg`     | Legacy 4-state type for storage      | `reg [3:0] counter;`        |
| `wire`    | Connects components (default: 1-bit) | `wire clk;`                 |
| `logic`   | Modern replacement for `reg`/`wire`  | `logic [7:0] data_bus;`     |
| `integer` | 32-bit signed integer (4-state)      | `integer timeout = 100;`    |
| `time`    | 64-bit unsigned time value           | `time start_time;`          |
| `realtime`| Real-number time (e.g., delays)      | `realtime delay = 2.5e-9;`  |

```SV
module design_example;
  logic [3:0] addr; // Replaces reg/wire in modern designs
  wire enable;      // Default 1-bit connection
  integer error_count = 0;
endmodule
```


### **2-State Types (for Verification)**
Used in testbenches for **high-performance simulation** (no X/Z states).

| Type         | Description                     | Example                   |
|--------------|---------------------------------|---------------------------|
| `bit`        | 2-state, unsigned (default: 1-bit) | `bit flag = 1;`           |
| `byte`       | 8-bit signed integer            | `byte temperature = -5;`  |
| `shortint`   | 16-bit signed integer           | `shortint offset = 16'hFF;` |
| `int`        | 32-bit signed integer           | `int packet_size = 1024;` |
| `longint`    | 64-bit signed integer           | `longint universe_age;`   |
| `shortreal`  | 32-bit floating-point           | `shortreal voltage = 3.3;`|
| `real`       | 64-bit floating-point           | `real pi = 3.1415926535;` |

```SV
module testbench;
  bit reset = 0;    // 2-state for verification
  int  transactions = 100;
  real clock_period = 10.0e-9; // 10ns period
endmodule
```


## **Advanced Built-in Types**
Specialized types for modeling hardware-specific behavior.

### **Tri-State and Multi-Driver Types**
| Type   | Description                     | Example                 |
|--------|---------------------------------|-------------------------|
| `tri`   | Tri-state bus (identical to `wire`) | `tri [7:0] data_bus;` |
| `tri0`  | Pull-down when undriven         | `tri0 enable;`          |
| `tri1`  | Pull-up when undriven           | `tri1 reset;`           |
| `wand`  | Wired-AND resolution            | `wand signal;`          |
| `wor`   | Wired-OR resolution             | `wor interrupt;`        |

```SV
module bus_driver;
  tri1 [15:0] address_bus; // Pull-up if undriven
  wand shared_line;         // AND of all drivers
endmodule
```


## **User-Defined Data Types**
Custom types for improved readability and abstraction.

### 1. **`typedef`**
Create aliases for existing types.
```SV
typedef logic [31:0] word_t; // 32-bit word
word_t instruction;
```

### 2. **`enum`**
Define a set of named values (ideal for state machines).
```SV
typedef enum {IDLE, START, DATA, STOP} state_t;
state_t current_state = IDLE;
```

### 3. **`struct`**
Group related variables (similar to C structs).
```SV
typedef struct {
  logic [7:0] addr;
  logic [31:0] data;
  bit rw; // 0=read, 1=write
} transaction_t;

transaction_t tx; // Instance of struct
tx.addr = 8'hFF;  // Access fields
```

### 4. **`union`**
Share storage between different data types.
```SV
typedef union {
  int i;
  shortreal f;
} data_union_t;

data_union_t du;
du.f = 3.14; // Interpret bits as float
```


## **Packed vs. Unpacked Arrays**
### **Packed Arrays**
- Contiguous bits (treated as a single vector).
- Efficient for bit-level operations.
```SV
logic [3:0][7:0] packed_array; // 4x8-bit vector (32 bits total)
assign packed_array = 32'hA5A5_A5A5;
```

### **Unpacked Arrays**
- Collections of elements (memory-efficient for large arrays).
```SV
int unpacked_array [0:1023]; // 1024 32-bit integers
unpacked_array[0] = 42;      // Access individual elements
```


## **Exercises & Solutions**
1. **Declare a `reg` and assign a value:**
   ```SV
   reg [7:0] data_reg;
   initial data_reg = 8'b1010_1100;
   ```

   2. **Connect `wire` to `reg`:**
   ```SV
   reg  enable_reg;
   wire enable_wire = enable_reg; // Continuous assignment
   ```

   3. **Use `integer` in arithmetic:**
   ```SV
   integer a = 10, b = 20;
   integer sum = a + b; // sum = 30
   ```

   4. **Assign `real` value:**
   ```SV
   real capacitance = 1.2e-12; // 1.2 picofarads
   ```

   5. **Store simulation time:**
   ```SV
   time timestamp;
   initial timestamp = $time;
   ```

   6. **Bitwise operations on `logic`:**
   ```SV
   logic [3:0] mask = 4'b1100;
   logic [3:0] result = mask & 4'b1010; // 4'b1000
   ```

   7. **Define and use `struct`:**
   ```SV
   typedef struct { int x; int y; } point_t;
   point_t origin;
   origin.x = 0;
   ```

   8. **`enum` for state machine:**
   ```SV
   typedef enum {S_IDLE, S_ACTIVE} state_t;
   state_t state = S_IDLE;
   ```

   9. **Initialize packed array:**
   ```SV
   logic [3:0][3:0] matrix = '{4'hA, 4'hB, 4'hC, 4'hD};
   ```

   10. **Iterate unpacked array:**
    ```SV
    int arr [4] = '{1, 2, 3, 4};
    initial foreach (arr[i]) $display(arr[i]);
    ```
