# Advanced Data Types

## enum
An `enum` is used to define a set of named values, which makes the code more readable and maintainable.
```SV
typedef enum logic [1:0] {
    IDLE = 2'b00,
    RUNNING = 2'b01,
    PAUSED = 2'b10,
    STOPPED = 2'b11
} state_t;

state_t currentState;
initial begin
    currentState = IDLE;
    #10 currentState = RUNNING;
end
```

### Exercise
Create an `enum` type for traffic light states (RED, YELLOW, GREEN), and simulate the state transitions.

## typedef
A `typedef` is used to create a new data type name, which can simplify complex type definitions and improve code readability.
```SV
typedef int unsigned uint32_t;
uint32_t myUnsignedInt;
initial myUnsignedInt = 32'hFFFFFFFF;
```

### Exercise
Create a `typedef` for a 16-bit signed integer and use it to declare a variable.

## struct
A `struct` is used to group different data types into a single composite type.

### Packed Struct
A packed struct is a contiguous set of bits, which can be used for bit-level operations.
```SV
typedef struct packed {
    logic [7:0] byte_field;
    int integer_field;
} packedStruct_t;

packedStruct_t myPackedStruct;
initial begin
    myPackedStruct.byte_field = 8'hFF;
    myPackedStruct.integer_field = 42;
    $display("Packed Struct: byte_field = %h, integer_field = %0d", myPackedStruct.byte_field, myPackedStruct.integer_field);
    myPackedStruct = '{8'hAA, 100};
    $display("Packed Struct: byte_field = %h, integer_field = %0d", myPackedStruct.byte_field, myPackedStruct.integer_field);
end
```

### Unpacked Struct
An unpacked struct is a collection of variables that are not necessarily contiguous in memory.
```SV
typedef struct {
    logic [7:0] byte_field;
    int integer_field;
} unpackedStruct_t;

unpackedStruct_t myUnpackedStruct;
initial begin
    myUnpackedStruct.byte_field = 8'hFF;
    myUnpackedStruct.integer_field = 42;
    $display("Unpacked Struct: byte_field = %h, integer_field = %0d", myUnpackedStruct.byte_field, myUnpackedStruct.integer_field);
    myUnpackedStruct = '{byte_field: 8'hBB, integer_field: 200};
    $display("Unpacked Struct: byte_field = %h, integer_field = %0d", myUnpackedStruct.byte_field, myUnpackedStruct.integer_field);
end
```

### Exercise
Create a packed struct and an unpacked struct to represent a 3D point with `x`, `y`, and `z` coordinates, and initialize them with some values.
