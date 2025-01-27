# Data Types

## reg
A `reg` is a data type used to represent variables that hold their value until explicitly changed.
```SV
reg myReg;
initial begin
    myReg = 1'b0;
    #10 myReg = 1'b1;
end
```

### Exercise
Create a `reg` variable, toggle its value every 5 time units, and print out its value using `$display`.

## wire
A `wire` is used to connect different elements and continuously drive a value.
```SV
wire myWire;
assign myWire = myReg;
```

### Exercise
Create a `wire` that connects two `reg` variables, observe the changes, and print out the values using `$display`.

## integer
An `integer` is a general-purpose variable used for arithmetic operations.
```SV
integer myInt;
initial myInt = 42;
```

### Exercise
Create an `integer` variable, perform basic arithmetic operations on it, and print out the results using `$display`.

## real
A `real` is used to represent floating-point numbers.
```SV
real myReal;
initial myReal = 3.14;
```

### Exercise
Create a `real` variable, perform basic arithmetic operations on it, and print out the results using `$display`.

## time
A `time` is used to store simulation time values.
```SV
time myTime;
initial myTime = $time;
```

### Exercise
Create a `time` variable, display the current simulation time using `$display`.

## realtime
A `realtime` is similar to `real` but specifically used for time values.
```SV
realtime myRealTime;
initial myRealTime = $realtime;
```

### Exercise
Create a `realtime` variable, display the current simulation time using `$display`.

## logic
A `logic` is a 4-state data type that can be used in place of `reg` or `wire`.
```SV
logic myLogic;
initial myLogic = 1'b0;
```

### Exercise
Create a `logic` variable, toggle its value every 5 time units, and print out its value using `$display`.

## bit
A `bit` is a 2-state data type (0 or 1).
```SV
bit myBit;
initial myBit = 1'b1;
```

### Exercise
Create a `bit` variable, toggle its value every 5 time units, and print out its value using `$display`.

## byte
A `byte` is an 8-bit data type.
```SV
byte myByte;
initial myByte = 8'hFF;
```

### Exercise
Create a `byte` variable, perform bitwise operations on it, and print out the results using `$display`.

## shortint
A `shortint` is a 16-bit signed integer.
```SV
shortint myShortInt;
initial myShortInt = 16'sh1234;
```

### Exercise
Create a `shortint` variable, perform arithmetic operations on it, and print out the results using `$display`.

## int
An `int` is a 32-bit signed integer.
```SV
int myInt;
initial myInt = 32'h12345678;
```

### Exercise
Create an `int` variable, perform arithmetic operations on it, and print out the results using `$display`.

## longint
A `longint` is a 64-bit signed integer.
```SV
longint myLongInt;
initial myLongInt = 64'h123456789ABCDEF0;
```

### Exercise
Create a `longint` variable, perform arithmetic operations on it, and print out the results using `$display`.

## shortreal
A `shortreal` is a 32-bit floating-point number.
```SV
shortreal myShortReal;
initial myShortReal = 3.14;
```

### Exercise
Create a `shortreal` variable, perform arithmetic operations on it, and print out the results using `$display`.
