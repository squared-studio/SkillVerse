# Methods

SystemVerilog provides two types of methods to encapsulate reusable code: `task` and `function`.

## task
A `task` is used to encapsulate a sequence of statements that can include time-consuming operations such as delays or event control. Tasks can have input, output, and inout arguments.

### Syntax
```SV
task task_name(input_type input_arg, output_type output_arg, inout_type inout_arg);
    // Task body
endtask
```

### Example
```SV
task add(input int a, input int b, output int sum);
    sum = a + b;
endtask
```

### Lifetime
Tasks can have either static or automatic lifetime:
- **Static**: Variables retain their values between calls.
- **Automatic**: Variables are reinitialized each time the task is called.

```SV
task automatic add(input int a, input int b, output int sum);
    sum = a + b;
endtask
```
```SV
task static add(input int a, output int sum);
    static int sum = 0;
    sum = a + sum;
endtask
```

## function
A `function` is used to encapsulate a sequence of statements that execute without any time-consuming operations. Functions can have input arguments and return a single value.

### Syntax
```SV
function return_type function_name(input_type input_arg);
    // Function body
    return return_value;
endfunction
```

### Example
```SV
function int add(input int a, input int b);
    add = a + b;
endfunction
```
```SV
function int add(input int a, input int b);
    return a + b;
endfunction
```

### Lifetime
Functions can also have either static or automatic lifetime:
- **Static**: Variables retain their values between calls.
- **Automatic**: Variables are reinitialized each time the function is called.

```SV
function automatic int add(input int a, input int b);
    add = a + b;
endfunction
```
```SV
function static int add(input int a);
    static int sum = 0;
    sum = a + sum;
    return sum;
endfunction
```

## Exercise
1. Create a `task` that takes two integers as input and outputs their sum.
2. Create a `task` that takes an integer array as input and outputs the maximum value in the array.
3. Create a `function` that takes two integers as input and returns their product.
4. Create a `function` that takes an integer as input and returns its factorial.
5. Modify the `task` from exercise 1 to take one input and sum with previous result using static lifetime.
6. Modify the `function` from exercise 3 to take one input and multiply with previous result using static lifetime.
