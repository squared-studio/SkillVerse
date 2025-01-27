# Control Statements

Control statements in SystemVerilog are used to control the flow of execution in a program. These statements include conditional statements, loops, and concurrent statements.

## case
The `case` statement is used to execute one of several blocks of code based on the value of an expression.
```SV
module case_example;
    int a = 2;
    initial begin
        case (a)
            1: $display("a is 1");
            2: $display("a is 2");
            3: $display("a is 3");
            default: $display("a is not 1, 2, or 3");
        endcase
    end
endmodule
```

## if-else
The `if-else` statement is used to execute a block of code based on a condition.
The `else if` statement is used to check multiple conditions in sequence.
```SV
module if_else_example;
    int a = 5;
    initial begin
        if (a > 10) begin
            $display("a is greater than 10");
        end else if (a > 5) begin
            $display("a is greater than 5 but less than or equal to 10");
        end else if (a > 0) begin
            $display("a is greater than 0 but less than or equal to 5");
        end else begin
            $display("a is less than or equal to 0");
        end
    end
endmodule
```

## repeat
The `repeat` statement is used to execute a block of code a fixed number of times.
```SV
module repeat_example;
    int i;
    initial begin
        repeat (5) begin
            $display("Iteration: %0d", i);
            i++;
        end
    end
endmodule
```

## while
The `while` statement is used to execute a block of code as long as a condition is true.
```SV
module while_example;
    int i = 0;
    initial begin
        while (i < 5) begin
            $display("Iteration: %0d", i);
            i++;
        end
    end
endmodule
```

## for
The `for` statement is used to execute a block of code a fixed number of times, with an initialization, condition, and increment.
```SV
module for_example;
    initial begin
        for (int i = 0; i < 5; i++) begin
            $display("Iteration: %0d", i);
        end
    end
endmodule
```

## foreach
The `foreach` statement is used to iterate over the elements of an array.
```SV
module foreach_example;
    int myArray[5] = '{1, 2, 3, 4, 5};
    initial begin
        foreach (myArray[i]) begin
            $display("Element at index %0d: %0d", i, myArray[i]);
        end
    end
endmodule
```

## forever
The `forever` statement is used to execute a block of code indefinitely.
```SV
module forever_example;
    initial begin
        forever begin
            $display("This will print forever");
            #10; // Delay to prevent infinite loop
        end
    end
endmodule
```

## continue
The `continue` statement is used to skip the remaining code in the current iteration of a loop and proceed to the next iteration.
```SV
module continue_example;
    initial begin
        for (int i = 0; i < 5; i++) begin
            if (i == 2) continue;
            $display("Iteration: %0d", i);
        end
    end
endmodule
```

## break
The `break` statement is used to exit a loop prematurely.
```SV
module break_example;
    initial begin
        for (int i = 0; i < 5; i++) begin
            if (i == 2) break;
            $display("Iteration: %0d", i);
        end
    end
endmodule
```

## fork-join
The `fork-join` statement is used to execute multiple blocks of code concurrently.
```SV
module fork_join_example;
    initial begin
        fork
            $display("Block 1");
            $display("Block 2");
        join
    end
endmodule
```

## fork-join_any
The `fork-join_any` statement is used to execute multiple blocks of code concurrently, and the execution continues as soon as any one of the blocks completes.
```SV
module fork_join_any_example;
    initial begin
        fork
            #10 $display("Block 1");
            #20 $display("Block 2");
        join_any
        $display("One of the blocks has completed");
    end
endmodule
```

## fork-join_none
The `fork-join_none` statement is used to execute multiple blocks of code concurrently, and the execution continues immediately without waiting for any of the blocks to complete.
```SV
module fork_join_none_example;
    initial begin
        fork
            #10 $display("Block 1");
            #20 $display("Block 2");
        join_none
        $display("Execution continues immediately");
    end
endmodule
```

## Exercise
1. Create a module that uses a `case` statement to print a message based on the value of a variable.
2. Create a module that uses an `if-else` statement to check if a number is positive or negative.
3. Create a module that uses an `else if` statement to check multiple conditions in sequence.
4. Create a module that uses a `repeat` statement to print a message 5 times.
5. Create a module that uses a `while` statement to print numbers from 0 to 4.
6. Create a module that uses a `for` statement to print numbers from 0 to 4.
7. Create a module that uses a `foreach` statement to iterate over an array and print its elements.
8. Create a module that uses a `forever` statement to print a message indefinitely with a delay.
9. Create a module that uses a `continue` statement to skip printing the number 2 in a loop.
10. Create a module that uses a `break` statement to exit a loop when the number 2 is encountered.
11. Create a module that uses a `fork-join` statement to execute two blocks of code concurrently.
12. Create a module that uses a `fork-join_any` statement to execute two blocks of code concurrently and continue execution as soon as one block completes.
13. Create a module that uses a `fork-join_none` statement to execute two blocks of code concurrently and continue execution immediately.