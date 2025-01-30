# Simple SystemVerilog Exercises

## Self Study
- [STRUCT                                                   ](https://www.chipverify.com/systemverilog/systemverilog-struct)
- [TYPEDEF ALIAS                                            ](https://www.chipverify.com/systemverilog/systemverilog-typedef-alias)
- [CONTROL FLOW LOOPS                                       ](https://www.chipverify.com/systemverilog/systemverilog-control-flow-loops)
- [WHILE DO WHILE LOOP                                      ](https://www.chipverify.com/systemverilog/systemverilog-while-do-while-loop)
- [WHILE DO WHILE LOOP                                      ](https://www.chipverify.com/systemverilog/systemverilog-while-do-while-loop)
- [FOREACH LOOP                                             ](https://www.chipverify.com/systemverilog/systemverilog-foreach-loop)
- [FOR LOOP                                                 ](https://www.chipverify.com/systemverilog/systemverilog-for-loop)
- [FOREVER LOOP                                             ](https://www.chipverify.com/systemverilog/systemverilog-forever-loop)
- [REPEAT LOOP                                              ](https://www.chipverify.com/systemverilog/systemverilog-repeat-loop)
- [BREAK CONTINUE                                           ](https://www.chipverify.com/systemverilog/systemverilog-break-continue)

## Structs
  - Define a simple struct called `Person` with fields for `name`, `age`, and `address`.
  - Create an instance of the `Person` struct and initialize its fields.
  - Access and modify the fields of the `Person` struct.

## Typedef and Alias
  - Create a typedef for a 32-bit unsigned integer called `MyUInt`.
  - Declare a variable of type `MyUInt` and assign a value to it.
  - Declare 2 32-bit wires called `bus_1` & `bus_2`.
  - Use an alias to connect both `bus_1` & `bus_2`.
  - Drive `bus_1` and check if `bus_2` also get driven.
  - Repeat the inverse by driving `bus_2` and check if `bus_1` also get driven.

## Control Flow and Loops
  - Write a SystemVerilog program that prints numbers from 1 to 10 using a `for` loop.
  - Implement a counter that increments by 2 in each iteration of the loop.
  - Use an `if` statement to check if a number is even or odd.

## While and Do-While Loops
  - Create a `while` loop that prints Fibonacci numbers up to a certain limit.
  - Implement a `do-while` loop that prompts the user for input until a valid value is entered.

## Foreach Loop
  - Define an array of integers and initialize it with some values.
  - Use a `foreach` loop to iterate through the array and print its elements.

## Forever Loop
  - Write a program that toggles an output signal using a `forever` loop.
  - Add a delay inside the loop to control the frequency of toggling.

## Repeat Loop
  - Create a repeat loop that executes a block of code 5 times.
  - Perform some operation (e.g., addition, subtraction) within the loop.

## Break and Continue
  - Use a loop to iterate through an array of strings.
  - If a specific condition is met (e.g., string length exceeds 5 characters), break out of the loop.
  - Otherwise, continue to the next iteration.
