# Task 11 : Simple SystemVerilog Exercises

## Self Study
- [UNIQUE PRIORITY IF ELSE                                  ](https://www.chipverify.com/systemverilog/systemverilog-unique-priority-if-else)
- [UNIQUE PRIORITY CASE                                     ](https://www.chipverify.com/systemverilog/systemverilog-unique-priority-case)
- [BLOCKING NON BLOCKING STATEMENTS                         ](https://www.chipverify.com/verilog/verilog-blocking-non-blocking-statements)
- [EVENT                                                    ](https://www.chipverify.com/systemverilog/systemverilog-event)
- [FUNCTIONS                                                ](https://www.chipverify.com/systemverilog/systemverilog-functions)
- [TASK                                                     ](https://www.chipverify.com/verilog/verilog-task)
- [THREADS                                                  ](https://www.chipverify.com/systemverilog/systemverilog-threads)
- [FORK JOIN                                                ](https://www.chipverify.com/systemverilog/systemverilog-fork-join)
- [FORK JOIN ANY                                            ](https://www.chipverify.com/systemverilog/systemverilog-fork-join-any)
- [FORK JOIN NONE                                           ](https://www.chipverify.com/systemverilog/systemverilog-fork-join-none)
- [DISABLE FORK                                             ](https://www.chipverify.com/systemverilog/systemverilog-disable-fork)
- [WAIT FORK                                                ](https://www.chipverify.com/systemverilog/systemverilog-wait-fork)

## Unique and Priority Constructs
  - Create a module that uses both `unique` and `priority` keywords for combinational logic.
  - Define multiple conditions and ensure that the unique and priority blocks behave as expected.

## Blocking and Non-blocking Assignments
  - Write a module that uses both blocking (`=`) and non-blocking (`<=`) assignments.
  - Observe the differences in behavior during simulation.

## Events and Sensitivity
  - Declare an event called `clk_event` using the `event` keyword.
  - Use the `@(clk_event)` construct to trigger a block of code when the event occurs.

## Functions
  - Create a function that calculates the factorial of an input integer.
  - Test the function by calling it with different input values.

## Tasks
  - Define a task that takes two input arguments and prints their sum.
  - Call the task from within a module.

## Threads and Fork-Join
  - Write a program that uses multiple threads (using `fork` and `join`) to perform parallel tasks.
  - Demonstrate synchronization and communication between threads.

## Fork-Join Any and None
  - Use the `fork-join-any` construct to execute multiple blocks concurrently.
  - Implement a scenario where any one of the blocks completes first.

## Disabling Fork Blocks
  - Create a fork block with multiple child blocks.
  - Use the `disable` keyword to selectively disable specific child blocks.

## Wait-Fork and Timing Control
  - Combine `wait` statements with `fork-join` constructs to control timing.
  - Illustrate how to wait for specific events or conditions before proceeding.
