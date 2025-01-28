# Task 12 : Simple SystemVerilog Exercises

## Self Study
- [INTERPROCESS COMMUNICATION                               ](https://www.chipverify.com/systemverilog/systemverilog-interprocess-communication)
- [SEMAPHORE                                                ](https://www.chipverify.com/systemverilog/systemverilog-semaphore)
- [MAILBOX                                                  ](https://www.chipverify.com/systemverilog/systemverilog-mailbox)
- [INTERFACE                                                ](https://www.chipverify.com/systemverilog/systemverilog-interface)
- [INTERFACE INTRO                                          ](https://www.chipverify.com/systemverilog/systemverilog-interface-intro)
- [INTERFACE BUNDLES                                        ](https://www.chipverify.com/systemverilog/systemverilog-interface-bundles)
- [MODPORT                                                  ](https://www.chipverify.com/systemverilog/systemverilog-modport)

## Interprocess Communication
  - Write a SystemVerilog program where two processes communicate using events. One process should generate a random number and the other process should print it.
  - Modify the above program to use named events.

## Semaphore
  - Write a SystemVerilog program where multiple processes access a shared resource using a semaphore.
  - Experiment with different semaphore counts and observe the behavior.

## Mailbox
  - Write a SystemVerilog program where one process sends a series of messages (numbers or strings) to another process via a mailbox.
  - Extend the program to use a bounded mailbox and handle the case when the mailbox is full.

## Interface
  - Define a simple interface for a bus with data, address, and control signals.
  - Write a module that uses this interface to perform read and write operations.

## Interface Intro
  - Write a testbench that uses the bus interface from the previous exercise.
  - The testbench should stimulate the bus with a sequence of read and write operations and check the responses.

## Interface Bundles
  - Modify the bus interface to include a bundle of control signals.
  - Update the module and testbench from the previous exercises to use the modified interface.

## Modport
  - Define a modport in the bus interface for the bus driver (write-only signals) and another modport for the bus monitor (read-only signals).
  - Update the module and testbench to use the appropriate modports.
