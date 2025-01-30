# Writing Testbenches

## Structure of a Testbench
A testbench is a top-level module used to verify the functionality of a design. It typically includes stimulus generation, response checking, and result reporting.

### Example
A testbench for an ALU might include modules for generating input operands, checking the ALU's output, and reporting the results.

## Stimulus Generation
Stimulus generation involves creating input signals to drive the design under test (DUT). This can be done using directed tests, random tests, or a combination of both.

### Example
Directed tests: Manually creating specific input scenarios to test the design.
Random tests: Automatically generating random input scenarios to test the design.

## Checker and Monitor Implementation
Checkers and monitors are used to verify the correctness of the DUT's outputs. Checkers compare the actual outputs with expected values, while monitors observe and log signal activities for analysis.

### Example
Checker: A module that compares the ALU's output with the expected result for given input operands.
Monitor: A module that logs all input and output signals of the ALU for later analysis.

## Exercises
1. **Describe the main components of a testbench.**
2. **Explain the difference between directed tests and random tests in stimulus generation.**
3. **What are checkers and monitors, and how are they used in a testbench?**
