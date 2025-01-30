# Simple SystemVerilog Exercises

## Self Study
- [SOLVE BEFORE                                             ](https://www.chipverify.com/systemverilog/systemverilog-solve-before)
- [STATIC CONSTRAINTS                                       ](https://www.chipverify.com/systemverilog/systemverilog-static-constraints)
- [RANDOMIZATION METHODS                                    ](https://www.chipverify.com/systemverilog/systemverilog-randomization-methods)
- [INLINE CONSTRAINTS                                       ](https://www.chipverify.com/systemverilog/systemverilog-inline-constraints)
- [SOFT CONSTRAINTS                                         ](https://www.chipverify.com/systemverilog/systemverilog-soft-constraints)
- [DISABLE CONSTRAINTS                                      ](https://www.chipverify.com/systemverilog/systemverilog-disable-constraints)
- [DISABLE RANDOMIZATION                                    ](https://www.chipverify.com/systemverilog/systemverilog-disable-randomization)
- [RANDCASE                                                 ](https://www.chipverify.com/systemverilog/systemverilog-randcase)

## `solve` before
  - Define a class with several interdependent properties and a constraint that uses the `solve` before construct.
  - Instantiate the class and randomize it to observe the effect of the `solve` before construct.

## Static Constraints
  - Define a class with a static constraint.
  - Instantiate the class and randomize it to observe the effect of the static constraint.

## Randomization Methods
  - Write a testbench that uses the `randomize()` and `pre_randomize()` methods to randomize a class object.
  - Observe the difference between the two methods.

## Inline Constraints
  - Define a class with an inline constraint.
  - Instantiate the class and randomize it to observe the effect of the inline constraint.

## Soft Constraints
  - Define a class with a soft constraint.
  - Instantiate the class and randomize it to observe the effect of the soft constraint.

## Disable Constraints
  - Define a class with several constraints and a method that disables one of them.
  - Instantiate the class, call the method, and randomize the object to observe the effect of disabling the constraint.

## Disable Randomization
  - Define a class with a method that disables randomization of one of its properties.
  - Instantiate the class, call the method, and randomize the object to observe the effect of disabling randomization.

## `randcase`
  - Write a testbench that uses the `randcase` construct to select one of several randomization scenarios.
  - Run the testbench multiple times to observe the different scenarios.
