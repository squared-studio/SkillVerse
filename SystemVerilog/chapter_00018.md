# Chapter 18: Coverage

## Introduction
Coverage in SystemVerilog is used to measure how thoroughly a design has been tested. It helps in identifying untested parts of the design and improving the overall quality of the verification process. Coverage can be classified into code coverage and functional coverage.

## Code Coverage
Code coverage measures how much of the design code has been executed during simulation. It includes statement coverage, branch coverage, and toggle coverage.

### Statement Coverage
Statement coverage measures the number of statements that have been executed.

### Example
```systemverilog
module statement_coverage_example;
  int a = 0;
  initial begin
    if (a == 0)
      $display("a is zero");
    else
      $display("a is not zero");
  end
endmodule
```

### Branch Coverage
Branch coverage measures the number of branches that have been executed.

### Example
```systemverilog
module branch_coverage_example;
  int a = 0;
  initial begin
    if (a == 0)
      $display("a is zero");
    else if (a == 1)
      $display("a is one");
    else
      $display("a is neither zero nor one");
  end
endmodule
```

### Toggle Coverage
Toggle coverage measures the number of times a signal changes its value.

### Example
```systemverilog
module toggle_coverage_example;
  logic clk;
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end
endmodule
```

## Functional Coverage
Functional coverage measures how well the functionality of the design has been tested. It includes covergroups, coverpoints, and cross coverage.

### Covergroups
Covergroups are used to define coverage points and collect coverage data.

### Example
```systemverilog
module covergroup_example;
  covergroup cg;
    coverpoint a;
    coverpoint b;
  endgroup

  int a, b;
  initial begin
    cg = new();
    a = 0;
    b = 1;
    cg.sample();
  end
endmodule
```

### Coverpoints
Coverpoints are used to specify the points in the design that need to be covered.

### Example
```systemverilog
module coverpoint_example;
  covergroup cg;
    coverpoint a;
  endgroup

  int a;
  initial begin
    cg = new();
    a = 0;
    cg.sample();
    a = 1;
    cg.sample();
  end
endmodule
```

### Cross Coverage
Cross coverage measures the coverage of combinations of different coverpoints.

### Example
```systemverilog
module cross_coverage_example;
  covergroup cg;
    coverpoint a;
    coverpoint b;
    cross a, b;
  endgroup

  int a, b;
  initial begin
    cg = new();
    a = 0;
    b = 1;
    cg.sample();
    a = 1;
    b = 0;
    cg.sample();
  end
endmodule
```

## Exercises
1. Write a module to measure statement coverage.
2. Write a module to measure branch coverage.
3. Write a module to measure toggle coverage.
4. Define a covergroup with coverpoints and collect coverage data.
5. Define cross coverage for different coverpoints and collect coverage data.

## Conclusion
Coverage in SystemVerilog provides powerful tools for measuring how thoroughly a design has been tested. Understanding how to use code coverage and functional coverage is essential for improving the quality of the verification process and ensuring that all parts of the design have been tested.
