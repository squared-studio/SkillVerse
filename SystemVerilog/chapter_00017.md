# SystemVerilog Assertions (SVA)

## Introduction
SystemVerilog Assertions (SVA) are used to specify and check properties of a design. They help in detecting and diagnosing errors by verifying that certain conditions hold true during simulation.

## Immediate Assertions
Immediate assertions are evaluated immediately when the statement is executed.

### Example
```SV
module immediate_assertion_example;
  int a = 5;
  initial begin
    assert (a > 0) else $fatal("Assertion failed: a is not greater than 0");
  end
endmodule
```

## Concurrent Assertions
Concurrent assertions are evaluated over a period of time and are used to check temporal properties.

### Example
```SV
module concurrent_assertion_example;
  logic clk, rst, a, b;
  initial begin
    clk = 0;
    rst = 1;
    a = 0;
    b = 0;
    #5 rst = 0;
    forever #5 clk = ~clk;
  end

  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      a <= 0;
      b <= 0;
    end else begin
      a <= ~a;
      b <= a;
    end
  end

  property p1;
    @(posedge clk) a |=> b;
  endproperty

  assert property (p1) else $fatal("Assertion failed: a |=> b");
endmodule
```

## Assertion Severity Levels
Assertions can have different severity levels: `fatal`, `error`, `warning`, and `info`.

### Example
```SV
module assertion_severity_example;
  int a = -1;
  initial begin
    assert (a >= 0) else $fatal("Fatal: a is negative");
    assert (a >= 0) else $error("Error: a is negative");
    assert (a >= 0) else $warning("Warning: a is negative");
    assert (a >= 0) else $info("Info: a is negative");
  end
endmodule
```

## Cover Properties
Cover properties are used to specify conditions that should be covered during simulation.

### Example
```SV
module cover_property_example;
  logic clk, rst, a, b;
  initial begin
    clk = 0;
    rst = 1;
    a = 0;
    b = 0;
    #5 rst = 0;
    forever #5 clk = ~clk;
  end

  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      a <= 0;
      b <= 0;
    end else begin
      a <= ~a;
      b <= a;
    end
  end

  cover property (@(posedge clk) a && b);
endmodule
```

## Exercises
1. Write an immediate assertion to check if a variable is positive.
2. Write a concurrent assertion to check if a signal follows another signal.
3. Use different assertion severity levels to report errors.
4. Write a cover property to check if a condition is met during simulation.

## Conclusion
SystemVerilog Assertions (SVA) provide powerful tools for specifying and checking properties of a design. Understanding how to use immediate and concurrent assertions, as well as cover properties, is essential for verifying and validating hardware designs.
