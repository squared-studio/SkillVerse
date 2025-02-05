# SystemVerilog Assertions

## Introduction to Assertion-Based Verification
SystemVerilog Assertions (SVA) form a critical component of modern verification methodologies, enabling:
- Formal specification of design requirements
- Temporal property checking during simulation
- Coverage metric collection for verification completeness
- Early error detection in simulation and formal analysis

### Key Benefits
- Self-documenting design intent
- Reusable verification components
- Enhanced debug capabilities through failure context
- Support for both simulation and formal verification

## Assertion Types Comparison
| Feature             | Immediate Assertions          | Concurrent Assertions           |
|---------------------|-------------------------------|---------------------------------|
| Evaluation Trigger  | Procedural execution          | Clock edges or temporal events  |
| Temporal Checking   | Immediate (current values)    | Multi-cycle behavior            |
| Typical Usage       | Combinational checks          | Protocol verification           |
| Execution Context   | Procedural blocks             | Module scope or clocking blocks |
| Simulation Overhead | Low                           | Moderate                        |

## Immediate Assertions Deep Dive

### Syntax and Usage
```SV
assert (expression) [action_block]
[else [action_block]];
```

### Enhanced Example with Parameters
```SV
module param_checker #(MIN_VAL=0, MAX_VAL=255) (
  input logic [7:0] data
);
  always_comb begin
    assert (data >= MIN_VAL && data <= MAX_VAL)
    else $error("Value %0d out of range [%0d:%0d]",
                data, MIN_VAL, MAX_VAL);
  end
endmodule
```

**Best Practices:**
- Use in `always_comb` blocks for combinational checks
- Avoid side effects in assertion expressions
- Combine with parameters for reusable checks
- Prefer specific error messages with formatted strings

## Concurrent Assertions Architecture

### Clock Declaration Styles
```SV
// Explicit clock in property
property p1;
  @(posedge clk) a |-> b;
endproperty

// Default clocking block
default clocking main_clk @(posedge clk);
endclocking

property p2;
  a ##1 b;
endproperty
```

### Reset-Aware Assertions
```SV
property safe_transition;
  @(posedge clk) disable iff (rst)
  $rose(en) |-> ##[1:3] $fell(alarm);
endproperty
```

## Temporal Operators Reference

| Operator          | Description                          | Example                   |
|-------------------|--------------------------------------|---------------------------|
| `##n`             | Delay n cycles                       | `a ##2 b`                 |
| `[*n]`            | Consecutive repetition               | `a [*3]`                  |
| `[->n]`           | Non-consecutive goto repetition      | `a[->3] ##1 b`            |
| `[=n]`            | Non-consecutive occurrence           | `a[=3] ##1 b`             |
| `throughout`      | Maintain condition during sequence   | `a throughout s1 ##1 b`   |
| `within`          | Sequence containment                 | `s1 within s2`            |
| `and`             | Both sequences match                 | `s1 and s2`               |
| `or`              | Either sequence matches              | `s1 or s2`                |
| `intersect`       | Simultaneous match with timing       | `s1 intersect s2`         |

## Assertion Severity Hierarchy

| Severity Level    | Typical Usage Scenario               | Simulation Impact          |
|-------------------|--------------------------------------|----------------------------|
| `$fatal`          | Critical unrecoverable errors        | Terminates simulation      |
| `$error`          | Design requirement violations        | Increments error count     |
| `$warning`        | Potential issues requiring review    | Logs warning message       |
| `$info`           | Diagnostic information               | Logs status message        |
| `$system`         | Tool-specific system messages        | Varies by implementation   |

### Severity Usage Example
```SV
module traffic_light_checker(
  input logic clk,
  input logic [1:0] light
);
  property no_dual_red;
    @(posedge clk) !(light == 2'b11);
  endproperty

  assert property (no_dual_red)
    else $fatal("Safety violation: Both directions red");

  cover property (light == 2'b00)
    $info("All lights off state observed");
endmodule
```

## Coverage-Driven Verification

### Coverage Property Types
1. **Event Coverage**: `cover (event_expression)`
2. **Sequence Coverage**: `cover sequence (sequence_expr)`
3. **Property Coverage**: `cover property (property_expr)`

### Cross-Coverage Example
```SV
module protocol_coverage;
  logic clk, start, done;
  enum {IDLE, BUSY, DONE} state;

  covergroup cg @(posedge clk);
    start_state: coverpoint state {
      bins start_transition = (IDLE => BUSY);
    }
    completion: coverpoint done {
      bins normal = (1'b0 => 1'b1);
      bins timeout = (1'b0 => 1'b0);
    }
    start_done_cross: cross start_state, completion;
  endgroup

  cg cov_inst = new();
endmodule
```

## Advanced Assertion Techniques

### Recursive Properties
```SV
property consecutive_ones(max);
  int count;
  @(posedge clk)
  (data_in, count = (data_in) ? count+1 : 0) |->
  (count <= max);
endproperty

assert property (consecutive_ones(7));
```

### Assertion Bindings
```SV
// External module assertion binding
bind fifo fifo_assertions #(.DEPTH(16)) fifo_checks(.*);
```

## Debugging Methodologies

### Assertion Control Tasks
```SV
initial begin
  // Disable specific assertions
  $assertoff(0, top.dut.arbiter.check_priority);

  // Enable after reset
  wait(rst == 0);
  $asserton(0, top.dut.arbiter.check_priority);
end
```

### Waveform Markers
```SV
property mem_write_check;
  @(posedge clk)
  write_en |-> ##[1:2] (
    $rose(ack),
    $info("Write completed at %0t", $time)
  );
endproperty
```

## Best Practices Checklist
1. Use named properties for complex assertions
2. Synchronize assertions with design clock domains
3. Include `disable iff` for reset conditions
4. Avoid combinatorial loops in assertion expressions
5. Use coverage properties to track scenario execution
6. Parameterize assertions for reuse
7. Combine with functional coverage points
8. Document assertion purpose using comments
9. Use severity levels appropriately
10. Verify assertion activation in simulation reports

## Practical Exercises

### 1. Packet Protocol Verification
Create assertions for a simple packet protocol:
- Start bit detection
- 8-bit data transfer
- Even parity check
- Stop bit verification

```SV
module packet_checker(
  input logic clk,
  input logic start,
  input logic [7:0] data,
  input logic parity,
  input logic stop
);
  // Implement assertions here
endmodule
```

### 2. State Machine Coverage
Define coverage points for a UART controller state machine:
- Idle to Start state transition
- Data bits reception coverage
- Stop bit detection
- Error state coverage

### 3. Memory Access Checks
Develop assertions for a memory controller:
- Write/read address stability
- Data bus contention checks
- Write enable pulse width
- Read-after-write hazard detection

### 4. Bus Protocol Assertions
Implement AMBA AHB protocol checks:
- Address phase validity
- Data phase sequencing
- Burst mode transitions
- Error response handling

## Comprehensive Function Reference

| Construct         | Description                          | Example                                     |
|-------------------|--------------------------------------|---------------------------------------------|
| `sequence`        | Temporal sequence definition         | `sequence s1; a ##1 b; endsequence`         |
| `property`        | Assertion property definition        | `property p1; @(clk) a \|=> b; endproperty` |
| `assert`          | Check property validity              | `assert property (p1);`                     |
| `cover`           | Track property occurrence            | `cover property (p1);`                      |
| `assume`          | Constraint for formal verification   | `assume property (p1);`                     |
| `$past`           | Access previous values               | `$past(signal, n)`                          |
| `$rose`           | Detect rising edge                   | `$rose(enable)`                             |
| `$fell`           | Detect falling edge                  | `$fell(reset)`                              |
| `$stable`         | Check value stability                | `$stable(data)`                             |
| `$countones`      | Count set bits                       | `$countones(bus)`                           |
| `$onehot`         | Verify one-hot encoding              | `$onehot(state)`                            |
| `$isunknown`      | Check for X/Z values                 | `$isunknown(bus)`                           |

```SV
// Sample Solution: Immediate Assertion Check
module positive_checker #(type T=int) (
  input T value
);
  always_comb begin
    assert (value > 0)
    else $error("Value %0d not positive", value);
  end
endmodule
```
