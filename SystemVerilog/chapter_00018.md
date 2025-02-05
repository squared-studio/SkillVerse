# Coverage

## Introduction
Coverage is a critical metric in verification that quantifies how thoroughly a design has been tested. It identifies gaps in testing and ensures alignment between verification efforts and design requirements. SystemVerilog supports two primary coverage types:

1. **Code Coverage** - Automatically tracks executed design code (e.g., statements, branches).
2. **Functional Coverage** - User-defined metrics to verify design specifications.

*Key Insight:* Code coverage answers "Did we execute all code?", while functional coverage answers "Did we test all required scenarios?"

## Code Coverage
Automatically measured by simulation tools. Three key metrics:

### 1. Statement Coverage
Measures percentage of executed statements.

```SV
module statement_cov;
  logic [1:0] mode = 2'b00;

  initial begin
    if (mode == 2'b00) begin
      $display("Mode A");  // <-- Always executed
    end else begin
      $display("Mode B");  // <-- Never executed (0% coverage)
    end
  end
endmodule
```
*Coverage Result:* 50% (1/2 statements executed)*

### 2. Branch Coverage
Measures all possible code branch executions.

```SV
module branch_cov;
  logic [1:0] state = 2'b01;

  initial begin
    case(state)
      2'b00: $display("State A");  // Not covered
      2'b01: $display("State B");  // Covered
      2'b10: $display("State C");  // Not covered
      default: $display("Error");  // Not covered
    endcase
  end
endmodule
```
*Coverage Result:* 25% branch coverage (1/4 branches taken)*

### 3. Toggle Coverage
Tracks signal value changes (0→1 and 1→0).

```SV
module toggle_cov;
  logic clk, enable = 0;

  initial begin
    #10 enable = 1;  // Toggle 0→1 (covered)
    #10 enable = 0;  // Toggle 1→0 (covered)
    #10 $finish;
  end
endmodule
```
*Coverage Result:* 100% toggle coverage for `enable`*

## Functional Coverage
User-defined scenarios to verify design behavior.

### 1. Covergroups
Containers for coverage points and cross-coverage definitions.

```SV
module func_cov;
  covergroup cg @(posedge clk);
    option.per_instance = 1;

    // Coverage point for 2-bit address
    addr_cp: coverpoint addr {
      bins low    = {[0:15]};
      bins mid    = {[16:31]};
      bins high   = {[32:47]};
    }

    // Cross coverage between addr and rw_op
    rw_x: cross addr_cp, rw_op;
  endgroup

  logic clk, [5:0] addr;
  logic rw_op;  // 0=read, 1=write
  cg cov_inst = new();

  // Test scenario
  initial begin
    for(int i=0; i<48; i++) begin
      @(negedge clk);
      addr = i;
      rw_op = i%2;
    end
  end
endmodule
```
*Key Features:*
- Temporal sampling at clock edges
- Custom bins for address ranges
- Cross-correlation between address and read/write operations

### 2. Coverpoints
Specific variables or expressions to monitor.

```SV
covergroup data_cg;
  // Track 4-bit data values
  data_cp: coverpoint data {
    bins zero = {0};          // Single value
    bins small = {[1:5]};     // Value range
    bins large = {[10:$]};    // Automatic upper limit
    illegal_bins err = {6};   // Forbidden value
  }
endgroup
```

### 3. Cross Coverage
Verifies combinations of variables.

```SV
covergroup protocol_cg;
  mode_cp: coverpoint mode { bins low_power, high_perf; }
  speed_cp: coverpoint speed { bins s1 = {1}, s2 = {2}; }

  // All mode-speed combinations
  mode_speed_x: cross mode_cp, speed_cp;
endgroup
```
*Coverage Target:* 2 modes × 2 speeds = 4 combinations

## Practical Exercises

1. **Statement Coverage Challenge**
   Create a module with a 3:1 multiplexer and achieve 100% statement coverage.

2. **Branch Coverage Scenario**
   Implement a traffic light controller with states RED→YELLOW→GREEN and verify all transitions.

3. **Toggle Coverage Task**
   Design a 4-bit counter with asynchronous reset and measure toggle coverage after 15 cycles.

4. **Functional Coverage Implementation**
   Define a covergroup for an 8-bit data bus with bins for prime numbers and powers of two.

5. **Cross Coverage Problem**
   Create cross coverage between a 2-bit opcode and 1-bit error flag, sampling all valid combinations.

## Best Practices
1. Combine code and functional coverage for comprehensive verification
2. Use exclusion filters for non-critical coverage points
3. Regularly analyze coverage holes with verification tools
4. Prioritize corner cases in cross coverage definitions
5. Maintain coverage databases across regression runs

*Remember:* High coverage percentage ≠ bug-free design, but low coverage almost certainly indicates missing tests.