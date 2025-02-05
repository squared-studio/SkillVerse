# Modules

## Introduction
Modules are the fundamental building blocks in SystemVerilog, enabling hierarchical and reusable design abstraction. They encapsulate:
- **Interface**: Defined through input/output ports
- **Functionality**: Internal logic using variables, nets, and processes (always/initial blocks)
- **Structure**: Instantiations of other modules

Key benefits include:
- Design partitioning for complexity management
- Reusability across projects
- Clear interface definitions for team collaboration

## Module Definition
### Basic Structure
```SV
module <module_name> [(port_list)];
  // Port declarations
  // Internal logic (variables, nets, processes)
  // Submodule instantiations
endmodule
```

### Example: Minimal Module
```SV
module sensor_interface;  // No ports
  // Internal register declaration
  logic [3:0] sensor_data;
endmodule
```

## Ports and Parameters
### Interface Definition
| Element      | Purpose                          | Syntax Example                     |
|--------------|----------------------------------|------------------------------------|
| Parameters   | Configuration constants          | `#(parameter WIDTH=32, DEPTH=64)` |
| Input Ports  | Receive external signals         | `input logic clk, input [7:0] cmd` |
| Output Ports | Drive external signals           | `output logic valid`              |
| Inout Ports  | Bidirectional signals            | `inout wire i2c_sda`              |

### Parameterized Module Example
```SV
module smart_buffer #(
  parameter DATA_WIDTH = 64,       // Default width
  parameter BUFFER_DEPTH = 8       // Default depth
)(
  input  logic clk,
  input  logic rst_n,              // Active-low reset
  input  logic [DATA_WIDTH-1:0] wr_data,
  output logic [DATA_WIDTH-1:0] rd_data
);
  // Internal storage declaration
  logic [DATA_WIDTH-1:0] buffer [0:BUFFER_DEPTH-1];

  // Functionality implementation
  // ...
endmodule
```

## Module Instantiation
### Connection Methods
1. **Positional Connection** (Not Recommended)
   ```SV
   d_flipflop uut (clk, rst_n, d_in, q_out);
   ```

2. **Named Connection** (Recommended)
   ```SV
   smart_buffer #(
     .DATA_WIDTH(128),        // Parameter override
     .BUFFER_DEPTH(16)
   ) data_cache (
     .clk(sys_clk),           // Clock connection
     .rst_n(main_reset_n),    // Reset connection
     .wr_data(network_payload),
     .rd_data(processor_input)
   );
   ```

### Hierarchical Design Example
**Submodule (Data Processing)**
```SV
module data_processor #(parameter PRECISION=16) (
  input  logic clk,
  input  logic [PRECISION-1:0] raw_input,
  output logic [PRECISION-1:0] calibrated_output
);
  always_ff @(posedge clk) begin
    // Calibration logic
    calibrated_output <= raw_input * 2'd3;
  end
endmodule
```

**Top-Level Integration**
```SV
module sensor_subsystem (
  input  logic core_clk,
  input  logic [15:0] sensor_adc,
  output logic [15:0] processed_data
);
  // Clock generator instantiation
  clock_divider clk_gen (
    .master_clk(core_clk),
    .divided_clk(proc_clk)
  );

  // Data processing chain
  data_processor #(.PRECISION(16)) dsp_unit (
    .clk(proc_clk),
    .raw_input(sensor_adc),
    .calibrated_output(processed_data)
  );

  // Additional modules...
endmodule
```

## Testbench Integration
### Clock/Reset Generation
```SV
module tb;
  logic clk_100MHz;
  logic system_reset;

  // Clock generation (100MHz, 50% duty)
  initial begin
    clk_100MHz = 0;
    forever #5 clk_100MHz = ~clk_100MHz;
  end

  // Reset sequence
  initial begin
    system_reset = 1'b1;
    #100 system_reset = 1'b0;   // Reset release after 100ns
  end

  // Device Under Test (DUT) instantiation
  sensor_subsystem dut (
    .core_clk(clk_100MHz),
    .sensor_adc(16'h0000),
    .processed_data()
  );
endmodule
```

## Best Practices
1. **Naming Conventions**
   - Module names: `lowercase_with_underscores`
   - Parameters: `UPPER_SNAKE_CASE`
   - Clock: `clk_<frequency>MHz`
   - Reset: `rst_<active_high_low>`

2. **Port Declaration Styles**
   Prefer ANSI-style for compactness:
   ```SV
   module uart_tx (
     input  logic clk_50MHz,
     input  logic [7:0] tx_data,
     output logic tx_active
   );
   ```

3. **Parameter Validation**
   ```SV
   if (BUFFER_DEPTH < 2) begin
     $error("Buffer depth must be ≥2");
   end
   ```

## Exercises
1. **Basic Module Creation**
   Create a `serial_encoder` module with:
   - Inputs: `clk`, `data_valid`, `byte_data[7:0]`
   - Output: `serial_out`

2. **Parameterized Design**
   Implement a `configurable_fifo` with parameters:
   - `DATA_WIDTH` (default 8-bit)
   - `DEPTH` (default 16 entries)

3. **Hierarchical Integration**
   Connect these modules in a `network_interface`:
   - 2× `configurable_fifo` (input/output buffers)
   - 1× `serial_encoder`
   - 1× `packet_formatter`

4. **Testbench Development**
   Create a self-checking testbench that:
   - Generates 100MHz clock with 10% duty cycle variance
   - Implements power-on reset sequence
   - Verifies FIFO overflow protection

