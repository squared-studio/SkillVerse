# Chapter 8: Low Power Design Techniques

## Clock Gating
Clock gating is a technique used to reduce dynamic power consumption by disabling the clock signal to inactive modules.

### Example: Clock Gating
```systemverilog
module clock_gating (
    input logic clk,
    input logic enable,
    output logic gated_clk
);
    assign gated_clk = clk & enable;
endmodule
```

## Power Gating
Power gating reduces static power consumption by shutting off the power supply to inactive modules.

### Example: Power Gating
```systemverilog
module power_gating (
    input logic power_enable,
    output logic power
);
    assign power = power_enable ? 1'b1 : 1'b0;
endmodule
```

## Dynamic Voltage and Frequency Scaling (DVFS)
DVFS adjusts the voltage and frequency of a circuit dynamically based on workload requirements to save power.

### Example: DVFS
```systemverilog
module dvfs (
    input logic [1:0] mode,
    output logic [1:0] voltage,
    output logic [1:0] frequency
);
    always_comb begin
        case (mode)
            2'b00: begin
                voltage = 2'b01;
                frequency = 2'b01;
            end
            2'b01: begin
                voltage = 2'b10;
                frequency = 2'b10;
            end
            2'b10: begin
                voltage = 2'b11;
                frequency = 2'b11;
            end
            default: begin
                voltage = 2'b00;
                frequency = 2'b00;
            end
        endcase
    end
endmodule
```

## Exercises

1. Design a clock gating circuit that disables the clock when a specific condition is met.
2. Implement a power gating module that shuts off power to a block when not in use.
3. Write a SystemVerilog module to demonstrate dynamic voltage and frequency scaling based on different modes.
