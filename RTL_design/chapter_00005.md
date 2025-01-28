# Chapter 5: Designing Sequential Circuits

## Counters (Up/Down Counters)
Counters are sequential circuits that count in a binary sequence. They can count up, down, or in a specific pattern.

### Example: 4-bit Up Counter
```systemverilog
module up_counter (
    input logic clk,
    input logic reset,
    output logic [3:0] count
);
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            count <= 4'b0000;
        else
            count <= count + 1;
    end
endmodule
```

## Shift Registers
Shift registers are sequential circuits that shift data in a specific direction (left or right) on each clock cycle.

### Example: 4-bit Shift Register
```systemverilog
module shift_register (
    input logic clk,
    input logic reset,
    input logic d,
    output logic [3:0] q
);
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            q <= 4'b0000;
        else
            q <= {q[2:0], d};
    end
endmodule
```

## Finite State Machines (FSMs)
FSMs are sequential circuits that transition between different states based on inputs and current state.

### Example: Simple FSM
```systemverilog
module simple_fsm (
    input logic clk,
    input logic reset,
    input logic in,
    output logic out
);
    typedef enum logic [1:0] {S0, S1, S2, S3} state_t;
    state_t state, next_state;

    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            state <= S0;
        else
            state <= next_state;
    end

    always_comb begin
        case (state)
            S0: next_state = in ? S1 : S0;
            S1: next_state = in ? S2 : S0;
            S2: next_state = in ? S3 : S0;
            S3: next_state = in ? S3 : S0;
            default: next_state = S0;
        endcase
    end

    assign out = (state == S3);
endmodule
```

## Exercises

1. Design a 4-bit down counter using SystemVerilog.
2. Implement an 8-bit shift register in SystemVerilog.
3. Write a SystemVerilog module for a Moore FSM that detects a specific sequence of bits.
