# Designing a Simple Processor

## Designing the Datapath
The datapath of a processor includes all the components that process data, such as ALUs, registers, and multiplexers.

### Example: Simple ALU
```SV
module simple_alu (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [1:0] alu_op,
    output logic [3:0] result,
    output logic carry_out
);
    always_comb begin
        case (alu_op)
            2'b00: {carry_out, result} = a + b; // Addition
            2'b01: {carry_out, result} = a - b; // Subtraction
            2'b10: result = a & b;              // AND
            2'b11: result = a | b;              // OR
            default: result = 4'b0000;
        endcase
    end
endmodule
```

## Implementing the Control Unit
The control unit generates control signals to direct the operation of the datapath components.

### Example: Simple Control Unit
```SV
module control_unit (
    input logic [3:0] opcode,
    output logic [1:0] alu_op,
    output logic reg_write,
    output logic mem_read,
    output logic mem_write
);
    always_comb begin
        case (opcode)
            4'b0000: begin // ADD
                alu_op = 2'b00;
                reg_write = 1;
                mem_read = 0;
                mem_write = 0;
            end
            4'b0001: begin // SUB
                alu_op = 2'b01;
                reg_write = 1;
                mem_read = 0;
                mem_write = 0;
            end
            4'b0010: begin // AND
                alu_op = 2'b10;
                reg_write = 1;
                mem_read = 0;
                mem_write = 0;
            end
            4'b0011: begin // OR
                alu_op = 2'b11;
                reg_write = 1;
                mem_read = 0;
                mem_write = 0;
            end
            4'b0100: begin // LOAD
                alu_op = 2'b00;
                reg_write = 1;
                mem_read = 1;
                mem_write = 0;
            end
            4'b0101: begin // STORE
                alu_op = 2'b00;
                reg_write = 0;
                mem_read = 0;
                mem_write = 1;
            end
            default: begin
                alu_op = 2'b00;
                reg_write = 0;
                mem_read = 0;
                mem_write = 0;
            end
        endcase
    end
endmodule
```

## Integrating and Testing the Processor
Integrate the datapath and control unit to form a complete processor and test its functionality.

### Example: Simple Processor Integration
```SV
module simple_processor (
    input logic clk,
    input logic reset,
    input logic [3:0] instruction,
    input logic [3:0] data_in,
    output logic [3:0] data_out
);
    logic [3:0] alu_result;
    logic [1:0] alu_op;
    logic reg_write, mem_read, mem_write;
    logic [3:0] reg_a, reg_b, reg_out;

    control_unit cu (
        .opcode(instruction[3:0]),
        .alu_op(alu_op),
        .reg_write(reg_write),
        .mem_read(mem_read),
        .mem_write(mem_write)
    );

    simple_alu alu (
        .a(reg_a),
        .b(reg_b),
        .alu_op(alu_op),
        .result(alu_result)
    );

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            reg_a <= 4'b0000;
            reg_b <= 4'b0000;
            reg_out <= 4'b0000;
        end else if (reg_write) begin
            reg_out <= alu_result;
        end
    end

    assign data_out = reg_out;
endmodule
```

## Exercises

1. Design a 4-bit multiplier as part of the datapath.
2. Implement a more complex control unit with additional instructions.
3. Write a testbench to verify the functionality of the simple processor.
