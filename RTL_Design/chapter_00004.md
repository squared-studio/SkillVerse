# Designing Combinational Circuits

## Multiplexers and Demultiplexers
Multiplexers (MUX) select one of many input signals and forward the selected input to a single output line. Demultiplexers (DEMUX) take a single input signal and select one of many data output lines.

### Example: 4-to-1 Multiplexer
```SV
module mux_4to1 (
    input logic [3:0] data,
    input logic [1:0] sel,
    output logic y
);
    assign y = (sel == 2'b00) ? data[0] :
               (sel == 2'b01) ? data[1] :
               (sel == 2'b02) ? data[2] :
               data[3];
endmodule
```

## Encoders and Decoders
Encoders convert 2^n input lines into an n-bit code. Decoders perform the reverse operation, converting an n-bit code into 2^n output lines.

### Example: 2-to-4 Decoder
```SV
module decoder_2to4 (
    input logic [1:0] in,
    output logic [3:0] out
);
    assign out = 1 << in;
endmodule
```

## Arithmetic Circuits
Arithmetic circuits perform arithmetic operations like addition, subtraction, and multiplication.

### Example: 4-bit Adder
```SV
module adder_4bit (
    input logic [3:0] a,
    input logic [3:0] b,
    output logic [3:0] sum,
    output logic carry_out
);
    assign {carry_out, sum} = a + b;
endmodule
```

## Exercises

1. Design an 8-to-1 multiplexer using SystemVerilog.
2. Implement a 3-to-8 decoder in SystemVerilog.
3. Write a SystemVerilog module for a 4-bit subtractor.
