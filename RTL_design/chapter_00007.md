# Chapter 7: Memory Design

## Designing RAM and ROM
RAM (Random Access Memory) and ROM (Read-Only Memory) are essential components in digital systems. RAM is used for temporary storage, while ROM is used for permanent storage.

### Example: Simple RAM
```systemverilog
module simple_ram (
    input logic clk,
    input logic we,
    input logic [3:0] addr,
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    logic [7:0] mem [0:15];

    always_ff @(posedge clk) begin
        if (we)
            mem[addr] <= data_in;
        data_out <= mem[addr];
    end
endmodule
```

### Example: Simple ROM
```systemverilog
module simple_rom (
    input logic [3:0] addr,
    output logic [7:0] data_out
);
    logic [7:0] mem [0:15] = '{8'h00, 8'h01, 8'h02, 8'h03, 8'h04, 8'h05, 8'h06, 8'h07,
                               8'h08, 8'h09, 8'h0A, 8'h0B, 8'h0C, 8'h0D, 8'h0E, 8'h0F};

    assign data_out = mem[addr];
endmodule
```

## FIFO (First-In-First-Out) Buffers
FIFO buffers are used to store data in the order it was received and retrieve it in the same order.

### Example: Simple FIFO
```systemverilog
module simple_fifo (
    input logic clk,
    input logic reset,
    input logic wr_en,
    input logic rd_en,
    input logic [7:0] data_in,
    output logic [7:0] data_out,
    output logic empty,
    output logic full
);
    logic [7:0] fifo_mem [0:15];
    logic [3:0] wr_ptr, rd_ptr;
    logic [4:0] count;

    assign empty = (count == 0);
    assign full = (count == 16);

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            wr_ptr <= 0;
            rd_ptr <= 0;
            count <= 0;
        end else begin
            if (wr_en && !full) begin
                fifo_mem[wr_ptr] <= data_in;
                wr_ptr <= wr_ptr + 1;
                count <= count + 1;
            end
            if (rd_en && !empty) begin
                data_out <= fifo_mem[rd_ptr];
                rd_ptr <= rd_ptr + 1;
                count <= count - 1;
            end
        end
    end
endmodule
```

## Memory Access and Timing
Proper timing and control signals are crucial for accessing memory efficiently and correctly.

## Exercises

1. Design a dual-port RAM in SystemVerilog.
2. Implement a 16x8 ROM with predefined values in SystemVerilog.
3. Write a SystemVerilog module for a circular buffer (FIFO) with parameterized depth.
