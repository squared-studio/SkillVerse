# Designing a Communication Protocol

## Implementing UART (Universal Asynchronous Receiver/Transmitter)
UART is a serial communication protocol used for asynchronous data transmission.

### Example: Simple UART Transmitter
```SV
module uart_tx (
    input logic clk,
    input logic reset,
    input logic [7:0] data_in,
    input logic start,
    output logic tx,
    output logic busy
);
    typedef enum logic [2:0] {IDLE, START, DATA, STOP} state_t;
    state_t state, next_state;
    logic [2:0] bit_count;
    logic [7:0] shift_reg;

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            state <= IDLE;
            bit_count <= 3'b000;
            shift_reg <= 8'b00000000;
            tx <= 1'b1;
            busy <= 1'b0;
        end else begin
            state <= next_state;
            if (state == START) begin
                tx <= 1'b0;
                busy <= 1'b1;
            end else if (state == DATA) begin
                tx <= shift_reg[0];
                shift_reg <= shift_reg >> 1;
                bit_count <= bit_count + 1;
            end else if (state == STOP) begin
                tx <= 1'b1;
                busy <= 1'b0;
            end
        end
    end

    always_comb begin
        case (state)
            IDLE: next_state = start ? START : IDLE;
            START: next_state = DATA;
            DATA: next_state = (bit_count == 3'b111) ? STOP : DATA;
            STOP: next_state = IDLE;
            default: next_state = IDLE;
        endcase
    end
endmodule
```

## Designing SPI (Serial Peripheral Interface)
SPI is a synchronous serial communication protocol used for short-distance communication.

### Example: Simple SPI Master
```SV
module spi_master (
    input logic clk,
    input logic reset,
    input logic [7:0] data_in,
    input logic start,
    output logic sclk,
    output logic mosi,
    output logic cs,
    output logic busy
);
    typedef enum logic [1:0] {IDLE, TRANSFER, DONE} state_t;
    state_t state, next_state;
    logic [2:0] bit_count;
    logic [7:0] shift_reg;

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            state <= IDLE;
            bit_count <= 3'b000;
            shift_reg <= 8'b00000000;
            sclk <= 1'b0;
            mosi <= 1'b0;
            cs <= 1'b1;
            busy <= 1'b0;
        end else begin
            state <= next_state;
            if (state == TRANSFER) begin
                sclk <= ~sclk;
                if (sclk) begin
                    mosi <= shift_reg[7];
                    shift_reg <= shift_reg << 1;
                    bit_count <= bit_count + 1;
                end
            end else if (state == DONE) begin
                cs <= 1'b1;
                busy <= 1'b0;
            end
        end
    end

    always_comb begin
        case (state)
            IDLE: next_state = start ? TRANSFER : IDLE;
            TRANSFER: next_state = (bit_count == 3'b111) ? DONE : TRANSFER;
            DONE: next_state = IDLE;
            default: next_state = IDLE;
        endcase
    end
endmodule
```

## Testing and Verifying the Communication Protocols
Testing and verification ensure that the communication protocols work correctly under various conditions.

## Exercises

1. Design a UART receiver in SystemVerilog.
2. Implement an SPI slave module in SystemVerilog.
3. Write a testbench to verify the functionality of the UART transmitter and SPI master.
