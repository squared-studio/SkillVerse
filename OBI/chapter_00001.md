# Open Bus Interface (OBI)

## Description

The Open Bus Interface (OBI) is a simple and efficient bus protocol designed for communication between master and slave devices in embedded systems. It supports both read and write operations with a straightforward handshake mechanism to ensure data integrity and synchronization. The OBI protocol is widely used in various applications due to its simplicity and ease of implementation. It allows for flexible data widths and supports byte-level access through byte enable signals. The protocol is designed to be scalable, making it suitable for a wide range of system architectures. The OBI protocol is particularly well-suited for systems that require low-latency communication and minimal overhead, making it ideal for real-time applications. The OBI protocol is open and royalty-free, encouraging adoption and collaboration within the embedded systems community. Its simplicity and efficiency make it a popular choice for designers looking to implement reliable communication between components in their systems. The OBI protocol defines a set of signals for communication, including address, data, and control signals. The protocol operates on a request-grant basis, where the master device sends a request to the slave device, and the slave responds with a grant signal when it is ready to process the request. The request completion is marked by the read valid signal for both read and write operations.

## Signals

- **arst_n:** Asynchronous reset (active low)
- **clk:** System clock signal
- **addr:** Address bus
- **we:** Write enable signal
- **wdata:** Write data bus
- **be:** Byte enable signals
- **req:** Request signal
- **gnt:** Grant signal
- **rdata:** Read data bus
- **rvalid:** Read valid signal

## Waveform

![Waveform](waveform.svg)

## Operations

### Reset

When the asynchronous reset signal (arst_n) is asserted low, the OBI master must set the request (req) signal to low. The OBI slave must set the grant (gnt) and rvalid signals to low.

### Read Operation

The master initiates a read operation by asserting the request (req) signal high and providing the address on the addr bus. The we must be set to low for a read operation. The bus must stay stable until the slave asserts the grant (gnt) signal high. Sebsequent request can follow immediately after the grant signal is asserted. The read operation is completed when the slave asserts the rvalid signal high and read data on the rdata bus is valid.

### Write Operation

The master initiates a write operation by asserting the request (req) signal high and providing the address on the addr bus, the data on the wdata bus, and the byte enable signals on the be bus. The we must be set to high for a write operation. The bus must stay stable until the slave asserts the grant (gnt) signal high. Subsequent request can follow immediately after the grant signal is asserted. The write operation is completed when the slave asserts the rvalid signal high. Rdata on the rdata bus is not valid for a write operation and should be ignored by the master.

##### Copyright (c) 2026 squared-studio

