# Open Bus Interface (OBI)

## Description

The Open Bus Interface (OBI) is a simple and efficient bus protocol designed for communication between master and slave devices in embedded systems. It is open, royalty-free, and widely adopted due to its straightforward implementation and minimal overhead.

### Key Features

- **Simple Handshake Mechanism:** Request-grant protocol ensures synchronized communication
- **Flexible Data Width:** Supports configurable address and data bus widths
- **Byte-Level Access:** Byte enable signals allow granular write operations
- **Low Latency:** Minimal protocol overhead enables real-time applications
- **Scalable:** Suitable for various system architectures and complexities

### Protocol Overview

The OBI protocol operates on a request-grant-response basis:
1. **Request Phase:** Master asserts request (req) with address and control signals
2. **Grant Phase:** Slave responds with grant (gnt) when ready to accept the transaction
3. **Response Phase:** Slave completes the transaction by asserting read valid (rvalid)

Both read and write operations follow this three-phase handshake, ensuring data integrity and proper synchronization between master and slave devices.

## Signals

### Clock and Reset

- **clk:** System clock signal (all signals are sampled on the rising edge)
- **arst_n:** Asynchronous reset, active low (resets the interface to idle state)

### Request Channel (Master to Slave)

- **req:** Request signal (1 = transaction requested, 0 = no transaction)
- **addr:** Address bus (specifies the target address for read/write operation)
- **we:** Write enable signal (1 = write operation, 0 = read operation)
- **wdata:** Write data bus (valid only when we = 1)
- **be:** Byte enable signals (indicates which bytes of wdata are valid)

### Response Channel (Slave to Master)

- **gnt:** Grant signal (1 = slave accepts the request, 0 = slave is busy)
- **rvalid:** Read valid signal (1 = response data is valid)
- **rdata:** Read data bus (valid data when rvalid = 1)

## Waveform

![Waveform](waveform.svg)

## Operations

### Reset

When the asynchronous reset signal (arst_n) is asserted low, all interface signals must be reset to their default states:

**Master Requirements:**
- Set req = 0 (no active request)
- Address, we, wdata, and be signals can be in any state (don't care)

**Slave Requirements:**
- Set gnt = 0 (not ready to accept requests)
- Set rvalid = 0 (no valid response)
- rdata can be in any state (don't care)

The interface must remain in reset state until arst_n is deasserted high. Normal operation can begin on the first rising clock edge after arst_n is released.

### Read Operation

The master initiates a read operation by:
1. Asserting req = 1
2. Driving the target address on addr
3. Setting we = 0 to indicate a read
4. Optionally setting be to indicate which bytes are needed (implementation-dependent)

**Timing Requirements:**
- All request signals (req, addr, we) must remain stable until gnt is asserted
- Once gnt = 1, the slave has accepted the request
- The master can issue a subsequent request immediately after receiving gnt (pipelined operation)
- The request and grant phases are decoupled from the response phase

**Response Phase:**
- The slave completes the read by asserting rvalid = 1
- When rvalid = 1, valid read data is available on rdata
- The master must sample rdata on the rising clock edge when rvalid = 1
- Multiple requests can be outstanding, with responses returned in order or out-of-order (implementation-dependent)

### Write Operation

The master initiates a write operation by:
1. Asserting req = 1
2. Driving the target address on addr
3. Setting we = 1 to indicate a write
4. Driving the write data on wdata
5. Setting be to indicate which bytes should be written

**Timing Requirements:**
- All request signals (req, addr, we, wdata, be) must remain stable until gnt is asserted
- Once gnt = 1, the slave has accepted the write request and captured the data
- The master can issue a subsequent request immediately after receiving gnt (pipelined operation)
- The request and grant phases are decoupled from the response phase

**Response Phase:**
- The slave completes the write by asserting rvalid = 1
- When rvalid = 1, the write operation has been completed successfully
- The rdata bus is not used during write operations and should be ignored by the master
- The be signal allows partial word writes; only bytes with be[i] = 1 are written to memory
- Multiple write requests can be outstanding, with completions signaled via rvalid

**Byte Enable Examples:**
- For a 32-bit data bus: be = 4'b1111 writes all 4 bytes
- be = 4'b0001 writes only byte 0 (least significant byte)
- be = 4'b1100 writes only bytes 2 and 3 (upper halfword)

##### Copyright (c) 2026 squared-studio
