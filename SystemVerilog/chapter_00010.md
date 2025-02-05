# Interprocess Communications

## Introduction
Interprocess Communication (IPC) in SystemVerilog is essential for coordinating parallel processes in testbenches and design models. Processes often need to exchange data or synchronize their execution to avoid race conditions and ensure correct behavior. SystemVerilog provides two primary mechanisms for IPC: **mailboxes** for message passing and **semaphores** for resource access control. This guide explores their usage, differences, and practical applications.


## Mailbox
A mailbox is a communication channel that allows processes to exchange messages safely. It can be **bounded** (fixed size) or **unbounded**, and supports parameterization for type-specific data.

### Methods for Mailboxes
| Method       | Description                                  | Return Value         | Example                    |
|--------------|----------------------------------------------|----------------------|----------------------------|
| `put()`      | Blocking send. Waits if the mailbox is full. | `void`               | `mbox.put(42);`            |
| `get()`      | Blocking receive. Waits if the mailbox is empty. | `void`          | `mbox.get(msg);`           |
| `try_put()`  | Non-blocking send. Fails if full.            | `1` (success) / `0`  | `if (mbox.try_put(42)) ...`|
| `try_get()`  | Non-blocking receive. Fails if empty.        | `1` (success) / `0`  | `if (mbox.try_get(msg)) ...`|

### Creating a Mailbox
```SV
mailbox mbox = new();       // Unbounded mailbox
mailbox #(string) str_mbox = new(5); // Bounded (size=5) for strings
```

### Example: Two Processes Exchanging Data
```SV
module mailbox_example;
  mailbox #(int) mbox = new(3); // Bounded mailbox with capacity 3

  // Process 1: Sender
  initial begin
    for (int i=1; i<=4; i++) begin
      if (mbox.try_put(i))
        $display("[Sender] Sent: %0d", i);
      else
        $display("[Sender] Mailbox full. Failed to send: %0d", i);
      #10;
    end
  end

  // Process 2: Receiver
  initial begin
    int received;
    #15; // Let sender fill the mailbox first
    while (mbox.try_get(received))
      $display("[Receiver] Received: %0d", received);
  end
endmodule
```
**Key Points**:
- `try_put()` fails when the mailbox is full.
- Parameterization (`#(int)`) ensures type safety.


## Semaphore
A semaphore controls access to shared resources using a **counter**. Processes acquire/release "keys" to synchronize.

### Methods for Semaphores
| Method       | Description                                  | Parameters           | Example                    |
|--------------|----------------------------------------------|----------------------|----------------------------|
| `get()`      | Acquires `N` keys (blocks if unavailable).   | `N=1` (default)      | `sem.get(2);`              |
| `put()`      | Releases `N` keys.                           | `N=1` (default)      | `sem.put(2);`              |
| `try_get()`  | Non-blocking acquire. Returns success/fail.  | `N=1` (default)      | `if (sem.try_get(2)) ...`  |
| `try_put()`  | Non-blocking release. Rarely used.           | `N=1` (default)      | `sem.try_put(2);`          |

### Example: Resource Access Control
```SV
module semaphore_example;
  semaphore sem = new(3); // 3 keys available
  int shared_resource = 0;

  // Process 1
  initial begin
    sem.get(1); // Acquire 1 key
    $display("[P1] Accessed resource at t=%0t", $time);
    shared_resource += 1;
    #20;
    sem.put(1); // Release key
    $display("[P1] Released resource at t=%0t", $time);
  end

  // Process 2
  initial begin
    #10;
    sem.get(1);
    $display("[P2] Accessed resource at t=%0t", $time);
    shared_resource += 1;
    #10;
    sem.put(1);
    $display("[P2] Released resource at t=%0t", $time);
  end
endmodule
```
**Output**:
```
[P1] Accessed resource at t=0
[P2] Accessed resource at t=10  // P2 waits until P1 releases at t=20? Wait, no—semaphore has 3 keys. Wait, initial count is 3. So P1 and P2 can both acquire keys immediately. Let me adjust the example to show contention.

```

Hmm, the example may not show waiting. Let's correct that. Maybe set semaphore to 1 key initially.

Let’s adjust the semaphore example to have 1 key:

```SV
semaphore sem = new(1); // Only 1 key available
```

Now, Process 1 acquires the key at t=0, holds it until t=20. Process 2 tries to acquire at t=10 but blocks until t=20 when Process 1 releases.


## Comparison: Mailboxes vs Semaphores
| **Feature**      | **Mailbox**                          | **Semaphore**                     |
|-------------------|--------------------------------------|------------------------------------|
| **Purpose**       | Data exchange between processes      | Resource access control           |
| **Blocking**      | Yes (with `put()`/`get()`)           | Yes (with `get()`)                |
| **Data Type**     | Supports parameterization (e.g., `#(int)`) | Manages keys (no data)      |
| **Use Cases**     | Producer-consumer models             | Critical section synchronization  |


## Exercises
1. **Mailbox with Strings**: Create a mailbox parameterized for `string` type. Send "Hello" from one process and receive it in another.
2. **Shared Counter Protection**: Implement a counter accessed by two processes. Use a semaphore to ensure atomic increments.
3. **Bounded Mailbox**: Create a bounded mailbox of size 2. Demonstrate `try_put()` failures when full.
4. **Semaphore Contention**: Initialize a semaphore with 2 keys. Spawn 4 processes that each acquire 1 key, showing how 2 processes proceed immediately while others wait.


## Best Practices
- **Avoid Deadlocks**: Always release semaphores after acquisition.
- **Bounded Mailboxes**: Use `try_put()`/`try_get()` to handle overflow/underflow.
- **Parameterization**: Use `mailbox #(type)` for type safety.


