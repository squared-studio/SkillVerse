# Interprocess Communications

## Introduction
Interprocess communication in SystemVerilog allows different processes to communicate and synchronize with each other. The primary mechanisms for interprocess communication are mailboxes and semaphores.

## Mailbox
A mailbox is a communication channel that allows processes to send and receive messages.

### Methods for Mailboxes
| Method     | Description                              | Example                    |
|------------|------------------------------------------|----------------------------|
| `put`      | Sends a message to the mailbox           | `mbox.put(42);`            |
| `get`      | Receives a message from the mailbox      | `mbox.get(msg);`           |
| `try_put`  | Non-blocking send to the mailbox         | `mbox.try_put(42);`        |
| `try_get`  | Non-blocking receive from the mailbox    | `mbox.try_get(msg);`       |

### Creating a Mailbox
A mailbox is created using the `mailbox` keyword.

```SV
mailbox mbox = new();
```

### Sending Messages
Messages are sent to a mailbox using the `put` method.

```SV
module mailbox_put_example;
  mailbox mbox = new();
  initial begin
    mbox.put(42);
    $display("Message sent: 42");
  end
endmodule
```

### Receiving Messages
Messages are received from a mailbox using the `get` method.

```SV
module mailbox_get_example;
  mailbox mbox = new();
  int msg;
  initial begin
    mbox.put(42);
    mbox.get(msg);
    $display("Message received: %0d", msg);
  end
endmodule
```

### Non-blocking Send and Receive
Non-blocking send and receive operations can be performed using the `try_put` and `try_get` methods.

```SV
module mailbox_try_example;
  mailbox mbox = new();
  int msg;
  initial begin
    if (mbox.try_put(42))
      $display("Message sent: 42");
    if (mbox.try_get(msg))
      $display("Message received: %0d", msg);
  end
endmodule
```

## Semaphore
A semaphore is a synchronization primitive that controls access to shared resources.

### Methods for Semaphores
| Method     | Description                              | Example                    |
|------------|------------------------------------------|----------------------------|
| `get`      | Acquires the semaphore                   | `sem.get();`               |
| `put`      | Releases the semaphore                   | `sem.put();`               |
| `try_get`  | Non-blocking acquire of the semaphore    | `sem.try_get();`           |
| `try_put`  | Non-blocking release of the semaphore    | `sem.try_put();`           |

### Creating a Semaphore
A semaphore is created using the `semaphore` keyword and initialized with a count.

```SV
semaphore sem = new(1);
```

### Acquiring a Semaphore
A semaphore is acquired using the `get` method.

```SV
module semaphore_get_example;
  semaphore sem = new(1);
  initial begin
    sem.get();
    $display("Semaphore acquired");
  end
endmodule
```

### Releasing a Semaphore
A semaphore is released using the `put` method.

```SV
module semaphore_put_example;
  semaphore sem = new(1);
  initial begin
    sem.get();
    $display("Semaphore acquired");
    sem.put();
    $display("Semaphore released");
  end
endmodule
```

### Non-blocking Acquire and Release
Non-blocking acquire and release operations can be performed using the `try_get` and `try_put` methods.

```SV
module semaphore_try_example;
  semaphore sem = new(1);
  initial begin
    if (sem.try_get())
      $display("Semaphore acquired");
    sem.put();
    $display("Semaphore released");
  end
endmodule
```

## Exercises
1. Create a mailbox and send a message to it. Then, receive the message and display it.
2. Use a semaphore to control access to a shared resource between two processes.
3. Implement non-blocking send and receive operations using a mailbox.
4. Implement non-blocking acquire and release operations using a semaphore.

## Conclusion
Interprocess communication mechanisms in SystemVerilog, such as mailboxes and semaphores, provide powerful tools for synchronizing and coordinating processes. Understanding these mechanisms is essential for writing efficient and effective hardware models and testbenches.
