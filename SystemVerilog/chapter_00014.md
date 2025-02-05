# Class

## Introduction
SystemVerilog classes enable **object-oriented programming (OOP)** for building modular, reusable, and scalable testbenches. They encapsulate data (properties) and behaviors (methods), forming the foundation of verification methodologies like UVM. Key OOP principles include inheritance, polymorphism, and encapsulation, which promote code maintainability and reduce redundancy.

## Defining Classes
Classes are declared using the `class` keyword. By default, members are **public**; use `local` or `protected` to restrict access.

### Example: Basic Class
```SV
// Define a class with a property and method
class SimpleClass;
  int data;  // Public property (default)

  // Method to display data
  function void display();
    $display("data = %0d", data);
  endfunction
endclass
```

## Creating Objects
Objects are instantiated using the `new()` constructor. Memory is dynamically allocated, and objects are referenced via handles.

### Example: Object Instantiation
```SV
module test;
  initial begin
    SimpleClass obj = new();  // Create object
    obj.data = 42;            // Assign value to property
    obj.display();            // Call method (Output: "data = 42")
  end
endmodule
```

## Inheritance
Derived classes inherit properties/methods from a base class using `extends`. Use `super` to access parent class members.

### Example: Base and Derived Classes
```SV
// Base class
class Animal;
  string name;

  function void speak();
    $display("Animal sound");
  endfunction
endclass

// Derived class overriding method
class Dog extends Animal;
  function void speak();
    super.speak();       // Call base method (optional)
    $display("%0s barks: Woof!", name);
  endfunction
endclass

module test;
  initial begin
    Dog d = new();
    d.name = "Buddy";
    d.speak();  // Output: "Animal sound" followed by "Buddy barks: Woof!"
  end
endmodule
```

## Polymorphism
Achieved via **virtual methods**. A base handle can reference derived objects, invoking methods based on the actual object type.

### Example: Dynamic Method Dispatch
```SV
class Shape;
  virtual function void draw();
    $display("Drawing a shape");
  endfunction
endclass

class Circle extends Shape;
  function void draw();
    $display("Drawing a circle");
  endfunction
endclass

module test;
  initial begin
    Shape s;       // Base class handle
    s = new Circle();  // Assign derived object
    s.draw();      // Calls Circle's draw() (Output: "Drawing a circle")
  end
endmodule
```

## Encapsulation
Hide internal state using `local`/`protected` access modifiers. Expose controlled access via public methods.

### Example: Data Hiding
```SV
class BankAccount;
  local int balance;  // Private property

  // Public method to modify balance
  function void deposit(int amount);
    balance += amount;
  endfunction

  function int getBalance();
    return balance;
  endfunction
endclass

module test;
  initial begin
    BankAccount acc = new();
    acc.deposit(100);
    $display("Balance: $%0d", acc.getBalance());  // Output: "Balance: $100"
    // acc.balance = 50;  // Illegal: Direct access to local member
  end
endmodule
```

## Randomization
Generate constrained random values for verification using `rand` variables and `constraint` blocks.

### Example: Random Stimulus Generation
```SV
class Packet;
  rand bit [7:0] addr;  // Randomizable variable
  rand bit [3:0] size;

  // Constraints to limit values
  constraint valid_addr { addr inside {[1:255]}; }
  constraint valid_size { size > 0; size < 10; }
endclass

module test;
  initial begin
    Packet pkt = new();
    if (pkt.randomize())  // Check randomization success
      $display("Addr: %0d, Size: %0d", pkt.addr, pkt.size);
    else
      $display("Randomization failed");
  end
endmodule
```

## Exercises
1. **Basic Class**: Create a `Car` class with properties `model` (string) and `speed` (int), and a method `accelerate()` that increases speed by 10.
2. **Object Usage**: Instantiate a `Car`, set `model` to "Sedan", and call `accelerate()` twice. Display the final speed.
3. **Inheritance**: Derive `ElectricCar` from `Car`. Override `accelerate()` to increase speed by 20.
4. **Polymorphism**: Use a virtual `start_engine()` method in `Car`, override it in `ElectricCar`, and demonstrate dynamic dispatch.
5. **Encapsulation**: Make `speed` private in `Car` and add `getSpeed()`/`setSpeed()` methods.
6. **Randomization**: Create a `Transaction` class with random `addr`, `data`, and constraints for valid ranges.

**Key Enhancements**:
- Fixed encapsulation example to use `local` variables.
- Added practical context for OOP in verification.
- Clarified virtual methods and dynamic polymorphism.
- Improved constraint examples for randomization.
- Structured exercises to align with core concepts.

