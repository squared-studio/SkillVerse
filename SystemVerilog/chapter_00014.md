# Classes

## Introduction
Classes in SystemVerilog are used to create object-oriented models. They provide a way to encapsulate data and functionality, making the design more modular and reusable.

## Defining Classes
Classes are defined using the `class` keyword.

### Example
```SV
class SimpleClass;
  int a;
  function void display();
    $display("a: %0d", a);
  endfunction
endclass
```

## Creating Objects
Objects are instances of classes and are created using the `new` keyword.

### Example
```SV
module class_example;
  initial begin
    SimpleClass obj = new();
    obj.a = 10;
    obj.display();
  end
endmodule
```

## Inheritance
Inheritance allows a class to inherit properties and methods from another class.

### Example
```SV
class BaseClass;
  int a;
  function void display();
    $display("BaseClass a: %0d", a);
  endfunction
endclass

class DerivedClass extends BaseClass;
  int b;
  function void display();
    super.display();
    $display("DerivedClass b: %0d", b);
  endfunction
endclass

module inheritance_example;
  initial begin
    DerivedClass obj = new();
    obj.a = 10;
    obj.b = 20;
    obj.display();
  end
endmodule
```

## Polymorphism
Polymorphism allows a method to behave differently based on the object that calls it.

### Example
```SV
class BaseClass;
  virtual function void display();
    $display("BaseClass display");
  endfunction
endclass

class DerivedClass extends BaseClass;
  function void display();
    $display("DerivedClass display");
  endfunction
endclass

module polymorphism_example;
  initial begin
    BaseClass obj;
    obj = new DerivedClass();
    obj.display();
  end
endmodule
```

## Encapsulation
Encapsulation is the practice of hiding the internal details of a class and exposing only the necessary methods.

### Example
```SV
class EncapsulatedClass;
  int a;
  function void set_a(int value);
    a = value;
  endfunction
  function int get_a();
    return a;
  endfunction
endclass

module encapsulation_example;
  initial begin
    EncapsulatedClass obj = new();
    obj.set_a(10);
    $display("a: %0d", obj.get_a());
  end
endmodule
```

## Randomization
Classes in SystemVerilog can also be used for randomization.

### Example
```SV
class RandomClass;
  rand int a;
  constraint a_constraint { a > 0 && a < 100; }
endclass

module random_class_example;
  initial begin
    RandomClass obj = new();
    if (obj.randomize())
      $display("Random value: %0d", obj.a);
  end
endmodule
```

## Exercises
1. Define a class with a method to display its properties.
2. Create an object of the class and call its method.
3. Use inheritance to create a derived class and override a method.
4. Implement polymorphism by creating a base class and a derived class with a virtual method.
5. Use encapsulation to hide the internal details of a class.
6. Create a class with random variables and constraints, and generate random values for its properties.

## Conclusion
Classes in SystemVerilog provide powerful tools for creating object-oriented models. Understanding how to define, create, and use classes is essential for writing modular and reusable hardware models and testbenches.
