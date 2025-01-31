# Package

## Introduction
Packages in SystemVerilog are used to group related declarations, such as data types, constants, functions, and tasks. They help in organizing and reusing code across multiple modules and files.

## Defining Packages
Packages are defined using the `package` keyword.

### Example
```SV
package my_package;
  // Declarations
  typedef int my_int;
  function int add(input int a, input int b);
    add = a + b;
  endfunction
endpackage
```

## Importing Packages
Packages can be imported into modules or other packages using the `import` keyword.

### Example
```SV
module package_example;
  import my_package::*;
  initial begin
    my_int a = 10;
    my_int b = 20;
    $display("Sum: %0d", add(a, b));
  end
endmodule
```

## Package Scope
Items declared in a package can be accessed using the package scope resolution operator `::`.

### Example
```SV
module package_scope_example;
  initial begin
    my_package::my_int a = 10;
    my_package::my_int b = 20;
    $display("Sum: %0d", my_package::add(a, b));
  end
endmodule
```

## Exporting Packages
Packages can be exported to make their contents available to other packages or modules.

### Example
```SV
package my_package;
  export my_int, add;
  typedef int my_int;
  function int add(input int a, input int b);
    add = a + b;
  endfunction
endpackage

module export_example;
  import my_package::*;
  initial begin
    my_int a = 10;
    my_int b = 20;
    $display("Sum: %0d", add(a, b));
  end
endmodule
```

## Exercises
1. Define a package with a typedef and a function.
2. Import the package into a module and use the typedef and function.
3. Use the package scope resolution operator to access items in the package.
4. Export items from a package and use them in a module.

