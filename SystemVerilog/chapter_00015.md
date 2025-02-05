# Package

## Introduction
Packages provide a **namespace** to group related declarations (data types, constants, functions, tasks, classes) for reuse across multiple design and verification components. Key benefits include:
- Avoiding global namespace pollution
- Reducing code duplication
- Enabling modular code organization
- Facilitating team collaboration through standardized interfaces

## Defining Packages
Declared with `package` keyword. Can contain:
- `typedef` definitions
- `function`/`task` declarations
- `class` definitions
- `parameter`/`const` constants
- `import` statements from other packages

### Example: Basic Package Structure
```SV
package math_utils;
  // Type definition
  typedef logic [31:0] word_t;

  // Constant
  const real PI = 3.1415926535;

  // Function declaration
  function automatic word_t add(input word_t a, b);
    return a + b;
  endfunction

  // Task declaration
  task print_result(input string label, word_t value);
    $display("%s: 0x%h", label, value);
  endtask
endpackage
```

## Importing Packages
Import mechanisms control namespace visibility:

| Import Style          | Description                          |
|-----------------------|--------------------------------------|
| `import pkg::*;`      | Wildcard import (all visible items)  |
| `import pkg::item;`   | Specific item import                 |
| `import pkg::*;`      | Import all items (use with caution)  |

### Example: Selective Import
```SV
module calculator;
  import math_utils::word_t;      // Import specific type
  import math_utils::add;         // Import specific function

  initial begin
    word_t x = 32'hA5, y = 32'h5A;
    $display("Sum: 0x%h", add(x, y));  // 0xFF
  end
endmodule
```

## Package Scope Resolution
Access package members without imports using `::` operator:

### Example: Explicit Scope Access
```SV
module physics_engine;
  initial begin
    math_utils::word_t mass = 32'd100;
    real circumference = 2 * math_utils::PI * 5.0;

    math_utils::print_result("Mass", mass);
  end
endmodule
```

## Package Export System
Re-export imported items using `export` to create abstraction layers:

### Example: Hierarchical Package Organization
```SV
// Base package
package base_pkg;
  typedef logic [7:0] byte_t;
  function byte_t invert(input byte_t b);
    return ~b;
  endfunction
endpackage

// Extended package
package extended_pkg;
  import base_pkg::*;     // Import all from base
  export base_pkg::*;     // Re-export base items

  // Add new functionality
  function byte_t mask(input byte_t b, input byte_t m);
    return b & m;
  endfunction
endpackage

// Top module using exported items
module chip;
  import extended_pkg::*;  // Gets base_pkg + extended_pkg

  initial begin
    byte_t data = 8'b1010_1100;
    $display("Inverted: 0x%h", invert(data));  // From base_pkg
    $display("Masked: 0x%h", mask(data, 8'h0F)); // From extended_pkg
  end
endmodule
```

## Best Practices
1. **Avoid Wildcard Imports**
   Prefer explicit imports to prevent naming conflicts
   ```SV
   // Instead of:
   import math_utils::*;

   // Use:
   import math_utils::word_t, math_utils::add;
   ```

2. **Use Unique Package Names**
   Prefix packages with project/organization name
   ```SV
   package acme_math_pkg;  // Good
   package math;           // Risky - common name
   ```

3. **Organize by Functionality**
   Create separate packages for:
   - Data types (`typedefs_pkg`)
   - Verification components (`tb_utils_pkg`)
   - Protocol-specific items (`usb_pkg`)

4. **Combine with `include**
   Split large packages into multiple files
   ```SV
   // File: usb_types.svh
   package usb_pkg;
     `include "usb_types.svh"
     `include "usb_functions.svh"
     `include "usb_classes.svh"
   endpackage
   ```

## Exercises
1. **Basic Package**: Create `geometry_pkg` with:
   - `point_t` struct (x,y coordinates)
   - `distance()` function
   - `AREA_CONST` constant

2. **Import Practice**: Build module that:
   - Uses wildcard import for `geometry_pkg`
   - Creates two `point_t` variables
   - Calculates distance between them

3. **Explicit Scope**: Rewrite previous module using `::` operator without imports

4. **Package Export**: Create:
   - `base_pkg` with `color_t` enum (RED, GREEN, BLUE)
   - `graphics_pkg` that imports/reexports `base_pkg` and adds `mix_colors()`
   - Top module using both through `graphics_pkg`

5. **Conflict Resolution**: Create two packages with same-named `print()` function.
   Demonstrate how to resolve name conflicts using:
   - Explicit scope resolution
   - Renaming imports

**Key Improvements**:
- Added practical hierarchical package example
- Clarified valid `export` usage with real-world scenario
- Included best practices section
- Expanded exercises with conflict resolution
- Fixed package export misconceptions from original example
- Added code organization recommendations
