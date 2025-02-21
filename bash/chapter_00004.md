# Functions in Bash

## Defining Functions
Functions in Bash allow you to encapsulate reusable code blocks. They must be defined before they are called and use positional parameters similar to scripts.

**Key Points:**
- Function syntax: `function_name() { ... }`
- Parameters are passed during invocation and accessed with `$1`, `$2`, etc.
- Functions can be called multiple times with different arguments.

Example:
```bash
#!/bin/bash
# Define a function
greet() {
  echo "Hello, ${1}!"
}

# Call the function with arguments
greet "World"   # Output: Hello, World!
greet "Bash"    # Output: Hello, Bash!
```

## Function Parameters
Parameters passed to functions are separate from script parameters. Use `local` variables to avoid unintended side effects in global scope.

**Best Practices:**
- Use `local` keyword for function-specific variables.
- Validate parameters with `$#` (e.g., `if [ $# -ne 2 ]; then ...`).

Example:
```bash
#!/bin/bash
add() {
  local sum=$(( $1 + $2 ))  # 'local' restricts scope to the function
  echo "Sum: $sum"
}

add 5 10  # Output: Sum: 15
```

## Returning Values
Bash functions return values in two ways:
1. **Exit Status**: Use `return` for numeric status codes (0-255). `0` indicates success.
2. **Output Capture**: Use `echo` to return data and capture it with command substitution `$(...)`.

### Example 1: Returning Data
```bash
#!/bin/bash
multiply() {
  local result=$(( $1 * $2 ))
  echo "$result"  # Output the result to be captured
}

product=$(multiply 5 10)
echo "Product: $product"  # Output: Product: 50
```

### Example 2: Exit Status
```bash
#!/bin/bash
is_even() {
  if (( $1 % 2 == 0 )); then
    return 0  # Success (even)
  else
    return 1  # Failure (odd)
  fi
}

is_even 4 && echo "Even" || echo "Odd"  # Output: Even
```

## Exercise
Create a function `calculate_product` that takes two numbers as arguments and returns their product. Include error handling for non-numeric inputs.

**Enhanced Solution:**
```bash
#!/bin/bash
calculate_product() {
  # Check if both arguments are numbers
  if ! [[ $1 =~ ^-?[0-9]+$ ]] || ! [[ $2 =~ ^-?[0-9]+$ ]]; then
    echo "Error: Both arguments must be numbers." >&2
    return 1
  fi

  local product=$(( $1 * $2 ))
  echo "$product"
}

# Usage
read -p "Enter first number: " num1
read -p "Enter second number: " num2

result=$(calculate_product "$num1" "$num2") || exit 1  # Exit on error
echo "Product: $result"
```

**Explanation:**
- Uses regex to validate numeric inputs.
- Returns an error message to STDERR and exits with status `1` on invalid input.
- Uses `local` for the result variable to ensure encapsulation.

