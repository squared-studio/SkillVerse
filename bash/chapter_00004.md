# Functions

## Defining Functions
Functions allow you to group a set of commands into a single unit, which can be called multiple times within a script.

Example:
```bash
#!/bin/bash
greet() {
  echo "Hello, $1!"
}

greet "World"
greet "Bash"
```

## Function Parameters
You can pass parameters to functions and access them using `$1`, `$2`, etc.

Example:
```bash
#!/bin/bash
add() {
  sum=$(( $1 + $2 ))
  echo "Sum: $sum"
}

add 5 10
```

## Returning Values
Functions can return values using the `return` statement or by echoing the result.

Example:
```bash
#!/bin/bash
multiply() {
  result=$(( $1 * $2 ))
  echo $result
}

result=$(multiply 5 10)
echo "Product: $result"
```

## Exercise
Create a function that takes two numbers as arguments and returns their product. Call the function and print the result.

Example solution:
```bash
#!/bin/bash
# This script defines a function to multiply two numbers and prints the result

# Define the function
multiply() {
  result=$(( $1 * $2 ))
  echo $result
}

# Call the function and print the result
product=$(multiply 5 10)
echo "Product: $product"
```

## Conclusion
In this chapter, we covered functions in Bash scripting, including defining functions, passing parameters, and returning values. In the next chapter, we will explore working with files in Bash.
