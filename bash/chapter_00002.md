# Basics of Bash

## Hello World Script
Let's start with a simple "Hello World" script. This will help you understand the basic structure of a Bash script.

1. Open your text editor and create a new file named `hello_world.sh`.
2. Add the following code to the file:
   ```bash
   #!/bin/bash
   echo "Hello, World!"
   ```
3. Save the file and close the text editor.
4. Open a terminal and navigate to the directory where you saved the file.
5. Make the script executable by running:
   ```bash
   chmod +x hello_world.sh
   ```
6. Execute the script by running:
   ```bash
   ./hello_world.sh
   ```

You should see the output: `Hello, World!`

## Basic Shell Commands
Bash provides a wide range of built-in commands. Here are some of the most commonly used commands:

- `ls`: List directory contents
- `cd`: Change the current directory
- `pwd`: Print the current working directory
- `cp`: Copy files and directories
- `mv`: Move or rename files and directories
- `rm`: Remove files or directories
- `mkdir`: Create directories
- `rmdir`: Remove empty directories

## Variables and Data Types
Variables in Bash are used to store data that can be used later in the script. Here are some examples:

```bash
#!/bin/bash
# Define a variable
greeting="Hello, World!"
# Print the variable
echo $greeting
```

Bash supports several data types, including strings, integers, and arrays.

### Strings
Strings are sequences of characters. You can define a string variable like this:
```bash
name="John Doe"
echo "My name is $name"
```

### Integers
Integers are whole numbers. You can perform arithmetic operations using integers:
```bash
num1=5
num2=10
sum=$((num1 + num2))
echo "The sum is $sum"
```

### Arrays
Arrays are used to store multiple values in a single variable:
```bash
fruits=("Apple" "Banana" "Cherry")
echo "First fruit: ${fruits[0]}"
```

## Basic Operators
Bash supports various operators for performing arithmetic, comparison, and logical operations.

### Arithmetic Operators
- `+`: Addition
- `-`: Subtraction
- `*`: Multiplication
- `/`: Division
- `%`: Modulus

Example:
```bash
a=10
b=5
echo "Addition: $((a + b))"
echo "Subtraction: $((a - b))"
```

### Comparison Operators
- `-eq`: Equal to
- `-ne`: Not equal to
- `-lt`: Less than
- `-le`: Less than or equal to
- `-gt`: Greater than
- `-ge`: Greater than or equal to

Example:
```bash
a=10
b=5
if [ $a -gt $b ]; then
  echo "$a is greater than $b"
fi
```

### Logical Operators
- `&&`: Logical AND
- `||`: Logical OR
- `!`: Logical NOT

Example:
```bash
a=10
b=5
if [ $a -gt $b ] && [ $a -lt 20 ]; then
  echo "$a is between $b and 20"
fi
```

## Exercise
Create a script that defines a variable with your name and prints a greeting message.

Example solution:
```bash
#!/bin/bash
# This script defines a variable with your name and prints a greeting message

# Define the variable
name="John Doe"

# Print the greeting message
echo "Hello, $name!"
```

## Conclusion
In this chapter, we covered the basics of Bash scripting, including writing a simple script, using basic shell commands, working with variables and data types, and using basic operators. In the next chapter, we will explore control structures in Bash, such as conditional statements and loops.
