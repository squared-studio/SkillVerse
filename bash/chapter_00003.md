# Chapter 3: Control Structures

## Conditional Statements
Conditional statements allow you to execute different commands based on certain conditions.

### if, else, elif
The `if` statement is used to test a condition. If the condition is true, the commands following the `if` statement are executed. You can use `else` and `elif` to add additional conditions.

Example:
```bash
#!/bin/bash
a=10
b=20

if [ $a -gt $b ]; then
  echo "$a is greater than $b"
elif [ $a -lt $b ]; then
  echo "$a is less than $b"
else
  echo "$a is equal to $b"
fi
```

## Loops
Loops allow you to execute a block of code multiple times.

### for Loop
The `for` loop iterates over a list of items and executes the commands for each item.

Example:
```bash
#!/bin/bash
for i in 1 2 3 4 5; do
  echo "Number: $i"
done
```

### while Loop
The `while` loop executes the commands as long as the condition is true.

Example:
```bash
#!/bin/bash
count=1
while [ $count -le 5 ]; do
  echo "Count: $count"
  count=$((count + 1))
done
```

### until Loop
The `until` loop executes the commands until the condition becomes true.

Example:
```bash
#!/bin/bash
count=1
until [ $count -gt 5 ]; do
  echo "Count: $count"
  count=$((count + 1))
done
```

## Case Statements
The `case` statement allows you to execute commands based on different patterns.

Example:
```bash
#!/bin/bash
fruit="apple"

case $fruit in
  "apple")
    echo "Apple pie"
    ;;
  "banana")
    echo "Banana split"
    ;;
  "cherry")
    echo "Cherry tart"
    ;;
  *)
    echo "Unknown fruit"
    ;;
esac
```

## Conclusion
In this chapter, we covered control structures in Bash, including conditional statements, loops, and case statements. In the next chapter, we will explore functions in Bash scripting.
