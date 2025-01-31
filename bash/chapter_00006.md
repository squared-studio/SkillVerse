# Chapter 6: Advanced Scripting

## Regular Expressions
Regular expressions are patterns used to match character combinations in strings. They are commonly used with tools like `grep`, `sed`, and `awk`.

Example:
```bash
#!/bin/bash
echo "Hello 123" | grep -E '[0-9]+'
```

## Sed and Awk
`sed` and `awk` are powerful text processing tools.

### Sed
`sed` is a stream editor used to perform basic text transformations.

Example:
```bash
#!/bin/bash
echo "Hello World" | sed 's/World/Bash/'
```

### Awk
`awk` is a programming language for pattern scanning and processing.

Example:
```bash
#!/bin/bash
echo "1 2 3" | awk '{print $1 + $2 + $3}'
```

## Process Substitution
Process substitution allows you to use the output of a command as a file.

Example:
```bash
#!/bin/bash
diff <(ls dir1) <(ls dir2)
```

## Command Substitution
Command substitution allows you to capture the output of a command and use it as a variable.

Example:
```bash
#!/bin/bash
date=$(date)
echo "Current date and time: $date"
```

## Conclusion
In this chapter, we covered advanced scripting techniques in Bash, including regular expressions, `sed` and `awk`, process substitution, and command substitution. In the next chapter, we will explore error handling in Bash scripting.
