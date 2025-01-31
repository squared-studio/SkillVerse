# Best Practices

## Writing Readable Code
Write code that is easy to read and understand.

### Use Meaningful Variable Names
Choose variable names that describe their purpose.

Example:
```bash
#!/bin/bash
# Bad
a=10
# Good
file_count=10
```

### Use Indentation
Indent your code to show its structure.

Example:
```bash
#!/bin/bash
if [ $file_count -gt 0 ]; then
  echo "Files found"
else
  echo "No files found"
fi
```

## Commenting and Documentation
Add comments to explain your code and create documentation for your scripts.

Example:
```bash
#!/bin/bash
# This script counts the number of files in a directory
dir="/path/to/directory"
file_count=$(ls $dir | wc -l)
echo "Number of files: $file_count"
```

## Script Optimization
Optimize your scripts for better performance.

### Avoid Unnecessary Commands
Remove commands that are not needed.

Example:
```bash
#!/bin/bash
# Bad
for file in $(ls); do
  echo $file
done
# Good
for file in *; do
  echo $file
done
```

### Use Built-in Commands
Use built-in commands instead of external commands whenever possible.

Example:
```bash
#!/bin/bash
# Bad
count=$(cat file.txt | wc -l)
# Good
count=$(wc -l < file.txt)
```

## Exercise
Create a script that counts the number of files in a directory and prints the result. Use meaningful variable names, proper indentation, and add comments to explain your code.

Example solution:
```bash
#!/bin/bash
# This script counts the number of files in a directory

# Define the directory to search
directory="/path/to/directory"

# Count the number of files in the directory
file_count=$(ls $directory | wc -l)

# Print the result
echo "Number of files in $directory: $file_count"
```
