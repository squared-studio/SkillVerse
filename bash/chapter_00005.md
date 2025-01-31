# Chapter 5: Working with Files

## File Test Operators
Bash provides several file test operators to check the properties of files.

Example:
```bash
#!/bin/bash
file="example.txt"

if [ -e $file ]; then
  echo "File exists"
else
  echo "File does not exist"
fi
```

Common file test operators:
- `-e`: Check if file exists
- `-f`: Check if file is a regular file
- `-d`: Check if file is a directory
- `-r`: Check if file is readable
- `-w`: Check if file is writable
- `-x`: Check if file is executable

## Reading and Writing Files
You can read from and write to files using redirection and the `cat` command.

Example:
```bash
#!/bin/bash
# Write to a file
echo "Hello, World!" > example.txt

# Read from a file
cat example.txt
```

## File Permissions
You can change file permissions using the `chmod` command.

Example:
```bash
#!/bin/bash
# Make a file executable
chmod +x example.sh
```

## Directory Management
You can create and manage directories using the `mkdir` and `rmdir` commands.

Example:
```bash
#!/bin/bash
# Create a directory
mkdir my_directory

# Remove a directory
rmdir my_directory
```

## Conclusion
In this chapter, we covered working with files in Bash, including file test operators, reading and writing files, file permissions, and directory management. In the next chapter, we will explore advanced scripting techniques in Bash.
