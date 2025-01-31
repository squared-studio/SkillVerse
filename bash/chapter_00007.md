# Error Handling

## Exit Status
Every command in Bash returns an exit status, which indicates whether the command was successful or not. An exit status of `0` means success, while any non-zero value indicates an error.

Example:
```bash
#!/bin/bash
ls /nonexistent_directory
echo "Exit status: $?"
```

## Trap Command
The `trap` command allows you to catch signals and execute commands when a signal is received.

Example:
```bash
#!/bin/bash
trap 'echo "Script interrupted"; exit' INT
while true; do
  echo "Running..."
  sleep 1
done
```

## Debugging Techniques
You can use various techniques to debug your Bash scripts.

### Using `set` Command
The `set` command can be used to enable debugging options.

Example:
```bash
#!/bin/bash
set -x
echo "Debugging enabled"
set +x
echo "Debugging disabled"
```

### Using `trap` Command
You can use the `trap` command to print the current line number and command being executed.

Example:
```bash
#!/bin/bash
trap 'echo "Line $LINENO: $BASH_COMMAND"' DEBUG
echo "This is a test"
```

## Exercise
Create a script that attempts to create a directory and handles any errors that occur. Use the `trap` command to catch errors and print a message.

Example solution:
```bash
#!/bin/bash
# This script attempts to create a directory and handles errors

# Define the directory name
directory="new_directory"

# Trap errors and print a message
trap 'echo "Error: Failed to create directory"; exit 1' ERR

# Attempt to create the directory
mkdir $directory

# Print success message
echo "Directory $directory created successfully"
```
