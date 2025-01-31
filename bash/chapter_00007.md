# Chapter 7: Error Handling

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

## Conclusion
In this chapter, we covered error handling in Bash scripting, including exit status, the `trap` command, and debugging techniques. In the next chapter, we will explore practical examples of Bash scripts.
