# Control Structures

## **Conditional Statements: Make Your Scripts Smart**
Conditionals let your scripts react dynamically to different scenarios - essential for error handling, validation, and decision-based automation.

### **`if`, `else`, `elif`**
**Syntax Deep Dive**:
```bash
if [ condition ]; then  # [ ] requires spaces around brackets
  # Code if true
elif [ condition ]; then
  # Alternative check
else
  # Fallback code
fi
```

**Real-World Example**: Check if a critical file exists before processing:
```bash
#!/bin/bash
config_file="/etc/app/config.conf"

if [ -f "$config_file" ]; then  # -f checks if file exists
  echo "Config found. Starting service..."
  ./start_service.sh
elif [ -d "/etc/app/backups" ]; then  # -d checks for directory
  echo "Config missing! Using backup directory."
  cp "/etc/app/backups/config.conf" "$config_file"
else
  echo "Critical error: No config or backups!" >&2  # Output to stderr
  exit 1
fi
```

**Key Operators**:
- Numeric: `-eq` (equal), `-ne` (not equal), `-gt`/`-lt` (greater/less than)
- File Checks: `-f` (file exists), `-d` (directory), `-s` (file not empty)
- String: `=`, `!=`, `-z` (string is empty)

## **Loops: Automate Repetitive Tasks**

### **`for` Loop: Iterate Over Known Items**
**Use Cases**: Process files, run commands on multiple servers, generate reports.

**Enhanced Example**: Rename all `.txt` files in a directory:
```bash
#!/bin/bash
for file in *.txt; do
  new_name="${file%.txt}.bak"  # Parameter expansion removes .txt
  mv "$file" "$new_name"
  echo "Renamed: $file → $new_name"
done
```

**Brace Expansion Trick**:
```bash
for i in {1..5}; do  # No need for spaces: {START..END..INCREMENT}
  echo "Processing item $i"
done
```

### **`while` Loop: Run Until Condition Fails**
**Use Cases**: Read files line-by-line, monitor system resources.

**Real-World Example**: Monitor memory usage until it exceeds 90%:
```bash
#!/bin/bash
threshold=90

while true; do
  usage=$(free | awk '/Mem/{printf "%.0f", $3/$2*100}')
  echo "Memory usage: $usage%"

  if [ $usage -ge $threshold ]; then
    echo "ALERT! Memory over $threshold%!" >&2
    exit 1
  fi

  sleep 5  # Check every 5 seconds
done
```

### **`until` Loop: Inverse of `while`**
**Use Cases**: Wait for a service to start, retry failed operations.

**Server Ready Check**:
```bash
#!/bin/bash
until curl -s http://localhost:8080/healthcheck; do
  echo "Waiting for server..."
  sleep 10
done
echo "Server is up!"
```

## **`case` Statements: Simplify Complex Conditionals**
**Ideal For**: Handling command-line flags, menu systems, or multiple matched patterns.

**Advanced Example**: Process user input for a CLI tool:
```bash
#!/bin/bash
read -p "Enter action (start/stop/restart): " user_input

case "$user_input" in
  start|s)  # Matches "start" or "s"
    systemctl start myservice
    ;;
  stop|halt)
    systemctl stop myservice
    ;;
  restart|reload)
    systemctl restart myservice
    ;;
  *)  # Default case
    echo "Invalid action: $user_input" >&2
    exit 1
    ;;
esac
```

**Pattern Matching Features**:
- `|` for multiple matches
- Wildcards: `*.log` matches "error.log", "debug.log"
- Ranges: `[a-z]`, `[0-9]`

## **Exercise: Automate a Number Generator**
**Task**: Write a script that:
1. Prints numbers from 1 to 10 using a `for` loop
2. **Bonus**: Only print even numbers
3. **Expert Challenge**: Sum all numbers and print the total

**Example Solution**:
```bash
#!/bin/bash
total=0

for num in {1..10}; do
  echo "Number: $num"
  total=$((total + num))  # Arithmetic expansion
done

echo "Total sum: $total"
```

**Even Numbers Solution**:
```bash
for num in {2..10..2}; do  # Step by 2
  echo "Even: $num"
done
```

## **Pro Tips**
1. **Avoid Infinite Loops**: Always include an exit condition in `while true` loops.
2. **Quote Variables**: Prevent word splitting with `"$var"`.
3. **Use `(( ))` for Math**: More readable than `$(( ))` in conditionals:
   ```bash
   if (( count > 10 )); then ...
   ```

**Gotchas**:
- Forgot `;;` in `case`? Your script will execute multiple blocks!
- Missing spaces in `[ $a -eq $b ]` causes syntax errors.
