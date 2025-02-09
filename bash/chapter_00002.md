# Bash Essentials

## **Your First Script: Beyond Hello World**
Let's dissect the classic "Hello World" to understand Bash scripting fundamentals.

### **Step-by-Step Breakdown**
1. **Create `hello_world.sh`**:
   ```bash
   #!/bin/bash  # Shebang: Specifies Bash as the interpreter
   echo "Hello, World!"  # echo outputs text to the terminal
   ```

2. **Make Executable**:
   ```bash
   chmod +x hello_world.sh  # Adds execute permission
   ```

3. **Run the Script**:
   ```bash
   ./hello_world.sh  # Executes in current directory
   ```

**Pro Tip**: Use `bash hello_world.sh` to run without execute permissions.

**Troubleshooting**:
- `Permission denied?` → Run `chmod +x` again.
- `Command not found?` → Check file path or shebang line.

## **Core Shell Commands: Navigate Like a Pro**
Master these essential commands for file and directory management:

| Command | Description       | Common Flags                              |
|---------|-------------------|-------------------------------------------|
| `ls`    | List files        | `-l` (details), `-a` (show hidden)        |
| `cd`    | Change dir        | `cd ~` (home), `cd -` (previous dir)      |
| `pwd`   | Show current path |                                           |
| `cp`    | Copy files        | `-r` (recursive for directories)          |
| `mv`    | Move/rename       | `-i` (confirm overwrite)                  |
| `rm`    | Delete files      | `-rf` (Caution: Force delete dirs)        |
| `mkdir` | Create dirs       | `-p` (create parent dirs if missing)      |

**Example Workflow**:
```bash
mkdir -p ~/projects/scripts  # Create nested directories
cd ~/projects/scripts && ls  # Navigate and list
```

## **Variables: Store Data Like a Pro**
Bash variables store text, numbers, or complex data.

### **Key Concepts**:
- **No Data Types**: All variables are strings by default.
- **Declaration**: `var_name="value"` (No spaces around `=`)
- **Access**: `$var_name` or `${var_name}`

**Best Practices**:
```bash
#!/bin/bash
user="Alice"  # Lowercase for local variables
readonly PI=3.14  # Uppercase for constants
file_list=$(ls *.txt)  # Store command output

echo "User: $user, PI: $PI"
echo "Text files: $file_list"
```

### **Arrays: Manage Collections**
```bash
fruits=("Apple" "Banana" "Cherry")
echo "First fruit: ${fruits[0]}"  # Index starts at 0
echo "All fruits: ${fruits[@]}"  # Access all elements
```

**Pro Tip**: Use `declare -a` for explicit array declaration.

## **Operators: Math, Logic, and Comparisons**

### **Arithmetic Operations**
Use `$(( ))` or `let` for calculations:
```bash
sum=$((5 + 3 * 2))  # Outputs 11
((count++))  # Increment variable
```

### **Comparison Operators**

| Numeric | String | Purpose      |
|---------|--------|--------------|
| `-eq`   | `==`   | Equal        |
| `-ne`   | `!=`   | Not equal    |
| `-lt`   | `<`    | Less than    |
| `-gt`   | `>`    | Greater than |

**Example**:
```bash
if [ "$1" == "admin" ] && [ $# -eq 1 ]; then
  echo "Welcome, administrator!"
fi
```

### **Logical Operators**
Chain conditions with `&&` (AND), `||` (OR):
```bash
[ -f "file.txt" ] || touch file.txt  # Create file if missing
```

## **Exercise: Build a Dynamic Greeting System**

**Task**: Create a script that:
1. Takes a username as a command-line argument
2. Greets the user with the current time
3. **Bonus**: Add error handling for missing arguments

**Example Solution**:
```bash
#!/bin/bash
# Ensure an argument is provided
if [ $# -eq 0 ]; then
  echo "Error: Please provide a name" >&2
  exit 1
fi

current_time=$(date +"%H:%M")
echo "Hello, $1! Current time is $current_time"
```

**Run It**:
```bash
./greet.sh Alice  # Output: Hello, Alice! Current time is 14:30
```

## **Pro Tips for Bash Newbies**
1. **Quote Variables**: Prevent errors with spaces → `"$var"`
2. **Use `[[ ]]` for Advanced Checks**: Supports regex and safer expansions
   ```bash
   if [[ "$file" == *.log ]]; then ...
   ```
3. **Debug Mode**: Run `bash -x script.sh` to trace execution.

**Gotcha Alert**:
- `var=5+2` assigns the string "5+2" → Use `$(( ))` for math.
- Unquoted variables with spaces → `rm $file` becomes `rm file1 file2`!
