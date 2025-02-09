# Introduction
Welcome to the **Bash Scripting Mastery Course**! Whether you're a developer, system administrator, or tech enthusiast, this course will empower you to automate repetitive tasks, streamline workflows, and harness the full potential of the command line. By the end of this journey, you'll be able to:
- Write scripts to manage files, users, and system operations.
- Automate backups, log analysis, and deployments.
- Solve real-world problems with efficient, maintainable code.


## Why Learn Bash?
**Bash (Bourne Again SHell)** is the cornerstone of Unix-based systems and a critical tool for:
- **Automation**: Turn complex workflows into one-click solutions.
- **DevOps & SysOps**: Master scripting for server management, CI/CD pipelines, and infrastructure as code (IaC).
- **Cross-Platform Flexibility**: Run scripts seamlessly on Linux, macOS, and Windows (via WSL/Git Bash).

Fun fact: Over 80% of cloud infrastructure relies on Linux, where Bash is the default shell.


## Setting Up Your Environment

### **Linux**
Most distributions (Ubuntu, Fedora, etc.) include Bash by default.
1. Open the terminal (`Ctrl+Alt+T`).
2. Verify your Bash version:
   ```bash
   bash --version
   ```


### **macOS**
While macOS includes Bash, **the default shell is now zsh (since Catalina)**.
1. Switch to Bash temporarily:
   ```bash
   bash
   ```
2. *(Optional)* Install the latest Bash version via Homebrew:
   ```bash
   brew install bash
   ```
   Update your shell permanently by adding `/usr/local/bin/bash` to `/etc/shells` and running:
   ```bash
   chsh -s /usr/local/bin/bash
   ```


### **Windows**
Choose one of these robust environments:

#### **Option 1: Windows Subsystem for Linux (WSL)**
**Best for**: Full Linux experience.
**Prerequisites**: Windows 10 (Build 2004+) or Windows 11.

1. Run PowerShell as Admin and execute:
   ```powershell
   wsl --install
   ```
2. Reboot your machine.
3. Install a Linux distribution (e.g., Ubuntu) from the Microsoft Store.

#### **Option 2: Git Bash**
**Best for**: Lightweight scripting without a full Linux setup.
1. Download [Git Bash](https://git-scm.com/downloads).
2. Install using default settings.


### **Choosing a Text Editor**
Enhance your workflow with these tools:
- **Visual Studio Code** (Recommended): Install the [Bash IDE extension](https://marketplace.visualstudio.com/items?itemName=mads-hartmann.bash-ide-vscode) for syntax highlighting and debugging.
- **Vim/Nano**: Lightweight terminal-based editors.
- **Sublime Text/Atom**: Feature-rich GUI editors.

**Pro Tip**: Configure your editor to use **Unix (LF)** line endings to prevent `^M` errors.


## Your First Script: Hello World!
Let’s create a script to validate your setup.

### Step-by-Step Guide
1. Create a file named `hello_world.sh`:
   ```bash
   #!/bin/bash  # Shebang line: Tells the system to use Bash.
   echo "Hello, World!"  # Print text to the terminal.
   ```
2. Save the file and make it executable:
   ```bash
   chmod +x hello_world.sh  # Grants execute permission.
   ```
3. Run the script:
   ```bash
   ./hello_world.sh
   ```

**Expected Output**:
```
Hello, World!
```

### Troubleshooting
- **Permission Denied?** Ensure you ran `chmod +x`.
- **Command Not Found?** Use `bash hello_world.sh` to run without execute permissions.


**Pro Challenge**: Modify `hello_world.sh` to greet you by name. (Hint: Use a variable like `$USER`!)

