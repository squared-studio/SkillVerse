# Task 1 : Linux Terminal

## Introduction

The **Linux terminal**, also known as the command line interface (CLI), is a powerful tool that allows users to interact directly with the system's shell. Unlike the graphical user interface (GUI) which uses visual elements like windows, icons, and menus, the terminal relies on text-based commands.

The terminal is important for several reasons:

1. **Efficiency**: Tasks that require multiple clicks in a GUI can often be done in one or two commands in the terminal. This can greatly speed up your workflow.

2. **Control**: The terminal gives you more control over your system. You can see exactly what's happening behind the scenes and make precise changes.

3. **Scripting**: With the terminal, you can write scripts to automate repetitive tasks. This can save a lot of time and effort.

4. **Troubleshooting**: The terminal allows you to dig deep into your system to troubleshoot and fix issues. Error messages are often more detailed in the terminal.

5. **Remote Access**: You can access and manage your system remotely via the terminal using SSH (Secure Shell), which is crucial for server administration.

Overall, while the terminal has a steeper learning curve compared to the GUI, its power and versatility make it an essential tool for anyone using Linux. Whether you're a system administrator, a developer, or an enthusiast, understanding how to use the terminal will greatly enhance your Linux experience.

## Commonly used commands

**`pwd`**: Print Working Directory. This command will display the directory in which you are currently located.

```bash
$ pwd
/home/user
```

**`ls`**: List. This command will list all files and directories in your current directory.

Options:
- `-l`: Use a long listing format.
- `-a`: Include hidden files.

```bash
$ ls
Desktop  Documents  Downloads  Music  Pictures  Public  Templates  Videos

$ ls -l
total 0
drwxr-xr-x  2 user user  4096 Jan  1 00:00 Desktop
drwxr-xr-x  2 user user  4096 Jan  1 00:00 Documents

$ ls -a
.  ..  .hidden  Desktop  Documents
```

**`cd`**: Change Directory. This command will change your current directory to the one specified.

Options:
- `..`: Move up one directory level.
- `-`: Move to the previous directory.

```bash
$ cd Documents
$ cd ..
$ cd -
```

**`cat`**: Concatenate. This command will display the contents of a file.

Options:
- `-n`: Number all output lines.

```bash
$ cat file.txt
$ cat -n file.txt
```

**`cp`**: Copy. This command will copy files or directories.

Options:
- `-r`: Copy directories recursively.
- `-i`: Prompt before overwrite.

```bash
$ cp source.txt destination.txt
$ cp -r source_dir destination_dir
$ cp -i source.txt destination.txt
```

**`mv`**: Move. This command will move files or directories.

Options:
- `-i`: Prompt before overwrite.
- `-u`: Move only when the source file is newer than the destination file or when the destination file is missing.

```bash
$ mv old.txt new.txt
$ mv -i old.txt new.txt
$ mv -u old.txt new.txt
```

**`rm`**: Remove. This command will delete files or directories.

Options:
- `-r`: Remove directories and their contents recursively.
- `-i`: Prompt before every removal.

```bash
$ rm file.txt
$ rm -r directory
$ rm -i file.txt
```

**`man`**: Manual. This command will display the manual of the command specified.

```bash
$ man ls
```

**`sudo`**: SuperUser DO. This command will execute a command with superuser privileges.

Options:
- `-s`: Run the shell specified by the SHELL environment variable if set or the shell specified by the invoking user's password database entry.

```bash
$ sudo apt-get update
$ sudo -s
```

**`exit`**: Exit. This command will close the terminal.

```bash
$ exit
```

**`mkdir`**: Make Directory. This command is used to create a new directory.

Options:
- `-p`: Create parent directories as needed.

```bash
$ mkdir new_directory
$ mkdir -p parent_directory/new_directory
```

**`rmdir`**: Remove Directory. This command is used to remove an empty directory.

Options:
- `-p`: Remove DIRECTORY and its ancestors.

```bash
$ rmdir directory
$ rmdir -p parent_directory/new_directory
```

**`find`**: This command is used to search and locate the list of files and directories based on conditions you specify for files that match the arguments.

Options:
- `-name`: Search for files by name.
- `-type`: Search for a specific type (e.g., `f` for files, `d` for directories).

```bash
$ find /home -name file.txt
$ find /home -type d -name "dir_name"
```

**`grep`**: This command is used to search text using patterns.

Options:
- `-i`: Ignore case distinctions.
- `-r`: Read all files under each directory, recursively.

```bash
$ grep "pattern" /path/to/file
$ grep -i "pattern" /path/to/file
$ grep -r "pattern" /path/to/directory
```

**`history`**: This command will show you all the commands you have used previously.

Options:
- `-c`: Clear the history list.

```bash
$ history
$ history -c
```

**`clear`**: This command is used to clear your terminal if it gets filled up with too many commands.

```bash
$ clear
```