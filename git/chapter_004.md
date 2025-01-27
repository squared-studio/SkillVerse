# Basics

## `git init`
The `git init` command is used to create a new Git repository. When you run this command in a directory, it sets up all the necessary files and subdirectories required to start versioning the project's files. Essentially, it's the command you use to initialize a new project with Git.

Here's a simple breakdown of what happens when you run `git init`:

1. **Create a New Repository:** It creates a hidden `.git` directory inside your project folder, where all the magic happens.
2. **Set Up Version Control:** The `.git` directory contains all the metadata and object files that Git uses to manage and keep track of the project's history.
3. **Stage for Changes:** Your working directory is now ready to start tracking changes. You can start adding files and committing them to version control.

### Example
```bash
$ cd your_project_directory
$ git init
```
After running these commands, your project directory becomes a Git repository, ready for you to start tracking changes, making commits, and much more.



## `git clone`
The `git clone` command is used to create a copy of an existing Git repository. This command is helpful when you want to take an existing project (hosted on a remote server like GitHub) and create a local copy on your machine. It not only creates a working copy of the project, but it also downloads the entire history of changes.

### Example
```bash
$ git clone <repository-url>
```
Replace `<repository-url>` with the URL of the repository you want to clone. For example, if the repository is hosted on GitHub, the URL would look something like this:
```bash
$ git clone https://github.com/username/repository-name.git
```

### What `git clone` Does:
1. **Download Repository Data:** Fetches all the files and their history from the remote repository.
2. **Create a Local Copy:** Sets up a new directory named after the repository, containing a working copy of all the files.
3. **Track Remotes:** Configures the local repository to track the remote repository so you can easily pull updates and push changes.

It's a handy command to quickly get a full-fledged copy of a project and start working on it immediately.



## `git status`
The `git status` command is super useful for checking the current state of your working directory and staging area in a Git repository. It provides information about the changes that have been made, what files are being tracked, and what files are staged for the next commit.

### Example
```bash
$ git status
```

### What `git status` Does:
- **Shows Tracked and Untracked Files:** Lists files that are staged for commit, modified but not staged, and untracked files.
- **Indicates Staged Changes:** Displays which files have changes that are ready to be committed.
- **Alerts to Unmerged Paths:** If there are conflicts during a merge, it will highlight the files with issues.
- **Reminds of New Branch:** It shows which branch you're currently on and if your branch is ahead or behind the remote branch.

It's like getting a real-time status update on your project, helping you stay organized and aware of your progress.



## `git add`
The `git add` command is used to add changes in the working directory to the staging area. In other words, it tells Git that you want to include updates to a particular file(s) or all files in the next commit. The `git add` command doesn't actually affect the remote repository until you run `git commit` followed by `git push`.

### Example
To add a specific file:
```bash
$ git add filename
```

To add all changed files:
```bash
$ git add .
```

### What `git add` Does:
- **Stages Changes:** Prepares changes to be committed. You can choose specific files or use a wildcard to add all changes.
- **Incremental Commits:** Allows you to break your work into smaller, manageable pieces by staging parts of a project at a time.

This command is key to controlling what gets included in your commits and ensuring you're versioning exactly what you intend to.



## `git commit`
The `git commit` command is used to save your changes to the local repository. Once changes are staged using `git add`, you commit them with `git commit` to create a snapshot of your project at a certain point in time. This snapshot can be referenced or reverted to in the future.

### Example
To commit staged changes with a commit message:
```bash
$ git commit -m "Your commit message"
```

### What `git commit` Does:
- **Records Changes:** It captures the changes in the staging area and saves them in the local repository.
- **Commit Message:** The `-m` flag allows you to add a commit message describing what changes were made. This is very helpful for tracking the history of your project and understanding what each commit represents.

### Example Commit Message
```bash
$ git commit -m "Add feature for user authentication"
```

After running this command, your changes are now committed to your local repository. 

Remember, to push these commits to a remote repository, you'd use the `git push` command.



## `git push`
The `git push` command is used to upload your local repository content to a remote repository. After you've made commits in your local repository, the `git push` command allows you to send those commits to a remote repository (like GitHub, GitLab, or Bitbucket) so others can access and collaborate on the project.

### Example
```bash
$ git push origin main
```

In this example:
- `origin` is the default name for the remote repository.
- `main` is the branch name you're pushing to. (Note: It can also be `master` or any other branch name you're working with.)

### What `git push` Does:
- **Sync Changes:** Uploads your local commits to the remote repository.
- **Collaborate:** Allows team members to see and pull your changes.
- **Track Progress:** Ensures your remote repository reflects your local repository's state.

Using `git push` keeps your work backed up and shareable with others working on the same project.



## `git fetch`
The `git fetch` command is used to download commits, files, and references from a remote repository into your local repository. Unlike `git pull`, it doesn't automatically merge the changes into your working branch. Instead, it allows you to review the updates before integrating them, giving you more control over the merge process.

### Example
```bash
$ git fetch origin
```

In this example:
- `origin` is the default name for the remote repository.

### What `git fetch` Does:
- **Download Updates:** Retrieves updates from the remote repository without altering your working directory.
- **Inspect Changes:** Allows you to review the fetched changes before merging them into your branch.
- **Work Independently:** Keeps your local branch clean until you're ready to merge the fetched changes.

### Example Workflow
1. **Fetch Changes:**
    ```bash
    $ git fetch origin
    ```

2. **Review Changes:**
    ```bash
    $ git log origin/main
    ```

3. **Merge Changes:**
    ```bash
    $ git merge origin/main
    ```

Using `git fetch` gives you the flexibility to see what changes have been made in the remote repository before deciding to merge them into your local branch, making it a valuable tool for managing updates and collaborations effectively.



## `git pull`
The `git pull` command is used to fetch and download content from a remote repository and immediately update the local repository to match that content. It's a combination of two commands: `git fetch` (which downloads the new data) and `git merge` (which integrates it into your local branch).

### Example
```bash
$ git pull origin main
```

In this example:
- `origin` is the default name for the remote repository.
- `main` is the branch you want to update with the latest changes.

### What `git pull` Does:
- **Fetch and Merge:** Retrieves updates from the remote branch and merges them into the local branch.
- **Stay Updated:** Ensures your local repository reflects the latest version of the project, including changes made by other collaborators.
- **Resolve Conflicts:** If there are conflicting changes, you'll be prompted to resolve them during the merge process.

Using `git pull` helps you keep your local work in sync with the remote repository, making sure you're always working with the most current version of the project.



## `git checkout`
The `git checkout` command is a versatile tool in Git that can be used for various purposes, such as switching between branches or restoring files. It essentially changes the state of your working directory to match the specified branch or commit.

### Example
To switch to an existing branch:
```bash
$ git checkout branch-name
```

To create a new branch and switch to it:
```bash
$ git checkout -b new-branch-name
```

To restore a specific file to a previous state:
```bash
$ git checkout commit-hash -- filename
```

### What `git checkout` Does:
- **Switch Branches:** Updates your working directory to reflect the content of the branch you're switching to.
- **Create Branches:** With the `-b` flag, you can create a new branch and switch to it in one command.
- **Restore Files:** Allows you to revert a file to its state in a particular commit, useful for undoing changes to specific files.

### Example Workflow
```bash
# List all branches
$ git branch

# Switch to an existing branch
$ git checkout feature-xyz

# Create and switch to a new branch
$ git checkout -b new-feature-branch

# Restore a file to a previous state
$ git checkout HEAD~1 -- filename.txt
```

The `git checkout` command is incredibly powerful and can be used in different scenarios to manage your code effectively.



## `git log`
The `git log` command is used to display the commit history of a Git repository. It shows a list of all the commits made to the repository, along with details like commit hashes, author names, dates, and commit messages. This command is incredibly helpful for tracking changes and understanding the project's evolution.

### Example
To display the commit history:
```bash
$ git log
```

### What `git log` Shows:
- **Commit Hash:** A unique identifier for each commit.
- **Author Information:** Name and email of the person who made the commit.
- **Date and Time:** When the commit was made.
- **Commit Message:** A description of the changes made in the commit.

### Example Output
```plaintext
commit e42a1d15374c732b8a491c5b3a48a8de9125d85b
Author: Jane Doe <jane.doe@example.com>
Date:   Mon Jan 27 12:00:00 2025 +0900

    Add user authentication feature

commit d4e8c9f538d5a9e745f7a3bb8234d83de43b2f97
Author: John Smith <john.smith@example.com>
Date:   Sun Jan 26 10:00:00 2025 +0900

    Fix bug in payment gateway
```

### Additional Options
- To see a simplified, one-line summary of each commit:
    ```bash
    $ git log --oneline
    ```
- To see the history of a specific file:
    ```bash
    $ git log filename
    ```
- To include the difference introduced in each commit:
    ```bash
    $ git log -p
    ```

Using `git log` allows you to dive into the history of your project and understand the changes made over time.



## `git diff`
The `git diff` command is used to show the differences between various Git data sources. It allows you to see changes between commits, the working directory, and the staging area. This command is incredibly useful for reviewing what has changed before making a commit or seeing what was changed in a specific commit.

### Example
To see the changes in the working directory that are not yet staged for commit:
```bash
$ git diff
```

To see the changes that are staged for the next commit:
```bash
$ git diff --cached
```

To see the changes between two specific commits:
```bash
$ git diff commit1 commit2
```

### What `git diff` Does:
- **Unstaged Changes:** Shows the differences between the working directory and the staging area.
- **Staged Changes:** With the `--cached` option, it shows the differences between the staging area and the last commit.
- **Compare Commits:** Allows you to compare changes between two commits, which is useful for code review or tracking the evolution of a feature.

### Example Output
```plaintext
diff --git a/file.txt b/file.txt
index d1e8c9f..e42a1d1 100644
--- a/file.txt
+++ b/file.txt
@@ -1,3 +1,4 @@
 Line 1
 Line 2
 Line 3
+Line 4
```

The output shows the lines that were added, removed, or modified. In this example, `Line 4` was added to `file.txt`.

Using `git diff` helps you understand what has changed in your files and ensures that you're committing exactly what you intend to.



## `git reset`
The `git reset` command is a powerful tool in Git that allows you to undo changes in your repository. It can be used to unstage files or to reset your working directory to a previous commit. Depending on the options you use, `git reset` can modify the staging area, the working directory, and/or the commit history.

### Example
To unstage a file (move it from the staging area back to the working directory):
```bash
$ git reset filename
```

To reset the staging area and the working directory to match the specified commit:
```bash
$ git reset --hard commit-hash
```

### What `git reset` Does:
- **Unstage Files:** With no options, it moves files from the staging area back to the working directory without modifying the working directory itself.
- **Modify Commit History:** With the `--soft`, `--mixed`, and `--hard` options, it can also change the commit history.
    - `--soft`: Resets the commit history to the specified commit but leaves changes in the staging area.
    - `--mixed` (default): Resets the commit history and the staging area, but leaves changes in the working directory.
    - `--hard`: Resets the commit history, the staging area, and the working directory to match the specified commit. **Warning:** This option will discard any changes in the working directory.

### Example Workflow
```bash
# Unstage a file
$ git reset filename

# Reset to a previous commit, but keep changes in the working directory
$ git reset commit-hash

# Reset to a previous commit and discard all changes
$ git reset --hard commit-hash
```

Using `git reset` gives you the flexibility to undo changes at various levels, making it easier to manage your project's state.



## `git stash`
The `git stash` command is used to temporarily save (or "stash") changes in your working directory that are not yet ready to be committed. This is particularly useful if you need to switch branches or make some other changes but don't want to commit your current work yet.

### Example
To stash your changes:
```bash
$ git stash
```

To list all stashes:
```bash
$ git stash list
```

To apply the most recent stash:
```bash
$ git stash apply
```

### What `git stash` Does:
- **Save Changes Temporarily:** Moves your changes from the working directory to a stash stack, cleaning up the working directory.
- **Multiple Stashes:** You can have multiple stashes, and each stash will be saved with a unique identifier.
- **Apply Stashes:** You can apply a stash to your working directory when you're ready to resume work.

### Example Workflow
```bash
# Stash your current changes
$ git stash

# Switch to a different branch
$ git checkout other-branch

# Do some work on the other branch...

# Switch back to the original branch
$ git checkout original-branch

# Apply the most recent stash
$ git stash apply
```

The `git stash` command is a great way to save your work-in-progress without committing it, keeping your branches clean and organized.



