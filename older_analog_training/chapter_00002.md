# Task 2 : Introduction to git

## Introduction

GitHub is a web-based platform used for version control. Git simplifies the process of working with other people and makes it easy to collaborate on projects. Team members can work on files and easily merge their changes in with the master branch of the project.

GitHub is also a powerful tool for businesses. It allows businesses to track progress on their repositories and download the latest versions of software without having to build the software themselves. It also integrates with common platforms like AWS and Google Cloud, making it a robust tool for DevOps.

In addition to being a great tool for developers, GitHub has features that are useful to people in many different roles. For example, project managers can use GitHub to track bugs and feature requests. Designers can use GitHub to manage their design files and keep track of changes.

Overall, GitHub is a comprehensive platform for software development, with a strong community that provides a wealth of resources and knowledge for users and developers alike. It’s an essential tool for anyone involved in programming, from beginners to experts.

## Commonly used git commands

**`git clone`**: Creates a local copy of a project that already exists remotely. The clone includes all the project’s files, history, and branches.

When to use:
- When you need to start working on a project that is hosted on a remote repository.

How to use:
```bash
$ git clone https://github.com/user/repository.git
```

**`git add`**: Stages a change. Git tracks changes to a developer’s codebase, but it’s necessary to stage and take a snapshot of the changes to include them in the project’s history.

When to use:
- When you have made changes to files and want to include them in the next commit.

How to use:
```bash
$ git add file.txt
$ git add .
```

**`git commit`**: Saves the snapshot to the project history and completes the change-tracking process. In short, a commit functions like taking a photo. Anything that’s been staged with `git add` will become a part of the snapshot with `git commit`.

When to use:
- After staging changes with `git add` and you are ready to save them to the project history.

How to use:
```bash
$ git commit -m "Commit message"
```

**`git status`**: Shows the status of changes as untracked, modified, or staged.

When to use:
- To check the status of your working directory and staging area.

How to use:
```bash
$ git status
```

**`git branch`**: Shows the branches being worked on locally.

When to use:
- To list all branches or create a new branch.

How to use:
```bash
$ git branch
$ git branch new-branch
```

**`git merge`**: Merges lines of development together. This command is typically used to combine changes made on two distinct branches.

When to use:
- To merge changes from one branch into another.

How to use:
```bash
$ git merge branch-name
```

**`git pull`**: Updates the local line of development with updates from its remote counterpart. Developers use this command if a teammate has made commits to a branch on a remote, and they would like to reflect those changes in their local environment.

When to use:
- To fetch and merge changes from the remote repository to your local repository.

How to use:
```bash
$ git pull
```

**`git push`**: Uplinks the local repository to the remote repository. This command is used to upload local repository content to a remote repository.

When to use:
- To push your local commits to the remote repository.

How to use:
```bash
$ git push origin branch-name
```

**`git checkout`**: This command is used to switch from one branch to another. It can also be used to restore files.

When to use:
- To switch branches or restore files.

How to use:
```bash
$ git checkout branch-name
$ git checkout -- file.txt
```

**`git stash`**: This command temporarily saves changes that you don't want to commit immediately. You can apply the stashed changes later.

When to use:
- To save changes temporarily without committing them.

How to use:
```bash
$ git stash
$ git stash apply
```

**`git reset`**: This command is used to reset your index as well as the working directory to the state of your last commit.

When to use:
- To undo changes and reset the working directory.

How to use:
```bash
$ git reset --hard
```

**`git log`**: This command is used to display the commit history.

When to use:
- To view the commit history of the repository.

How to use:
```bash
$ git log
```

**`git diff`**: This command shows the file differences which are not yet staged.

When to use:
- To see changes between commits, commit and working tree, etc.

How to use:
```bash
$ git diff
```
