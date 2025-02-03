# Basics

## `git init`  
**Initialize a new Git repository** in your project folder.  

### Key Points:  
- **One-time setup** for new projects.  
- Creates a hidden `.git` directory to track changes.  
- Run this *before* adding files.  

### Example:  
```bash  
cd my-project  
git init  # Now ready for commits!  
```  

## `git clone`  
**Copy an existing repo** to your local machine.  

### Usage:  
```bash  
git clone https://github.com/user/repo.git  
```  
**Pro Tips**:  
- Use **SSH** for secure access: `git clone git@github.com:user/repo.git`.  
- Clone into a custom folder: `git clone URL folder-name`.  

## `git status`  
**Check what’s changed** in your working directory.  

### Sample Output:  
```  
On branch main  
Changes not staged:  
  (use "git add <file>..." to update)  
  modified:   index.html  
  
Untracked files:  
  (use "git add <file>..." to include)  
  new-file.txt  
```  

**Use `-s` for short format**:  
```bash  
git status -s  # Output: M index.html, ?? new-file.txt  
```  

## `git add`  
**Stage changes** for the next commit.  

### Common Use Cases:  
```bash  
git add .               # Stage all changes  
git add file1.js        # Stage one file  
git add *.css           # Stage all CSS files  
```  

**Watch Out!**  
- `git add .` includes new files. Use `git add -u` to only stage modified/deleted files.  

## `git commit`  
**Save staged changes** to your local repo.  

### Best Practices:  
- Write **atomic commits** (one logical change per commit).  
- Use the [Conventional Commits](https://www.conventionalcommits.org/) style:  
  ```bash  
  git commit -m "feat: add dark mode toggle"  
  git commit -m "fix: resolve login button crash"  
  ```  

## `git push`  
**Upload local commits** to a remote repo.  

### First Push? Set Upstream:  
```bash  
git push -u origin main  # Links local branch to remote  
```  

**Fix Rejected Push**:  
```bash  
git pull --rebase origin main  # Sync with remote first  
git push  
```  

## `git fetch`  
**Download remote changes** without merging.  

```bash  
git fetch origin  # Fetches updates but leaves your code untouched  
git log origin/main  # See what’s new  
```  

**VS `git pull`**:  
- `fetch` → review → merge = safer workflow.  
- `pull` = `fetch` + `merge` (can cause surprises).  

## `git pull`  
**Sync local branch** with remote changes.  

```bash  
git pull origin main  
```  
**Conflict Alert**: If others edited the same files, resolve conflicts manually.  

## `git checkout`  
**Switch branches** or **restore files**.  

### Switch/Create Branches:  
```bash  
git checkout main           # Switch to main  
git checkout -b new-feature # Create and switch to new branch  
```  

### Undo File Changes:  
```bash  
git checkout HEAD -- style.css  # Revert style.css to last commit  
```  

## `git log`  
**View commit history**.  

### Handy Flags:  
```bash  
git log --oneline          # Compact view  
git log -p                 # Show code changes  
git log --graph --decorate # Visualize branches  
git log -2                 # Last 2 commits  
```  

## `git diff`  
**See line-by-line changes**.  

```bash  
git diff           # Unstaged changes  
git diff --staged  # Staged changes  
git diff HEAD~3    # Compare to 3 commits ago  
```  

## `git reset`  
**Undo commits or unstage files**.  

### Soft Reset (Keep Changes):  
```bash  
git reset --soft HEAD~1  # Undo last commit, keep code staged  
```  

### Hard Reset (DANGER!):  
```bash  
git reset --hard HEAD~3  # Delete last 3 commits and all changes
```  

## `git stash`  
**Temporarily shelve changes**.  

```bash  
git stash          # Save changes  
git stash list     # View stashes  
git stash pop      # Apply and delete most recent stash  
```  

**Scenario**:  
```bash  
# Work on main → urgent fix needed  
git stash  
git checkout hotfix-branch  
# Fix the bug → commit → push  
git checkout main  
git stash pop  
```  

### **Quick Reference Table**  
| Command              | Action                                      |  
|----------------------|---------------------------------------------|  
| `git init`           | Create new repo                             |  
| `git clone URL`      | Copy remote repo                            |  
| `git status`         | Check changes                               |  
| `git add .`          | Stage all files                             |  
| `git commit -m "..."`| Save changes                                |  
| `git push`           | Upload to remote                            |  
| `git pull`           | Download and merge updates                  |  
| `git checkout -b ...`| Create/swich branch                         |  
| `git log --oneline`  | Compact history                             |  
