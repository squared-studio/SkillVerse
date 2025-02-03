# Git Concepts  

## Branch
A **branch** is a parallel workspace that lets you develop features, fix bugs, or experiment **without altering the main codebase**. Think of it as a "safe zone" for changes.  

### Key Features:  
- **Isolation**: Work independently without affecting `main`/`master`.  
- **Merge-Ready**: Integrate changes back via pull requests.  
- **Common Branch Types**:  
  - `feature/new-login` (for new functionality)  
  - `bugfix/crash-on-startup` (for fixes)  
  - `experiment/ai-integration` (for testing ideas)  

**Example**:  
```bash  
git checkout -b feature/dark-mode  # Create and switch to a new branch  
```  

## Commit
A **commit** is a *snapshot* of your code at a point in time. It’s like a "save point" in a game – you can always roll back to it.  

### Best Practices:  
- **Atomic Commits**: One logical change per commit (e.g., "Fix login button color", not "Update stuff").  
- **Meaningful Messages**:  
  ```bash  
  git commit -m "feat: add user authentication  
  - Implement OAuth2 login  
  - Add error handling for failed auth"  
  ```  
- **SHA-1 Hash**: Unique ID for every commit (e.g., `a1b2c3d`).  

**Undo Mistakes**:  
```bash  
git reset --soft HEAD~1  # Undo last commit but keep changes  
```  

## Issue
**Issues** track tasks, bugs, or ideas in collaboration platforms like GitHub/GitLab. They’re your project’s to-do list.  

### Why Use Issues?  
- **Centralized Tracking**: No more lost sticky notes!  
- **Workflow Integration**: Link issues to commits/PRs with keywords:  
  ```  
  Fixes #45  # Automatically closes issue 45 when merged  
  ```  
- **Labels & Assignees**: Prioritize with `bug`, `feature`, or `urgent`.  

**Pro Tip**: Use issue templates to standardize bug reports or feature requests.  

## Push
`git push` uploads your local commits to a remote repository (like GitHub).  

### Key Notes:  
- **First Push?** Use `-u` to set upstream:  
  ```bash  
  git push -u origin feature/dark-mode  
  ```  
- **Force Push** (use with caution!):  
  ```bash  
  git push --force  # Rewrites remote history – risky!  
  ```  

**Example Workflow**:  
```bash  
git add .  
git commit -m "feat: add dark mode toggle"  
git push origin feature/dark-mode  
```  

## Pull
`git pull` syncs your local repo with the remote. It’s shorthand for:  
```bash  
git fetch + git merge  
```  

### Pro Tips:  
- **Avoid Surprises**: Always `pull` before starting work.  
- **Prefer Fetch + Merge**:  
  ```bash  
  git fetch origin  # Check for updates  
  git merge origin/main  # Merge manually  
  ```  

**Conflict Alert**: If changes clash, Git will prompt you to resolve them.  

## Pull Request (PR)
A **pull request** proposes merging changes from one branch to another (usually `feature → main`). It’s where code review happens!  

### PR Lifecycle:  
1. **Create**: After pushing a branch.  
2. **Review**: Team comments on code.  
3. **Test**: CI/CD runs checks (tests, linting).  
4. **Merge**: Approved changes join the main codebase.  

**Golden Rules**:  
- Keep PRs small (under 300 lines).  
- Use descriptive titles: "Fix image scaling bug" > "Update code".  

**GitHub Magic**:  
```  
Close #12  # Link PR to issue  
```  

### Concept Cheat Sheet
| Command          | Action                                  |  
|------------------|-----------------------------------------|  
| `git branch`     | List/create branches                    |  
| `git commit`     | Save changes with a message             |  
| `git push`       | Upload local commits to remote          |  
| `git pull`       | Download and merge remote changes       |  
| `gh pr create`   | Create a PR (GitHub CLI)                |  
