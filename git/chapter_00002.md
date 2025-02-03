# Getting Started  

## Creating a New Git Repository via CLI  
**Initialize a Git repository** to start tracking your project. The `git init` command creates a hidden `.git` folder that stores version control data, enabling commits, branching, and collaboration.  

### Step-by-Step Guide (Local Repository):  
1. **Open a terminal** (Git Bash, Command Prompt, or PowerShell).  
2. **Navigate to your project folder**:  
   ```bash  
   cd path/to/your/project  
   ```  
3. **Initialize the repository**:  
   ```bash  
   git init  
   ```  
   *(Creates the `.git` directory to track changes)*  

4. **Stage files for commit**:  
   ```bash  
   git add .  # Stages all files  
   # OR  
   git add file1.txt file2.js  # Specific files  
   ```  

5. **Commit your changes**:  
   ```bash  
   git commit -m "Initial commit: project setup"  
   ```  

### Connect to GitHub (Optional):  
1. **Create a new empty repo** on [GitHub](https://github.com/new).  
2. **Link your local repo to GitHub**:  
   ```bash  
   git remote add origin https://github.com/username/repo-name.git  
   ```  
3. **Push changes**:  
   ```bash  
   git push -u origin main  # For "main" branch  
   ```  

## Creating a New Repository via GitHub Web  
**Ideal for new projects** – create a repo directly on GitHub’s platform.  

### Step-by-Step Guide:  
1. **Log in to GitHub** and click the **+** (top-right) → **New repository**.  
2. **Configure repo settings**:  
   - **Repository name**: `your-repo-name` (no spaces).  
   - **Visibility**: Public (open to all) or Private (restricted access).  
   - **Initialize options** (recommended):  
     - **Add a README**: Describe your project.  
     - **Add .gitignore**: Prevents tracking temporary/unnecessary files (e.g., `node_modules/`).  
     - **Choose a license**: MIT, Apache, etc.  
3. **Click "Create repository"**.  

**Pro Tip**:  
After creating the repo, clone it locally to start working:  
```bash  
git clone https://github.com/username/your-repo-name.git  
```  

## Cloning a Git Repository  
**Clone a repo** to create a local copy of a remote project. This includes the full history, branches, and collaboration capabilities.  

### Why Clone?  
- Work offline.  
- Contribute to open-source projects.  
- Test changes without affecting the original codebase.  

### Step-by-Step Guide:  
1. **Copy the repo URL** from GitHub:  
   - HTTPS: `https://github.com/username/repo.git`  
   - SSH: `git@github.com:username/repo.git`  

2. **In your terminal**:  
   ```bash  
   git clone https://github.com/username/repo.git  
   ```  
   ```  
   Cloning into 'repo'...  
   remote: Counting objects: 100% (75/75), done.  
   Resolving deltas: 100% (30/30), done.  
   ```  

3. **Navigate to the cloned folder**:  
   ```bash  
   cd repo  
   ```  

**Pro Tip**:  
Use `git clone --branch feature-branch https://github.com/...` to clone a specific branch.  
