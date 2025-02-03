# Merge Conflicts

## What Causes a Merge Conflict?  
Git fails to auto-merge when:  
1. **Same Line Edits**: Two branches modify identical lines  
   ```python  
   # Branch A:  
   print("Hello World")  
   # Branch B:  
   print("Bonjour le monde")  
   ```  
2. **File Deletion Wars**: One branch deletes a file, another modifies it  
3. **Structural Clashes**: Conflicting directory reorganizations  

## How to Spot Merge Conflicts  
Git marks conflict zones with **"<<<<<<<"** markers:  
```javascript  
<<<<<<< HEAD // Your version  
const apiUrl = "https://your-api.com";  
=======      // Incoming changes  
const apiUrl = "https://new-api-service.dev";  
>>>>>>> feature/new-api  
```  
- **HEAD**: Your current branch's code  
- **=======**: Conflict divider  
- **>>>>>>> feature/new-api**: The incoming branch's code  

## Resolving Conflicts: Step-by-Step  

### 1. Abort or Engage?  
```bash  
git merge --abort  # Cancel merge (safe for beginners)  
# OR  
git status         # See conflicted files  
```

### 2. Resolve in Your Editor  
**VS Code Users**:  
1. Open conflicted file → Click "Resolve in Merge Editor"  
2. Choose between current/incoming changes or edit manually  
![VS Code Merge Tool](https://example.com/vscode-merge.png)  

**CLI Warriors**:  
```bash  
nano conflicted-file.js  # Manually edit between markers  
```

### 3. Finalize the Peace Treaty  
```bash  
git add .  # Stage resolved files  
git commit -m "Merge feat/new-api: resolve URL conflict"  
```

## Pro Conflict Resolution Kit  

### Test-Driven Merging  
```bash  
git checkout main  
git merge --no-ff --no-commit feature/new-api  
npm test    # Run tests before committing!  
```

### Smart Merge Strategies  
```bash  
git config --global merge.conflictStyle diff3  # Show common ancestor  
git config --global rerere.enabled true        # Remember resolutions  
```

### Prevention Tactics  
1. **Rebase Often**  
   ```bash  
   git fetch && git rebase origin/main  
   ```  
2. **Small PRs** → Fewer conflict opportunities  
3. **CI Guardians**: Set up GitHub Actions to block conflicting merges  
   ```yaml  
   # .github/workflows/conflict-check.yml  
   - name: Check for Conflicts  
     run: git merge --no-ff $GITHUB_HEAD_REF  
   ```

## Real-World Scenario: The API Endpoint War  

**Actors**:  
- Alice edits `config.js` line 12 → `api.example.com/v1`  
- Bob edits same line → `api.example.com/v2`  

**Resolution**:  
1. Bob pulls latest main:  
   ```bash  
   git pull origin main  
   ```  
2. Git flags conflict in `config.js`  
3. Team decision: Use v2 endpoint but keep v1 fallback  
   ```javascript  
   // Resolved code  
   const API_VERSION = process.env.USE_V2 ? 'v2' : 'v1';  
   ```  
4. Commit & push:  
   ```bash  
   git add config.js  
   git commit -m "Merge API versions with feature flag"  
   git push  
   ```

## Merge Conflict Cheat Sheet  

| Command                           | Action                                  |  
|-----------------------------------|-----------------------------------------|  
| `git diff --name-only --diff-filter=U` | List conflicted files            |  
| `git checkout --ours file.txt`    | Keep your version                     |  
| `git checkout --theirs file.txt`  | Take incoming changes                |  
| `git mergetool`                   | Launch visual merge tool              |  

## Wisdom Nuggets  
- "Conflicts are opportunities for better design" - Senior Dev Mantra  
- Use GitHub's **Conflict Editor** for web-based resolution  
- Celebrate conflict resolutions with :tada: in PR comments!
