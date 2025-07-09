#!/bin/bash
echo "🚀 ABSOLUTE GIT INITIALIZATION"
echo "=============================="

# Some background agents check for these environment variables
export GIT_DIR=".git"
export GIT_WORK_TREE="."

# Current working directory
CWD=$(pwd)
echo "Working directory: $CWD"

# Sometimes agents look for git in specific paths
which git
git --version

# Explicit git repository check
if git rev-parse --git-dir >/dev/null 2>&1; then
    echo "✅ Git repository detected at: $(git rev-parse --git-dir)"
else
    echo "❌ Git repository not detected - initializing..."
    git init .
fi

# Check if we're inside a git repository 
if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    echo "✅ Inside git working tree: $(git rev-parse --is-inside-work-tree)"
else
    echo "❌ Not inside git working tree"
fi

# Show the git root directory
echo "Git root: $(git rev-parse --show-toplevel 2>/dev/null || echo 'NOT FOUND')"

# Explicit status check
echo "Git status exit code: $(git status >/dev/null 2>&1; echo $?)"

# Create the most basic possible git marker
echo "initialized" > .git/INITIALIZED
echo "$(date)" > .git/LAST_INIT

# Set basic git configuration
git config core.bare false
git config core.logallrefupdates true

echo ""
echo "🎯 FINAL VERIFICATION:"
echo "  pwd: $(pwd)"
echo "  git rev-parse --git-dir: $(git rev-parse --git-dir 2>/dev/null || echo 'FAILED')"
echo "  git status: $(git status --porcelain 2>/dev/null | wc -l | tr -d ' ') changes"
echo "  git branch: $(git branch --show-current 2>/dev/null || echo 'FAILED')"
echo ""
echo "✨ Repository should now be detected by any background agent!"
