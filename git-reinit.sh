#!/bin/bash
echo "🔄 GIT RE-INITIALIZATION FOR BACKGROUND AGENT"
echo "=============================================="

# Save current state
CURRENT_BRANCH=$(git branch --show-current)
REMOTE_URL=$(git remote get-url origin)

echo "Current branch: $CURRENT_BRANCH"
echo "Remote URL: $REMOTE_URL"

# Verify .git directory exists and is valid
if [ ! -d ".git" ]; then
    echo "❌ No .git directory found"
    echo "🔧 Running git init..."
    git init
    git remote add origin "$REMOTE_URL"
else
    echo "✅ .git directory exists"
fi

# Ensure HEAD is properly set
if [ ! -f ".git/HEAD" ]; then
    echo "🔧 Creating HEAD reference..."
    echo "ref: refs/heads/$CURRENT_BRANCH" > .git/HEAD
fi

# Ensure proper git configuration
git config user.name "Background Agent" 2>/dev/null || true
git config user.email "agent@ledger-ethics.local" 2>/dev/null || true

# Verify all git components
echo "📋 VERIFICATION:"
echo "  Git directory: $(test -d .git && echo '✅ YES' || echo '❌ NO')"
echo "  HEAD file: $(test -f .git/HEAD && echo '✅ YES' || echo '❌ NO')"
echo "  Config file: $(test -f .git/config && echo '✅ YES' || echo '❌ NO')"
echo "  Objects dir: $(test -d .git/objects && echo '✅ YES' || echo '❌ NO')"
echo "  Refs dir: $(test -d .git/refs && echo '✅ YES' || echo '❌ NO')"
echo "  Clean status: $(git status --porcelain | wc -l | tr -d ' ') files"

# Create explicit marker files that background agents often look for
echo "true" > .git/REPOSITORY_INITIALIZED
echo "background-agent-ready" > .git/AGENT_READY
echo "$CURRENT_BRANCH" > .git/CURRENT_BRANCH
echo "$REMOTE_URL" > .git/REMOTE_URL

echo ""
echo "🎉 GIT RE-INITIALIZATION COMPLETE!"
echo "📁 Working directory: $(pwd)"
echo "🌿 Branch: $(git branch --show-current)"
echo "🔗 Remote: $(git remote get-url origin)"
echo "✨ Status: Ready for background agent"
