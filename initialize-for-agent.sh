#!/bin/bash
echo "🤖 BACKGROUND AGENT INITIALIZATION"
echo "=================================="

# Step 1: Verify git repository
echo "1. Checking Git Repository..."
if [ ! -d ".git" ]; then
    echo "❌ ERROR: No .git directory found"
    echo "Run this script from the repository root: /Users/jonathanwashburn/Desktop/Ethics/ledger-ethics"
    exit 1
fi
echo "✅ Git repository found"

# Step 2: Verify branch
CURRENT_BRANCH=$(git branch --show-current)
echo "2. Current branch: $CURRENT_BRANCH"
if [ "$CURRENT_BRANCH" != "background-agent-proofs" ]; then
    echo "⚠️  WARNING: Expected 'background-agent-proofs' branch"
    echo "   Run: git checkout background-agent-proofs"
fi

# Step 3: Verify remote
REMOTE_URL=$(git remote get-url origin 2>/dev/null)
echo "3. Remote URL: $REMOTE_URL"
if [ -z "$REMOTE_URL" ]; then
    echo "❌ ERROR: No remote origin configured"
    exit 1
fi
echo "✅ Remote configured"

# Step 4: Test build
echo "4. Testing Lean build..."
if ! lake build > /dev/null 2>&1; then
    echo "❌ ERROR: Lake build failed"
    echo "   Run: lake build"
    exit 1
fi
echo "✅ Lean build successful"

# Step 5: Check task file
echo "5. Checking task file..."
if [ ! -f "docs/BACKGROUND_AGENT_TASKS.md" ]; then
    echo "❌ ERROR: Task file not found"
    exit 1
fi
echo "✅ Task file found"

# Step 6: Count sorries
SORRY_COUNT=$(grep -rn "\bsorry\b" --include="*.lean" . | grep -v "Legacy" | grep -v "\.lake" | wc -l | tr -d ' ')
echo "6. Current sorry count: $SORRY_COUNT"

# Success!
echo ""
echo "🎉 INITIALIZATION COMPLETE!"
echo "=========================="
echo "Repository: Ready for background agent"
echo "Working Directory: $(pwd)"
echo "Branch: $CURRENT_BRANCH"
echo "Sorry count: $SORRY_COUNT to eliminate"
echo ""
echo "🚀 Start with: Ethics/HelperStubs.lean line 15"
echo "   Goal: Replace 'sorry' with 'Nat.zero_le n'"
