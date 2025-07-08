#!/usr/bin/env bash
set -euo pipefail

echo "🔍 Checking foundation layer integrity..."

# Build the project
echo "📦 Building project..."
lake build || { echo "❌ Build failed"; exit 1; }

# Check for forbidden keywords in foundation/
echo "🚫 Checking for sorry/admit/axiom in foundation/..."
if rg -n "^[[:space:]]*(sorry|admit|axiom)" foundation/; then
    echo "❌ FAILED: Found forbidden keywords (sorry/admit/axiom) in foundation/"
    exit 1
else
    echo "✅ No sorry/admit/axiom found in foundation/"
fi

# Check that all Lean files have proper headers
echo "📄 Checking file headers..."
for file in $(find foundation -name "*.lean" -type f); do
    if ! head -n 10 "$file" | grep -q "This file is in \`foundation/\`"; then
        echo "⚠️  WARNING: $file missing foundation header"
    fi
done

# Count theorems and definitions
echo "📊 Foundation statistics:"
echo -n "  Theorems: "
rg "^(theorem|lemma)" foundation/ -c | awk -F: '{sum += $2} END {print sum}'
echo -n "  Definitions: "
rg "^(def|structure|inductive|class)" foundation/ -c | awk -F: '{sum += $2} END {print sum}'

echo "✅ Foundation check complete!"
