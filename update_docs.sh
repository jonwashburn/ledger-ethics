#!/bin/bash

# Update good_is_zero_curvature
sed -i '' '206s|/-- Good is geometric flatness in recognition space -/|/-- Good is defined as zero moral curvature|' Ethics/Main.lean
sed -i '' '206a\
A moral state is good when its ledger is perfectly balanced,\
representing a flat geometry in recognition space with no moral debt. -/' Ethics/Main.lean

# Update evil_amplifies_curvature  
sed -i '' '213s|/-- Evil amplifies curvature through falsification -/|/-- Evil actions amplify moral curvature through falsification|' Ethics/Main.lean
sed -i '' '213a\
When an evil act breaks conservation laws, it creates runaway curvature growth,\
demonstrating how destructive actions compound their negative effects over time. -/' Ethics/Main.lean

# Update love_locally_optimal
sed -i '' '237s|/-- Love is the optimal local strategy -/|/-- Love is the mathematically optimal local strategy for reducing moral curvature|' Ethics/Main.lean
sed -i '' '237a\
By equalizing curvature between two states, love minimizes the variance while\
preserving total curvature, making it the most efficient virtue for local healing. -/' Ethics/Main.lean

# Update suffering_is_debt_signal
sed -i '' '281s|/-- Suffering signals recognition debt -/|/-- Suffering is a direct signal of recognition debt in the moral ledger|' Ethics/Main.lean
sed -i '' '281a\
When moral curvature is positive (ledger imbalance with more debits than credits),\
this manifests experientially as suffering, providing clear feedback about moral state. -/' Ethics/Main.lean

# Update joy_enables_creation
sed -i '' '387s|/-- Joy enables creativity -/|/-- Joy (negative curvature) enables creative acts by providing surplus energy|' Ethics/Main.lean
sed -i '' '387a\
When the moral ledger has surplus credits, this manifests as joy and provides\
the energetic resources needed for creative expression and new value generation. -/' Ethics/Main.lean

