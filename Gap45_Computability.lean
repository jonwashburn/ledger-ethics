  -- This leads to a contradiction with the period analysis
  -- Since s has period 45 and is in Gap45, any resolution requires ≥ 360 steps
  have h_period : Nat.lcm 8 s.period ≥ 360 := by
    unfold diagonalState at hs_gap
    exact lcm_blowup_45 s hs_gap
  -- But we claimed m < 360, contradiction
  linarith
