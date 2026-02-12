import LeanV31.R1PrefixSubsequenceDivergence

namespace LeanV31

/- S063 wrapper:
under mass divergence, prefix divergence eliminates the bounded branch in the
rank-one radius-floor dichotomy, so only the divergent branch remains with the
corresponding CS2 obstruction consequences. -/
theorem R1_mass_divergence_selects_divergent_branch
    {z : Complex}
    (hPrefixDiverges : R1PrefixMassDivergesAlongSubseqAt z)
    (hDichotomy :
      (R1BoundedBranchAt z \/ R1DivergentBranchAt z) /\
      (R1BoundedBranchAt z -> R1DivergentBranchAt z -> False))
    (hSelectBridge :
      R1PrefixMassDivergesAlongSubseqAt z ->
      ((R1BoundedBranchAt z \/ R1DivergentBranchAt z) /\
        (R1BoundedBranchAt z -> R1DivergentBranchAt z -> False)) ->
      R1DivergentBranchAt z)
    (hConsequenceBridge :
      R1DivergentBranchAt z ->
      R1KjDivergesAt z /\ R1CS2FailsAt z) :
    R1DivergentBranchAt z /\ R1KjDivergesAt z /\ R1CS2FailsAt z := by
  have hDiv : R1DivergentBranchAt z := hSelectBridge hPrefixDiverges hDichotomy
  have hCons : R1KjDivergesAt z /\ R1CS2FailsAt z := hConsequenceBridge hDiv
  exact And.intro hDiv hCons

end LeanV31
