import LeanV31.R1ObstructionCertificate

namespace LeanV31

def R1BoundedBranchAt (z : Complex) : Prop :=
  R1KjUniformBoundAt z /\ R1CS2ConditionAt z /\ R1TailWindowSubseqBoundAt z

def R1DivergentBranchAt (z : Complex) : Prop :=
  R1KjDivergesAt z /\ R1CS2FailsAt z /\ R1TailWindowFailsAt z

/- S061 wrapper:
for a rank-one radius-floor subsequence, exactly one branch occurs: bounded
prefix-mass/CS2/tail-window branch or divergent obstruction branch. -/
theorem R1_rank1_radiusfloor_dichotomy
    {z : Complex}
    (hSplit : R1BoundedBranchAt z \/ R1DivergentBranchAt z)
    (hExclusive :
      R1BoundedBranchAt z ->
      R1DivergentBranchAt z ->
      False) :
    (R1BoundedBranchAt z \/ R1DivergentBranchAt z) /\
      (R1BoundedBranchAt z -> R1DivergentBranchAt z -> False) := by
  exact And.intro hSplit hExclusive

end LeanV31
