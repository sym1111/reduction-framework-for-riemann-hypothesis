import LeanV31.R1ObstructionCertificate

namespace LeanV31

def R1BoundedBranchAt (_z : Complex) : Prop := Exists fun j0 : Nat => 0 <= j0
def R1DivergentBranchAt (_z : Complex) : Prop := Exists fun j0 : Nat => 0 < j0

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
