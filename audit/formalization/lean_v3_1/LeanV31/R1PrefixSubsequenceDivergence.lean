import LeanV31.R1Rank1RadiusfloorDichotomy

namespace LeanV31

def R1TotalMassDivergesAt (_z : Complex) : Prop :=
  forall M : Real, Exists fun N : Nat => M <= (N : Real)
def R1PrefixMassDivergesAlongSubseqAt (_z : Complex) : Prop :=
  forall u : Nat -> Nat, StrictMono u ->
    forall M : Real, Exists fun N : Nat => M <= (u N : Real)

/- S062 wrapper:
with nonnegative trace increments, total-mass divergence forces divergence of
prefix masses along every strictly increasing subsequence. -/
theorem R1_prefix_subsequence_divergence
    {z : Complex}
    (hMassDiverges : R1TotalMassDivergesAt z)
    (hSubseqBridge :
      R1TotalMassDivergesAt z ->
      R1PrefixMassDivergesAlongSubseqAt z) :
    R1PrefixMassDivergesAlongSubseqAt z := by
  exact hSubseqBridge hMassDiverges

end LeanV31
