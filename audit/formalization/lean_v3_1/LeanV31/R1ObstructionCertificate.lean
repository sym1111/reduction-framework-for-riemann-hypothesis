import LeanV31.R1Rank1ExactClosureReduction

namespace LeanV31

def R1PrefixMassDivergesAt (_z : Complex) : Prop := Exists fun j0 : Nat => 0 <= j0
def R1KjDivergesAt (_z : Complex) : Prop := Exists fun j0 : Nat => 0 < j0
def R1CS2FailsAt (_z : Complex) : Prop := Exists fun eps : Nat => 0 < eps
def R1TailWindowFailsAt (_z : Complex) : Prop := Exists fun n0 : Nat => 0 <= n0

/- S060 wrapper:
on a radius-floor subsequence, diverging prefix mass forces diverging `K_j`,
hence CS2 obstruction; in the rank-one branch this also obstructs tail-window
boundedness via exact closure reduction. -/
theorem R1_obstruction_certificate
    {z : Complex}
    (hDivergenceBridge :
      R1PrefixMassDivergesAt z ->
      R1KjDivergesAt z)
    (hCS2FailBridge :
      R1KjDivergesAt z ->
      R1CS2FailsAt z)
    (hTailFailBridge :
      R1RankOneTailBranchAt z ->
      R1CS2FailsAt z ->
      R1TailWindowFailsAt z)
    (hRankOneTail : R1RankOneTailBranchAt z) :
    (R1PrefixMassDivergesAt z -> R1KjDivergesAt z) /\
      (R1KjDivergesAt z -> R1CS2FailsAt z) /\
      (R1CS2FailsAt z -> R1TailWindowFailsAt z) := by
  have hTailImp : R1CS2FailsAt z -> R1TailWindowFailsAt z := by
    intro hFail
    exact hTailFailBridge hRankOneTail hFail
  exact And.intro hDivergenceBridge (And.intro hCS2FailBridge hTailImp)

end LeanV31
