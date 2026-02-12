import LeanV31.R1Rank1ExactClosureReduction

namespace LeanV31

def R1PrefixMassDivergesAt (_z : Complex) : Prop :=
  forall M : Real, Exists fun N : Nat => M <= R1PrefixTraceMassAt N

def R1KjDivergesAt (z : Complex) : Prop :=
  ¬ R1KjUniformBoundAt z

def R1CS2FailsAt (z : Complex) : Prop :=
  ¬ R1CS2ConditionAt z

def R1TailWindowFailsAt (z : Complex) : Prop :=
  ¬ R1TailWindowSubseqBoundAt z

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
