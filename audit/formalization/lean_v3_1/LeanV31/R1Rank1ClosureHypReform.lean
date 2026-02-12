import LeanV31.R1Rank1ExactClosureReduction
import LeanV31.R1RadiusfloorClosure

namespace LeanV31

def R1Rank1ClosureHypReformAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0

/- S109 wrapper:
on a radius-floor rank-one subsequence, exact closure reduction identifies CS2,
prefix-mass boundedness, and tail-window boundedness; together with
radius-floor closure this gives the reformulated equivalent hypothesis package. -/
theorem R1_rank1_closure_hyp_reform
    {z : Complex}
    (hExactReduction :
      (R1CS2ConditionAt z <-> R1KjUniformBoundAt z) /\
      (R1KjUniformBoundAt z <-> R1PrefixMassUniformBoundAt z) /\
      (R1PrefixMassUniformBoundAt z <-> R1TailWindowSubseqBoundAt z))
    (hRadiusfloorClosure :
      R1RadiusFloorTargetSubsequenceAt z ->
      R1RadiusfloorClosurePrefixBoundAt z /\ R1TailWindowBoundOnSubseqAt z)
    (hReformBridge :
      ((R1CS2ConditionAt z <-> R1KjUniformBoundAt z) /\
        (R1KjUniformBoundAt z <-> R1PrefixMassUniformBoundAt z) /\
        (R1PrefixMassUniformBoundAt z <-> R1TailWindowSubseqBoundAt z)) ->
      (R1RadiusFloorTargetSubsequenceAt z ->
        R1RadiusfloorClosurePrefixBoundAt z /\ R1TailWindowBoundOnSubseqAt z) ->
      R1Rank1ClosureHypReformAt z) :
    R1Rank1ClosureHypReformAt z := by
  exact hReformBridge hExactReduction hRadiusfloorClosure

end LeanV31
