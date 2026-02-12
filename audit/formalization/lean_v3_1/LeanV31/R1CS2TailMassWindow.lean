import LeanV31.R1Rank1StepLinear
import LeanV31.R1CS2Equiv

namespace LeanV31

def R1RankOneTailBranchAt (_z : Complex) : Prop :=
  Exists fun u : Nat -> Nat => StrictMono u

/- S052 wrapper:
on the rank-one branch, a uniform tail-mass window bound gives a uniform
tail-cocycle bound, and via CS2 equivalence yields CS2. -/
theorem R1_CS2_tail_mass_window
    {z : Complex}
    (hz : InUpperB21 z)
    (hTailWindow : R1TailWindowBoundAt z)
    (hRankOneTail : R1RankOneTailBranchAt z)
    (hStepLinear : forall k : Nat, R1Rank1StepLinearAt k z)
    (hTailBridge :
      InUpperB21 z ->
      R1TailWindowBoundAt z ->
      R1RankOneTailBranchAt z ->
      (forall k : Nat, R1Rank1StepLinearAt k z) ->
      R1CS2TailBoundAt z)
    (hCS2Bridge :
      R1CS2TailBoundAt z ->
      R1CS2ConditionAt z) :
    R1CS2TailBoundAt z /\ R1CS2ConditionAt z := by
  have hTail : R1CS2TailBoundAt z := hTailBridge hz hTailWindow hRankOneTail hStepLinear
  have hCS2 : R1CS2ConditionAt z := hCS2Bridge hTail
  exact And.intro hTail hCS2

end LeanV31
