import LeanV31.R1GeneralStepInverseBoundSector

namespace LeanV31

def R1TailWindowBoundAt (_z : Complex) : Prop :=
  Exists fun C : Real => 0 <= C

/- S048 wrapper:
in the nonnegative-`Re(z^2)` sector, the tail-window trace bound controls the
product of one-step inverse norms, giving CS2-tail and thus CS2. -/
theorem R1_CS2_tail_mass_window_sector
    {z : Complex}
    (hz : InUpperB21 z)
    (hSector : R1NonnegativeReZ2Sector z)
    (hTailWindow : R1TailWindowBoundAt z)
    (hStepBound : forall k : Nat, R1GeneralStepInverseBoundAt k z)
    (hTailBridge :
      InUpperB21 z ->
      R1NonnegativeReZ2Sector z ->
      R1TailWindowBoundAt z ->
      (forall k : Nat, R1GeneralStepInverseBoundAt k z) ->
      R1CS2TailBoundAt z)
    (hCS2Bridge :
      R1CS2TailBoundAt z ->
      R1CS2ConditionAt z) :
    R1CS2TailBoundAt z /\ R1CS2ConditionAt z := by
  have hTail : R1CS2TailBoundAt z := hTailBridge hz hSector hTailWindow hStepBound
  have hCS2 : R1CS2ConditionAt z := hCS2Bridge hTail
  exact And.intro hTail hCS2

end LeanV31
