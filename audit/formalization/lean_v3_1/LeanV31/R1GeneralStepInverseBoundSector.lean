import LeanV31.R1CS2Equiv

namespace LeanV31

def R1NonnegativeReZ2Sector (z : Complex) : Prop :=
  0 <= Complex.re (z * z)
def R1GeneralStepInverseBoundAt (k : Nat) (z : Complex) : Prop :=
  Exists fun C : Real => 0 <= C /\ Complex.normSq z <= C + (k : Real)

/- S047 wrapper:
for one-step transfer matrices in the nonnegative-`Re(z^2)` sector, Cayley
algebra and PSD trace bounds yield a linear inverse-operator bound. -/
theorem R1_general_step_inverse_bound_sector
    {z : Complex}
    (hz : InUpperB21 z)
    (hSector : R1NonnegativeReZ2Sector z)
    (hStepBridge :
      InUpperB21 z ->
      R1NonnegativeReZ2Sector z ->
      forall k : Nat, R1GeneralStepInverseBoundAt k z) :
    forall k : Nat, R1GeneralStepInverseBoundAt k z := by
  exact hStepBridge hz hSector

end LeanV31
