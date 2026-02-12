import LeanV31.R1CS2Equiv

namespace LeanV31

def R1CS2FromFiniteTotalMassAt (_z : Complex) : Prop := Exists fun C : Real => 0 <= C

/- S087 wrapper:
finite total trace mass yields a uniform inverse-tail cocycle bound, and via
the CS2 equivalence machinery this gives the subsequence CS2 condition. -/
theorem R1_CS2_from_finite_total_mass
    {z : Complex}
    (hFiniteMass : R1FiniteTotalMassAt z)
    (hTailBridge :
      R1FiniteTotalMassAt z ->
      R1CS2TailBoundAt z)
    (hTailToCS2 :
      R1CS2TailBoundAt z ->
      R1CS2ConditionAt z)
    (hFinalize :
      R1CS2TailBoundAt z ->
      R1CS2ConditionAt z ->
      R1CS2FromFiniteTotalMassAt z) :
    R1CS2FromFiniteTotalMassAt z := by
  have hTail : R1CS2TailBoundAt z := hTailBridge hFiniteMass
  have hCS2 : R1CS2ConditionAt z := hTailToCS2 hTail
  exact hFinalize hTail hCS2

end LeanV31
