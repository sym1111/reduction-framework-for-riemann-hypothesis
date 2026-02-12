import LeanV31.R1KappaPointwiseTailExp

namespace LeanV31

def R1PrefixMassUniformBoundAt (_z : Complex) : Prop :=
  Exists fun C : Real =>
    0 <= C /\ forall j : Nat, R1PrefixTraceMassAt j <= C

def R1KjUniformBoundAt (z : Complex) : Prop :=
  Exists fun C : Real =>
    0 <= C /\ forall j : Nat, R1KappaGaugeAt j z <= C

/- S057 wrapper:
on a radius-floor rank-one subsequence, lower/upper kappa controls from prefix
mass yield equivalence of growth scales between `K_j` and prefix mass. -/
theorem R1_Kj_prefix_equiv_rank1
    {z : Complex}
    (hLowerBridge :
      (forall j : Nat, R1KappaLowerFromPrefixAt j z) ->
      R1PrefixMassUniformBoundAt z ->
      R1KjUniformBoundAt z)
    (hUpperBridge :
      (forall k j : Nat, R1KappaPointwiseTailExpAt k j z) ->
      R1KjUniformBoundAt z ->
      R1PrefixMassUniformBoundAt z)
    (hLower : forall j : Nat, R1KappaLowerFromPrefixAt j z)
    (hPointwise : forall k j : Nat, R1KappaPointwiseTailExpAt k j z) :
    (R1PrefixMassUniformBoundAt z -> R1KjUniformBoundAt z) /\
      (R1KjUniformBoundAt z -> R1PrefixMassUniformBoundAt z) := by
  have hPmToK : R1PrefixMassUniformBoundAt z -> R1KjUniformBoundAt z := by
    intro hPm
    exact hLowerBridge hLower hPm
  have hKToPm : R1KjUniformBoundAt z -> R1PrefixMassUniformBoundAt z := by
    intro hK
    exact hUpperBridge hPointwise hK
  exact And.intro hPmToK hKToPm

end LeanV31
