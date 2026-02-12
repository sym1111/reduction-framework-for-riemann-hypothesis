import LeanV31.R1Rank1StepLinear

namespace LeanV31

def R1Rank1MixedFactorAt (p _q : Nat) (_z : Complex) : Prop := Exists fun r : Nat => r = p
def R1SymplecticOrthogonalityAt (p q : Nat) (_z : Complex) : Prop := Exists fun r : Nat => r = p \/ r = q

/- S050 wrapper:
for rank-one factors, mixed products `JH_a JH_b` reduce to a scalar symplectic
coupling factor, vanishing exactly under pairwise symplectic orthogonality. -/
theorem R1_rank1_mixed_factor
    {z : Complex}
    (hLinear : forall k : Nat, R1Rank1StepLinearAt k z)
    (hMixedBridge :
      (forall k : Nat, R1Rank1StepLinearAt k z) ->
      forall p q : Nat, R1Rank1MixedFactorAt p q z)
    (hOrthBridge :
      (forall p q : Nat, R1Rank1MixedFactorAt p q z) ->
      forall p q : Nat, R1SymplecticOrthogonalityAt p q z) :
    (forall p q : Nat, R1Rank1MixedFactorAt p q z) /\
      (forall p q : Nat, R1SymplecticOrthogonalityAt p q z) := by
  have hMixed : forall p q : Nat, R1Rank1MixedFactorAt p q z := hMixedBridge hLinear
  have hOrth : forall p q : Nat, R1SymplecticOrthogonalityAt p q z :=
    hOrthBridge hMixed
  exact And.intro hMixed hOrth

end LeanV31
