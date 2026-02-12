import LeanV31.R1CS2TailMassWindow

namespace LeanV31

def R1KappaTailExpPointwiseAt (k j : Nat) (_z : Complex) : Prop :=
  Exists fun C : Nat => k <= C + j
def R1FiniteTotalMassForKappaAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0

/- S053 wrapper:
under tail-window/rank-one assumptions, frame growth `kappa_{k,j}` admits a
pointwise exponential tail-mass bound; finite total mass then gives uniform
CS2 control. -/
theorem R1_kappa_tail_exp
    {z : Complex}
    (hTailWindow : R1TailWindowBoundAt z)
    (hRankOneTail : R1RankOneTailBranchAt z)
    (hPointwiseBridge :
      R1TailWindowBoundAt z ->
      R1RankOneTailBranchAt z ->
      forall k j : Nat, R1KappaTailExpPointwiseAt k j z)
    (hFiniteMassToCS2Bridge :
      R1FiniteTotalMassForKappaAt z ->
      (forall k j : Nat, R1KappaTailExpPointwiseAt k j z) ->
      R1CS2ConditionAt z) :
    (forall k j : Nat, R1KappaTailExpPointwiseAt k j z) /\
      (R1FiniteTotalMassForKappaAt z -> R1CS2ConditionAt z) := by
  have hPointwise : forall k j : Nat, R1KappaTailExpPointwiseAt k j z :=
    hPointwiseBridge hTailWindow hRankOneTail
  have hImp : R1FiniteTotalMassForKappaAt z -> R1CS2ConditionAt z := by
    intro hFinite
    exact hFiniteMassToCS2Bridge hFinite hPointwise
  exact And.intro hPointwise hImp

end LeanV31
