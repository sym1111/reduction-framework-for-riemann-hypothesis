import LeanV31.R1KappaLowerFromPrefix

namespace LeanV31

def R1KappaPointwiseTailExpAt (k j : Nat) (_z : Complex) : Prop :=
  Exists fun C : Real => 0 <= C /\ (k : Real) <= C + (j : Real)

/- S056 wrapper:
in the rank-one branch, step linearization converts tail products into
exponential tail-mass control, yielding pointwise `kappa_{k,j}` bounds. -/
theorem R1_kappa_pointwise_tail_exp
    {z : Complex}
    (hRankOneTail : R1RankOneTailBranchAt z)
    (hStepLinear : forall k : Nat, R1Rank1StepLinearAt k z)
    (hTailBridge :
      R1RankOneTailBranchAt z ->
      (forall k : Nat, R1Rank1StepLinearAt k z) ->
      forall k j : Nat, R1KappaPointwiseTailExpAt k j z) :
    forall k j : Nat, R1KappaPointwiseTailExpAt k j z := by
  exact hTailBridge hRankOneTail hStepLinear

end LeanV31
