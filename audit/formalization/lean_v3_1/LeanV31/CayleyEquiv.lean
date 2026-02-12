import LeanV31.MeasureIdentity

namespace LeanV31

noncomputable def cayleyOf (H : Complex -> Complex) : Complex -> Complex :=
  fun z => (1 + Complex.I * H z) / (1 - Complex.I * H z)

/- S016 wrapper:
pointwise Cayley equivalence on `cUpper` lifts to the global quantified form,
including the strict-inequality version. -/
theorem cayley_equiv
    {H W : Complex -> Complex}
    (hW : W = cayleyOf H)
    (hPointwise :
      forall z, z ∈ cUpper -> (0 <= Complex.im (H z) <-> ‖W z‖ <= 1))
    (hPointwiseStrict :
      forall z, z ∈ cUpper -> (0 < Complex.im (H z) <-> ‖W z‖ < 1)) :
    ((forall z, z ∈ cUpper -> 0 <= Complex.im (H z)) <->
      (forall z, z ∈ cUpper -> ‖W z‖ <= 1)) /\
    ((forall z, z ∈ cUpper -> 0 < Complex.im (H z)) <->
      (forall z, z ∈ cUpper -> ‖W z‖ < 1)) := by
  subst hW
  constructor
  · constructor
    · intro hNonneg z hz
      exact (hPointwise z hz).1 (hNonneg z hz)
    · intro hSchur z hz
      exact (hPointwise z hz).2 (hSchur z hz)
  · constructor
    · intro hPos z hz
      exact (hPointwiseStrict z hz).1 (hPos z hz)
    · intro hStrict z hz
      exact (hPointwiseStrict z hz).2 (hStrict z hz)

end LeanV31
