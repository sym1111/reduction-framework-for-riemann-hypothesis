import Mathlib

namespace LeanV31

open scoped ComplexConjugate

/- On `z ≠ 0`, the `dslope` Schur-step form matches the raw quotient form. -/
theorem schur_step_formula_nonzero
    {S : Complex -> Complex} {alpha z : Complex}
    (halpha : S 0 = alpha) (hz : z ≠ 0) :
    dslope S 0 z / (1 - conj alpha * S z) =
      (S z - alpha) / (z * (1 - conj alpha * S z)) := by
  rw [dslope_of_ne _ hz]
  have hslope : slope S 0 z = (S z - alpha) / z := by
    simp [slope_def_field, halpha]
  rw [hslope]
  field_simp [hz]

/- S145 core:
if `S` is analytic at `0` and `1 - conj(alpha)*alpha ≠ 0`,
then the Schur-step expression is analytic at `0` and its value at `0`
is the exact one-line update formula. -/
theorem alpha_k1_exact
    {S : Complex -> Complex} {alpha : Complex}
    (halpha : S 0 = alpha)
    (hS : AnalyticAt Complex S 0)
    (hrho : (1 - conj alpha * alpha) ≠ 0) :
    AnalyticAt Complex (fun z => dslope S 0 z / (1 - conj alpha * S z)) 0 ∧
      (dslope S 0 0 / (1 - conj alpha * S 0) = deriv S 0 / (1 - conj alpha * alpha)) := by
  have hds : AnalyticAt Complex (dslope S 0) 0 := by
    exact (hS.hasFPowerSeriesAt.has_fpower_series_dslope_fslope).analyticAt
  have hden : AnalyticAt Complex (fun z => 1 - conj alpha * S z) 0 := by
    simpa using (analyticAt_const.sub (analyticAt_const.mul hS))
  have hden0 : (1 - conj alpha * S 0) ≠ 0 := by
    simpa [halpha] using hrho
  refine ⟨hds.div hden hden0, ?_⟩
  simp [dslope_same, halpha]

/- S146 core in coefficient form:
for a local power-series model at 0, the derivative update formula follows from
`dslope` coefficient shift plus quotient differentiation. -/
  theorem bk1_exact_coeff
    {S : Complex -> Complex}
    {p : FormalMultilinearSeries Complex Complex Complex}
    {alpha : Complex}
    (hp : HasFPowerSeriesAt S p 0)
    (halpha : p.coeff 0 = alpha)
    (hrho : (1 - conj alpha * alpha) ≠ 0) :
    deriv (fun z => dslope S 0 z / (1 - conj alpha * S z)) 0 =
      p.coeff 2 / (1 - conj alpha * alpha) +
        conj alpha * (p.coeff 1) ^ 2 / (1 - conj alpha * alpha) ^ 2 := by
  have hS' : HasDerivAt S (p.coeff 1) 0 := by
    exact hp.hasDerivAt
  have hNps : HasFPowerSeriesAt (dslope S 0) p.fslope 0 := hp.has_fpower_series_dslope_fslope
  have hN' : HasDerivAt (dslope S 0) (p.coeff 2) 0 := by
    have hNraw : HasDerivAt (dslope S 0) (p.fslope.coeff 1) 0 := by
      exact hNps.hasDerivAt
    simpa [FormalMultilinearSeries.coeff_fslope] using hNraw
  have hConstConj : HasDerivAt (fun z : Complex => conj alpha) 0 0 := by
    simpa using (hasDerivAt_const (x := (0 : Complex)) (c := conj alpha))
  have hMul : HasDerivAt (fun z => conj alpha * S z) (conj alpha * p.coeff 1) 0 := by
    simpa using hConstConj.mul hS'
  have hConstOne : HasDerivAt (fun z : Complex => (1 : Complex)) 0 0 := by
    simpa using (hasDerivAt_const (x := (0 : Complex)) (c := (1 : Complex)))
  have hD' : HasDerivAt (fun z => 1 - conj alpha * S z) (-(conj alpha * p.coeff 1)) 0 := by
    simpa using hConstOne.sub hMul
  have hden0 : (1 - conj alpha * S 0) ≠ 0 := by
    have hS0p : p.coeff 0 = S 0 := hp.coeff_zero 1
    have hS0 : S 0 = p.coeff 0 := hS0p.symm
    calc
      1 - conj alpha * S 0 = 1 - conj alpha * p.coeff 0 := by simp [hS0]
      _ = 1 - conj alpha * alpha := by simp [halpha]
      _ ≠ 0 := hrho
  have hQ : HasDerivAt (fun z => dslope S 0 z / (1 - conj alpha * S z))
      ((p.coeff 2 * (1 - conj alpha * S 0) - dslope S 0 0 * (-(conj alpha * p.coeff 1))) /
        (1 - conj alpha * S 0) ^ 2) 0 := by
    exact hN'.div hD' hden0
  have hmain :
      deriv (fun z => dslope S 0 z / (1 - conj alpha * S z)) 0 =
        ((p.coeff 2 * (1 - conj alpha * S 0) - dslope S 0 0 * (-(conj alpha * p.coeff 1))) /
          (1 - conj alpha * S 0) ^ 2) := hQ.deriv
  rw [dslope_same, hS'.deriv] at hmain
  have hS0 : S 0 = alpha := by
    have hS0p : p.coeff 0 = S 0 := hp.coeff_zero 1
    have hS0q : S 0 = p.coeff 0 := hS0p.symm
    simpa [halpha] using hS0q
  rw [hS0] at hmain
  have hsimp :
      ((p.coeff 2 * (1 - conj alpha * alpha) - p.coeff 1 * (-(conj alpha * p.coeff 1))) /
        (1 - conj alpha * alpha) ^ 2) =
        p.coeff 2 / (1 - conj alpha * alpha) +
          conj alpha * (p.coeff 1) ^ 2 / (1 - conj alpha * alpha) ^ 2 := by
    field_simp [hrho]
    ring
  exact hmain.trans hsimp

end LeanV31
