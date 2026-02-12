import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace LeanV31

/- Paper map (`A_Reduction_Framework_RH_v3.1.tex`, lines ~58, ~81, ~5003):
`f(z) = xi(1/2 + i z)` and
`xi(s) = (1/2) * s * (s - 1) * pi^(-s/2) * Gamma(s/2) * zeta(s). -/
noncomputable def xiInput (z : Complex) : Complex :=
  (1 / 2 : Complex) + Complex.I * z

noncomputable def xiCompletedFromZeta (s : Complex) : Complex :=
  (1 / 2 : Complex) * s * (s - 1) *
    (Real.pi : Complex) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s

noncomputable def XiModel (z : Complex) : Complex :=
  xiCompletedFromZeta (xiInput z)

noncomputable def XiModelLogDerivative (z : Complex) : Complex :=
  -(deriv XiModel z) / XiModel z

theorem xi_model_formula :
    XiModel = fun z : Complex =>
      (1 / 2 : Complex) * (xiInput z) * (xiInput z - 1) *
        (Real.pi : Complex) ^ (-(xiInput z) / 2) *
        Complex.Gamma ((xiInput z) / 2) *
        riemannZeta (xiInput z) := by
  rfl

theorem xi_model_is_zeta_factorization :
    XiModel = fun z : Complex => xiCompletedFromZeta (xiInput z) := by
  rfl

lemma xi_input_star (z : Complex) :
    xiInput (star z) = 1 - star (xiInput z) := by
  unfold xiInput
  simp
  ring

lemma xi_input_neg (z : Complex) :
    xiInput (-z) = 1 - xiInput z := by
  unfold xiInput
  ring

theorem xi_model_neg_of_xi_completed_symmetry
    (hOneSub : forall s : Complex, xiCompletedFromZeta (1 - s) = xiCompletedFromZeta s) :
    forall z : Complex, XiModel (-z) = XiModel z := by
  intro z
  unfold XiModel
  rw [xi_input_neg z, hOneSub (xiInput z)]

theorem xi_model_conjugation_symmetric_of_xi_completed_symmetry
    (hOneSub : forall s : Complex, xiCompletedFromZeta (1 - s) = xiCompletedFromZeta s)
    (hConj : forall s : Complex, xiCompletedFromZeta (star s) = star (xiCompletedFromZeta s)) :
    forall z : Complex, XiModel (star z) = star (XiModel z) := by
  intro z
  unfold XiModel
  rw [xi_input_star z, hOneSub (star (xiInput z)), hConj (xiInput z)]

lemma xi_input_negI_center (s : Complex) :
    xiInput (-Complex.I * (s - (1 / 2 : Complex))) = s := by
  unfold xiInput
  ring_nf
  have hI2 : (Complex.I : Complex) ^ 2 = -1 := by
    norm_num
  rw [hI2]
  ring_nf

lemma xi_model_zero_of_riemann_zeta_zero (s : Complex)
    (hs : riemannZeta s = 0) :
    XiModel (-Complex.I * (s - (1 / 2 : Complex))) = 0 := by
  unfold XiModel xiCompletedFromZeta
  rw [xi_input_negI_center s, hs]
  simp

lemma im_negI_center (s : Complex) :
    (-Complex.I * (s - (1 / 2 : Complex))).im = -(s.re - (1 / 2 : Real)) := by
  simp

end LeanV31
