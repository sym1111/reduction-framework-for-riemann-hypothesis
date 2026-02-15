import Mathlib.NumberTheory.LSeries.RiemannZeta
import LeanV32.RHBasic
import LeanV32.XiModelPaper

namespace LeanV32

noncomputable section

/-!
Bridge to Mathlib's `RiemannHypothesis` statement.

Mathlib defines (see `Mathlib/NumberTheory/LSeries/RiemannZeta.lean`):
`_root_.RiemannHypothesis : Prop := ∀ s, ζ(s)=0 → ... → s.re = 1/2`.

The paper uses an xi-model `XiModel : ℂ → ℂ` in the variable `z` where
`s = 1/2 + i z`. A zero statement for `XiModel` (all zeros have `Im(z)=0`)
implies Mathlib's RH by the change-of-variables `z = -i (s - 1/2)`.
-/

abbrev MathlibRiemannHypothesis : Prop :=
  _root_.RiemannHypothesis

theorem mathlib_rh_of_xi_model_rh
    (hXiRH : RiemannHypothesis XiModel) :
    MathlibRiemannHypothesis := by
  intro s hs _hsTrivial _hsOne
  have hzZero : XiModel (-Complex.I * (s - (1 / 2 : Complex))) = 0 :=
    xi_model_zero_of_riemann_zeta_zero s hs _hsTrivial
  have hzIm : (-Complex.I * (s - (1 / 2 : Complex))).im = 0 :=
    hXiRH _ hzZero
  have hzImExpr :
      (-Complex.I * (s - (1 / 2 : Complex))).im = -(s.re - (1 / 2 : Real)) :=
    im_negI_center s
  linarith [hzIm, hzImExpr]

end

end LeanV32
