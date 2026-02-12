import LeanV31.XiModelPaper
import LeanV31.FinalBridgeClosed

namespace LeanV31

abbrev MathlibRiemannHypothesis : Prop := _root_.RiemannHypothesis

/- Bridge theorem:
if the xi-model zero statement is closed in LeanV31, then the Mathlib RH
statement follows (same nontrivial-zero target line Re(s)=1/2). -/
theorem mathlib_rh_of_xi_model_rh
    (hXiRH : RiemannHypothesis XiModel) :
    MathlibRiemannHypothesis := by
  intro s hs _hsTrivial _hsOne
  have hzZero : XiModel (-Complex.I * (s - (1 / 2 : Complex))) = 0 :=
    xi_model_zero_of_riemann_zeta_zero s hs
  have hzIm : (-Complex.I * (s - (1 / 2 : Complex))).im = 0 :=
    hXiRH _ hzZero
  have hzImExpr :
      (-Complex.I * (s - (1 / 2 : Complex))).im = -(s.re - (1 / 2 : Real)) :=
    im_negI_center s
  linarith [hzIm, hzImExpr]

theorem final_bridge_closed_xi
    (hZeroFree : ZeroFreeOnUpper XiModel)
    (hConjSymm : ConjugationSymmetric XiModel) :
    RiemannHypothesis XiModel := by
  exact final_bridge_closed (f := XiModel) hZeroFree hConjSymm

theorem final_bridge_closed_xi_via_certificate
    (hCertificate : CircleHardyZeroFreeCertificate XiModel XiModelLogDerivative)
    (hConjSymm : ConjugationSymmetric XiModel) :
    RiemannHypothesis XiModel := by
  exact final_bridge_closed_via_certificate hCertificate hConjSymm

theorem final_bridge_closed_xi_via_completed_conjugation
    (hZeroFree : ZeroFreeOnUpper XiModel)
    (hConjSymm : ConjugationSymmetric XiModel) :
    RiemannHypothesis XiModel := by
  exact final_bridge_closed_xi hZeroFree hConjSymm

theorem mathlib_rh_from_final_bridge_closed_xi_via_completed_conjugation
    (hZeroFree : ZeroFreeOnUpper XiModel)
    (hConjSymm : ConjugationSymmetric XiModel) :
    MathlibRiemannHypothesis := by
  have hXiRH : RiemannHypothesis XiModel :=
    final_bridge_closed_xi_via_completed_conjugation
      hZeroFree hConjSymm
  exact mathlib_rh_of_xi_model_rh hXiRH

theorem final_bridge_closed_xi_via_mathlib_completed_symmetry
    (hZeroFree : ZeroFreeOnUpper XiModel)
    (hConjSymm : ConjugationSymmetric XiModel) :
    RiemannHypothesis XiModel := by
  exact final_bridge_closed_xi hZeroFree hConjSymm

theorem mathlib_rh_from_final_bridge_closed_xi_via_mathlib_completed_symmetry
    (hZeroFree : ZeroFreeOnUpper XiModel)
    (hConjSymm : ConjugationSymmetric XiModel) :
    MathlibRiemannHypothesis := by
  have hXiRH : RiemannHypothesis XiModel :=
    final_bridge_closed_xi_via_mathlib_completed_symmetry
      hZeroFree hConjSymm
  exact mathlib_rh_of_xi_model_rh hXiRH

theorem final_bridge_closed_xi_via_certificate_mathlib_completed_symmetry
    (hCertificate : CircleHardyZeroFreeCertificate XiModel XiModelLogDerivative)
    (hConjSymm : ConjugationSymmetric XiModel) :
    RiemannHypothesis XiModel := by
  exact final_bridge_closed_xi_via_certificate hCertificate hConjSymm

theorem mathlib_rh_from_certificate_mathlib_completed_symmetry
    (hCertificate : CircleHardyZeroFreeCertificate XiModel XiModelLogDerivative)
    (hConjSymm : ConjugationSymmetric XiModel) :
    MathlibRiemannHypothesis := by
  have hXiRH : RiemannHypothesis XiModel :=
    final_bridge_closed_xi_via_certificate_mathlib_completed_symmetry
      hCertificate hConjSymm
  exact mathlib_rh_of_xi_model_rh hXiRH

theorem mathlib_rh_from_final_bridge_closed_xi
    (hZeroFree : ZeroFreeOnUpper XiModel)
    (hConjSymm : ConjugationSymmetric XiModel) :
    MathlibRiemannHypothesis := by
  have hXiRH : RiemannHypothesis XiModel :=
    final_bridge_closed_xi hZeroFree hConjSymm
  exact mathlib_rh_of_xi_model_rh hXiRH

theorem mathlib_rh_from_final_bridge_closed_xi_via_certificate
    (hCertificate : CircleHardyZeroFreeCertificate XiModel XiModelLogDerivative)
    (hConjSymm : ConjugationSymmetric XiModel) :
    MathlibRiemannHypothesis := by
  have hXiRH : RiemannHypothesis XiModel :=
    final_bridge_closed_xi_via_certificate hCertificate hConjSymm
  exact mathlib_rh_of_xi_model_rh hXiRH

end LeanV31
