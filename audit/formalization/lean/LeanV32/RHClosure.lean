import LeanV32.RHBasic
import LeanV32.XiModelPaper
import LeanV32.MathlibRHBridge

namespace LeanV32

noncomputable section

/-!
Clean closure endpoints:

1. `ZeroFreeOnUpper XiModel` + `ConjugationSymmetric XiModel` ⇒
   `RiemannHypothesis XiModel` (all zeros real in the `z`-variable).

2. `ZeroFreeOnUpper XiModel` + even symmetry `XiModel(-z)=XiModel(z)` ⇒
   `RiemannHypothesis XiModel` (this is the functional-equation route).

3. Combine with `mathlib_rh_of_xi_model_rh` to obtain Mathlib's RH statement.

These lemmas make the final logical dependencies explicit and auditable.
-/

theorem xi_model_rh_of_zero_free_and_conj_symm
    (hZeroFree : ZeroFreeOnUpper XiModel)
    (hConjSymm : ConjugationSymmetric XiModel) :
    RiemannHypothesis XiModel := by
  refine rh_from_lstar_core (f := XiModel) hZeroFree ?_
  exact conj_zero_of_conjugation_symmetric (f := XiModel) hConjSymm

theorem mathlib_rh_of_xi_model_zero_free_and_conj_symm
    (hZeroFree : ZeroFreeOnUpper XiModel)
    (hConjSymm : ConjugationSymmetric XiModel) :
    MathlibRiemannHypothesis := by
  have hXiRH : RiemannHypothesis XiModel :=
    xi_model_rh_of_zero_free_and_conj_symm hZeroFree hConjSymm
  exact mathlib_rh_of_xi_model_rh hXiRH

theorem xi_model_rh_of_zero_free
    (hZeroFree : ZeroFreeOnUpper XiModel) :
    RiemannHypothesis XiModel := by
  refine rh_from_lstar_core_via_even (f := XiModel) hZeroFree ?_
  exact xi_model_neg

theorem mathlib_rh_of_xi_model_zero_free
    (hZeroFree : ZeroFreeOnUpper XiModel) :
    MathlibRiemannHypothesis := by
  have hXiRH : RiemannHypothesis XiModel :=
    xi_model_rh_of_zero_free hZeroFree
  exact mathlib_rh_of_xi_model_rh hXiRH

end

end LeanV32
