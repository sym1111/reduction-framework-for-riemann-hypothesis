import LeanV32.TruncatedDiskCocycle

namespace LeanV32

noncomputable section

/-!
Paper v3.2 (Lean v3.2 track): the **single upstream bridge hypothesis** for the
denominator-separation bottleneck.

The algebraic v3.2 pipeline reduces uniform denominator separation to a uniform
bound `‖alpha_k‖ ≤ r0 < 1` on the Schur parameters. This file packages that
hypothesis in a clean, auditable form and exposes the downstream consequence:
`DenomSepCocycleAt z alphaSeq`.
-/

/-- Uniform Schur-radius bound: `∃ r0 < 1, ∀k, ‖alpha_k‖ ≤ r0`. -/
def AlphaRadiusBound (alphaSeq : Nat → Complex) : Prop :=
  ∃ r0 : Real, 0 ≤ r0 ∧ r0 < 1 ∧ ∀ k : Nat, ‖alphaSeq k‖ ≤ r0

theorem alphaRadiusBound_norm_lt_one {alphaSeq : Nat → Complex} (h : AlphaRadiusBound alphaSeq) :
    ∀ k : Nat, ‖alphaSeq k‖ < 1 := by
  rcases h with ⟨r0, hr0_nonneg, hr0_lt_one, hbound⟩
  intro k
  exact lt_of_le_of_lt (hbound k) hr0_lt_one

/-- Main consequence of the bridge hypothesis: the truncated disk cocycle satisfies uniform
denominator separation at every `z ∈ UHP`. -/
theorem denomSepCocycleAt_of_alphaRadiusBound
    (z : Complex) (alphaSeq : Nat → Complex)
    (hz : 0 < z.im)
    (hα : AlphaRadiusBound alphaSeq) :
    DenomSepCocycleAt z alphaSeq := by
  rcases hα with ⟨r0, hr0_nonneg, hr0_lt_one, hbound⟩
  exact
    denomSepCocycleAt_of_alpha_bound
      (z := z)
      (alphaSeq := alphaSeq)
      (r0 := r0)
      hz
      hr0_nonneg
      hr0_lt_one
      hbound

end

end LeanV32
