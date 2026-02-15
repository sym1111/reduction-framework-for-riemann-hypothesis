import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace LeanV32

noncomputable section

/-!
Paper v3.2: the completed xi-factor built from Mathlib's `riemannZeta`.

TeX intent: set `f(z) = xi(1/2 + i z)` with
`xi(s) = (1/2) * s * (s-1) * π^(-s/2) * Γ(s/2) * ζ(s)`.

This file only records the algebraic change-of-variables facts needed to bridge
Mathlib's `RiemannHypothesis` (about `riemannZeta`) to the paper's xi-model zero
statement (about `XiModel : ℂ → ℂ`).
-/

def xiInput (z : Complex) : Complex :=
  (1 / 2 : Complex) + Complex.I * z

def xiCompletedFromZeta (s : Complex) : Complex :=
  (1 / 2 : Complex) * s * (s - 1) * completedRiemannZeta s

def XiModel (z : Complex) : Complex :=
  xiCompletedFromZeta (xiInput z)

def XiModelLogDerivative (z : Complex) : Complex :=
  -(deriv XiModel z) / XiModel z

theorem xi_model_formula :
    XiModel = fun z : Complex =>
      (1 / 2 : Complex) * (xiInput z) * (xiInput z - 1) *
        completedRiemannZeta (xiInput z) := by
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

theorem xi_completed_one_sub (s : Complex) :
    xiCompletedFromZeta (1 - s) = xiCompletedFromZeta s := by
  unfold xiCompletedFromZeta
  simp [completedRiemannZeta_one_sub]
  ring

theorem xi_model_neg (z : Complex) : XiModel (-z) = XiModel z := by
  unfold XiModel
  rw [xi_input_neg z, xi_completed_one_sub (xiInput z)]

theorem xi_model_neg_of_xi_completed_symmetry
    (hOneSub : ∀ s : Complex, xiCompletedFromZeta (1 - s) = xiCompletedFromZeta s) :
    ∀ z : Complex, XiModel (-z) = XiModel z := by
  intro z
  unfold XiModel
  rw [xi_input_neg z, hOneSub (xiInput z)]

theorem xi_model_conjugation_symmetric_of_xi_completed_symmetry
    (hOneSub : ∀ s : Complex, xiCompletedFromZeta (1 - s) = xiCompletedFromZeta s)
    (hConj : ∀ s : Complex, xiCompletedFromZeta (star s) = star (xiCompletedFromZeta s)) :
    ∀ z : Complex, XiModel (star z) = star (XiModel z) := by
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
    (hs : riemannZeta s = 0)
    (hsTrivial : ¬∃ n : ℕ, s = -2 * (n + 1)) :
    XiModel (-Complex.I * (s - (1 / 2 : Complex))) = 0 := by
  -- Reduce to `completedRiemannZeta s = 0` using `riemannZeta = completedRiemannZeta / Gammaℝ`.
  have hs0 : s ≠ 0 := by
    intro hs0
    have h0 : riemannZeta 0 = 0 := by simpa [hs0] using hs
    -- `ζ(0) = -1/2`, so it cannot be zero.
    simp [riemannZeta_zero] at h0
  have hGamma : Complex.Gammaℝ s ≠ 0 := by
    intro hGamma0
    rcases (Complex.Gammaℝ_eq_zero_iff).1 hGamma0 with ⟨n, hn⟩
    cases n with
    | zero =>
        -- `s = 0` contradicts `hs`.
        exact hs0 (by simp [hn])
    | succ n =>
        -- `s = -2*(n+1)` contradicts `hsTrivial`.
        have : ∃ m : ℕ, s = -2 * (m + 1) := by
          refine ⟨n, ?_⟩
          -- Unpack `hn : s = -(2 * (Nat.succ n))` into the exact shape.
          -- Note: `Nat.succ n = n + 1`.
          calc
            s = -(2 * (Nat.succ n)) := hn
            _ = -(2 * (n + 1)) := by simp [Nat.succ_eq_add_one]
            _ = -2 * (n + 1) := by ring
        exact hsTrivial this
  have hdiv : completedRiemannZeta s / Complex.Gammaℝ s = 0 := by
    simpa [riemannZeta_def_of_ne_zero hs0] using hs
  have hmul := congrArg (fun t => t * Complex.Gammaℝ s) hdiv
  have hcompleted : completedRiemannZeta s = 0 := by
    -- `(a / b) * b = a` for `b ≠ 0`.
    simpa [div_eq_mul_inv, mul_assoc, hGamma] using hmul
  unfold XiModel xiCompletedFromZeta
  rw [xi_input_negI_center s, hcompleted]
  simp

lemma im_negI_center (s : Complex) :
    (-Complex.I * (s - (1 / 2 : Complex))).im = -(s.re - (1 / 2 : Real)) := by
  simp

end

end LeanV32
