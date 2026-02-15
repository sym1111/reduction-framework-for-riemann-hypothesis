import Mathlib

namespace LeanV32

noncomputable section

/-!
Paper v3.2: Schur-parameter rank-one Hamiltonian blocks.

TeX labels:
- `eq:R1_H_alpha_def`
- `eq:R1_u_tau_alpha`
-/

open scoped ComplexConjugate

abbrev Mat2 := Matrix (Fin 2) (Fin 2) Complex

def J : Mat2 :=
  !![(0 : Complex), (-1 : Complex); (1 : Complex), (0 : Complex)]

-- Paper notation: H(alpha) = 1/(1-|alpha|^2) * [[1, -alpha], [-conj(alpha), |alpha|^2]].
def denomAlpha (alpha : Complex) : Complex :=
  (1 : Complex) - alpha * conj alpha

def Halpha (alpha : Complex) : Mat2 :=
  ((1 : Complex) / denomAlpha alpha) •
    !![(1 : Complex), (-alpha); (-conj alpha), alpha * conj alpha]

-- Paper normalization: u(alpha) = (1, -conj(alpha)) / sqrt(1+|alpha|^2).
def uVec (alpha : Complex) : (Fin 2 → Complex) :=
  fun i =>
    match i with
    | 0 => (1 : Complex) / Real.sqrt (1 + Complex.normSq alpha)
    | 1 => (-conj alpha : Complex) / Real.sqrt (1 + Complex.normSq alpha)

-- Paper scalar: tau(alpha) = tr(H(alpha)) = (1+|alpha|^2)/(1-|alpha|^2).
def tau (alpha : Complex) : Real :=
  (1 + Complex.normSq alpha) / (1 - Complex.normSq alpha)

lemma denomAlpha_ne_zero_of_norm_lt_one (alpha : Complex) (hα : ‖alpha‖ < 1) :
    denomAlpha alpha ≠ 0 := by
  unfold denomAlpha
  have h0 : 0 ≤ ‖alpha‖ := norm_nonneg alpha
  have hsq : ‖alpha‖ ^ 2 < (1 : Real) ^ 2 := by nlinarith
  have hnormSq_lt : Complex.normSq alpha < 1 := by
    simpa [Complex.normSq_eq_norm_sq] using hsq
  have hpos : 0 < (1 : Real) - Complex.normSq alpha := by linarith
  have hmul : alpha * conj alpha = (Complex.normSq alpha : Complex) := by
    simpa using (Complex.mul_conj alpha)
  intro hden
  have hre : ((1 : Complex) - alpha * conj alpha).re = 0 := by
    simpa using congrArg Complex.re hden
  have hreal : (1 : Real) - Complex.normSq alpha = 0 := by
    simpa [hmul] using hre
  exact (ne_of_gt hpos) hreal

lemma one_le_tau (alpha : Complex) (hα : ‖alpha‖ < 1) : 1 ≤ tau alpha := by
  have h0 : 0 ≤ ‖alpha‖ := norm_nonneg alpha
  have hsq : ‖alpha‖ ^ 2 < (1 : Real) ^ 2 := by nlinarith
  have hnormSq_lt : Complex.normSq alpha < 1 := by
    simpa [Complex.normSq_eq_norm_sq] using hsq
  have hden_pos : 0 < 1 - Complex.normSq alpha := by linarith
  have hden_le_num : 1 - Complex.normSq alpha ≤ 1 + Complex.normSq alpha := by linarith [Complex.normSq_nonneg alpha]
  have h : 1 ≤ (1 + Complex.normSq alpha) / (1 - Complex.normSq alpha) :=
    (one_le_div hden_pos).2 hden_le_num
  simpa [tau] using h

end

end LeanV32
