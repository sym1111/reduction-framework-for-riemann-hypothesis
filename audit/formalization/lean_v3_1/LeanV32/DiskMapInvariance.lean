import Mathlib
import LeanV32.CanonicalStepDiskMap

namespace LeanV32

noncomputable section

open scoped ComplexConjugate

/-!
Paper v3.2: the explicit one-step map `Fval` sends the closed unit disk to itself.

This is proved by a direct inequality on the explicit PGL representative `diskMat`.
-/

-- This file contains a large symbolic expansion; give it a generous heartbeat budget.
set_option maxHeartbeats 6000000

-- Local helper: convert `‖x‖ ≤ 1` into `Complex.normSq x ≤ 1`.
private lemma normSq_le_one_of_norm_le_one (w : Complex) (hw : ‖w‖ ≤ 1) :
    Complex.normSq w ≤ 1 := by
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hw2 : ‖w‖ ^ 2 ≤ (1 : Real) ^ 2 := by nlinarith
  simpa [Complex.normSq_eq_norm_sq] using hw2

-- Local helper: convert `‖x‖ < 1` into `Complex.normSq x < 1`.
private lemma normSq_lt_one_of_norm_lt_one (w : Complex) (hw : ‖w‖ < 1) :
    Complex.normSq w < 1 := by
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hw2 : ‖w‖ ^ 2 < (1 : Real) ^ 2 := by nlinarith
  simpa [Complex.normSq_eq_norm_sq] using hw2

/-!
Key algebraic identity (already cross-checked numerically): for the explicit matrix `diskMat alpha z`,
the quantity `‖den‖^2 - ‖num‖^2` factors into a sum of manifestly nonnegative terms once multiplied
by `(‖alpha‖^2 + 1) = (Complex.normSq alpha + 1)`.

We keep the result in terms of `Complex.normSq` to avoid square roots.
-/
private lemma diskMat_normSq_den_sub_normSq_num_mul (alpha z w : Complex) :
    (Complex.normSq alpha + 1) *
        (Complex.normSq (den (diskMat alpha z) w) - Complex.normSq (num (diskMat alpha z) w)) =
      4 * z.im * (1 - Complex.normSq alpha) *
          ((w.re * (Complex.normSq alpha + 1) + (1 - Complex.normSq alpha)) ^ 2 +
            (w.im * (Complex.normSq alpha + 1) + 2 * alpha.re) ^ 2 +
            4 * alpha.im ^ 2) +
        4 * (Complex.normSq alpha + 1) * (1 - Complex.normSq w) *
          ((Complex.normSq alpha - 1) ^ 2 + alpha.im ^ 2 * Complex.normSq z) := by
  -- Expand both sides to a polynomial identity in `re/im` coordinates and close with `ring_nf`.
  -- `simp` handles all `re/im` projections of complex arithmetic, and reduces
  -- `alpha + conj alpha` / `alpha * conj alpha` to real expressions.
  simp [Complex.normSq_apply, num, den, diskMat, Complex.mul_conj, Complex.add_conj, pow_two]
  ring_nf

-- The explicit `diskMat` map is a disk self-map for `z ∈ UHP` and `‖α‖ < 1`.
--
-- We keep the proof purely algebraic: show `‖num‖ ≤ ‖den‖`, hence `‖num/den‖ ≤ 1`.
lemma diskMat_mobius_norm_le_one (alpha z w : Complex)
    (hz : 0 < z.im) (hα : ‖alpha‖ < 1) (hw : ‖w‖ ≤ 1) :
    ‖mobius (diskMat alpha z) w‖ ≤ 1 := by
  classical

  -- Reduce to a comparison of squared norms (no square roots).
  let A : Mat2 := diskMat alpha z

  have hs_lt_one : Complex.normSq alpha < 1 := normSq_lt_one_of_norm_lt_one alpha hα
  have hs1_pos : 0 < Complex.normSq alpha + 1 := by
    have : 0 ≤ Complex.normSq alpha := Complex.normSq_nonneg alpha
    linarith

  have hw_le_one : Complex.normSq w ≤ 1 := normSq_le_one_of_norm_le_one w hw

  -- Main inequality: `Complex.normSq (num A w) ≤ Complex.normSq (den A w)`.
  have h_numSq_le_denSq : Complex.normSq (num A w) ≤ Complex.normSq (den A w) := by
    have hz0 : 0 ≤ z.im := le_of_lt hz
    have hs0 : 0 ≤ 1 - Complex.normSq alpha := sub_nonneg.2 (le_of_lt hs_lt_one)
    have hw0 : 0 ≤ 1 - Complex.normSq w := sub_nonneg.2 hw_le_one

    have hS :
        0 ≤
          (w.re * (Complex.normSq alpha + 1) + (1 - Complex.normSq alpha)) ^ 2 +
            (w.im * (Complex.normSq alpha + 1) + 2 * alpha.re) ^ 2 +
              4 * alpha.im ^ 2 := by
      have h1 : 0 ≤ (w.re * (Complex.normSq alpha + 1) + (1 - Complex.normSq alpha)) ^ 2 :=
        sq_nonneg _
      have h2 : 0 ≤ (w.im * (Complex.normSq alpha + 1) + 2 * alpha.re) ^ 2 :=
        sq_nonneg _
      have h3 : 0 ≤ 4 * alpha.im ^ 2 := by
        have : 0 ≤ (4 : Real) := by norm_num
        exact mul_nonneg this (sq_nonneg _)
      linarith

    have hK :
        0 ≤ (Complex.normSq alpha - 1) ^ 2 + alpha.im ^ 2 * Complex.normSq z := by
      have h1 : 0 ≤ (Complex.normSq alpha - 1) ^ 2 := sq_nonneg _
      have h2 : 0 ≤ alpha.im ^ 2 * Complex.normSq z := by
        exact mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg z)
      linarith

    have hterm1 :
        0 ≤
          4 * z.im * (1 - Complex.normSq alpha) *
            ((w.re * (Complex.normSq alpha + 1) + (1 - Complex.normSq alpha)) ^ 2 +
              (w.im * (Complex.normSq alpha + 1) + 2 * alpha.re) ^ 2 +
                4 * alpha.im ^ 2) := by
      have h4 : 0 ≤ (4 : Real) := by norm_num
      have : 0 ≤ 4 * z.im := mul_nonneg h4 hz0
      have : 0 ≤ 4 * z.im * (1 - Complex.normSq alpha) := mul_nonneg this hs0
      exact mul_nonneg this hS

    have hterm2 :
        0 ≤
          4 * (Complex.normSq alpha + 1) * (1 - Complex.normSq w) *
            ((Complex.normSq alpha - 1) ^ 2 + alpha.im ^ 2 * Complex.normSq z) := by
      have h4 : 0 ≤ (4 : Real) := by norm_num
      have hs1 : 0 ≤ Complex.normSq alpha + 1 := by
        have : 0 ≤ Complex.normSq alpha := Complex.normSq_nonneg alpha
        linarith
      have : 0 ≤ 4 * (Complex.normSq alpha + 1) := mul_nonneg h4 hs1
      have : 0 ≤ 4 * (Complex.normSq alpha + 1) * (1 - Complex.normSq w) := mul_nonneg this hw0
      exact mul_nonneg this hK

    have hprod :
        0 ≤
          (Complex.normSq alpha + 1) *
            (Complex.normSq (den A w) - Complex.normSq (num A w)) := by
      -- Rewrite to the explicit RHS and use nonnegativity of both terms.
      simpa [A, diskMat_normSq_den_sub_normSq_num_mul alpha z w] using add_nonneg hterm1 hterm2

    have hdiff :
        0 ≤ Complex.normSq (den A w) - Complex.normSq (num A w) := by
      have hprod' :
          0 ≤
            (Complex.normSq (den A w) - Complex.normSq (num A w)) *
              (Complex.normSq alpha + 1) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
      exact nonneg_of_mul_nonneg_left hprod' hs1_pos

    linarith

  have h_num_le_den : ‖num A w‖ ≤ ‖den A w‖ := by
    have hn0 : 0 ≤ ‖num A w‖ := norm_nonneg _
    have hd0 : 0 ≤ ‖den A w‖ := norm_nonneg _
    have hsq : ‖num A w‖ ^ 2 ≤ ‖den A w‖ ^ 2 := by
      simpa [Complex.normSq_eq_norm_sq] using h_numSq_le_denSq
    exact (sq_le_sq₀ hn0 hd0).1 hsq

  -- Conclude from `‖num‖ ≤ ‖den‖`.
  have hden0 : 0 ≤ ‖den A w‖ := norm_nonneg _
  calc
    ‖mobius A w‖ = ‖num A w / den A w‖ := by simp [mobius, num, den]
    _ = ‖num A w‖ / ‖den A w‖ := by simp
    _ ≤ 1 := div_le_one_of_le₀ h_num_le_den hden0

-- Strict version: interior points are mapped to interior points (still purely algebraic).
lemma diskMat_mobius_norm_lt_one (alpha z w : Complex)
    (hz : 0 < z.im) (hα : ‖alpha‖ < 1) (hw : ‖w‖ < 1) :
    ‖mobius (diskMat alpha z) w‖ < 1 := by
  classical

  -- Reduce to a comparison of squared norms (no square roots).
  let A : Mat2 := diskMat alpha z

  have hs_lt_one : Complex.normSq alpha < 1 := normSq_lt_one_of_norm_lt_one alpha hα
  have hs1_pos : 0 < Complex.normSq alpha + 1 := by
    have : 0 ≤ Complex.normSq alpha := Complex.normSq_nonneg alpha
    linarith

  have hw_lt_one : Complex.normSq w < 1 := normSq_lt_one_of_norm_lt_one w hw

  -- Main strict inequality: `Complex.normSq (num A w) < Complex.normSq (den A w)`.
  have h_numSq_lt_denSq : Complex.normSq (num A w) < Complex.normSq (den A w) := by
    have hz0 : 0 ≤ z.im := le_of_lt hz
    have hs0 : 0 ≤ 1 - Complex.normSq alpha := sub_nonneg.2 (le_of_lt hs_lt_one)
    have hw0 : 0 < 1 - Complex.normSq w := sub_pos.2 hw_lt_one

    have hS :
        0 ≤
          (w.re * (Complex.normSq alpha + 1) + (1 - Complex.normSq alpha)) ^ 2 +
            (w.im * (Complex.normSq alpha + 1) + 2 * alpha.re) ^ 2 +
              4 * alpha.im ^ 2 := by
      have h1 : 0 ≤ (w.re * (Complex.normSq alpha + 1) + (1 - Complex.normSq alpha)) ^ 2 :=
        sq_nonneg _
      have h2 : 0 ≤ (w.im * (Complex.normSq alpha + 1) + 2 * alpha.re) ^ 2 :=
        sq_nonneg _
      have h3 : 0 ≤ 4 * alpha.im ^ 2 := by
        have : 0 ≤ (4 : Real) := by norm_num
        exact mul_nonneg this (sq_nonneg _)
      linarith

    have hK_pos :
        0 < (Complex.normSq alpha - 1) ^ 2 + alpha.im ^ 2 * Complex.normSq z := by
      have hαlt : Complex.normSq alpha - 1 < 0 := by linarith
      have h1 : 0 < (Complex.normSq alpha - 1) ^ 2 := sq_pos_of_ne_zero (ne_of_lt hαlt)
      have h2 : 0 ≤ alpha.im ^ 2 * Complex.normSq z := by
        exact mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg z)
      exact add_pos_of_pos_of_nonneg h1 h2

    have hterm1 :
        0 ≤
          4 * z.im * (1 - Complex.normSq alpha) *
            ((w.re * (Complex.normSq alpha + 1) + (1 - Complex.normSq alpha)) ^ 2 +
              (w.im * (Complex.normSq alpha + 1) + 2 * alpha.re) ^ 2 +
                4 * alpha.im ^ 2) := by
      have h4 : 0 ≤ (4 : Real) := by norm_num
      have : 0 ≤ 4 * z.im := mul_nonneg h4 hz0
      have : 0 ≤ 4 * z.im * (1 - Complex.normSq alpha) := mul_nonneg this hs0
      exact mul_nonneg this hS

    have hterm2 :
        0 <
          4 * (Complex.normSq alpha + 1) * (1 - Complex.normSq w) *
            ((Complex.normSq alpha - 1) ^ 2 + alpha.im ^ 2 * Complex.normSq z) := by
      have h4 : 0 < (4 : Real) := by norm_num
      have hA : 0 < 4 * (Complex.normSq alpha + 1) := mul_pos h4 hs1_pos
      have hB : 0 < 4 * (Complex.normSq alpha + 1) * (1 - Complex.normSq w) := mul_pos hA hw0
      exact mul_pos hB hK_pos

    have hprod :
        0 <
          (Complex.normSq alpha + 1) *
            (Complex.normSq (den A w) - Complex.normSq (num A w)) := by
      -- Rewrite to the explicit RHS and use `term2 > 0`.
      simpa [A, diskMat_normSq_den_sub_normSq_num_mul alpha z w] using
        add_pos_of_nonneg_of_pos hterm1 hterm2

    have hdiff_pos :
        0 < Complex.normSq (den A w) - Complex.normSq (num A w) := by
      have hprod' :
          0 <
            (Complex.normSq (den A w) - Complex.normSq (num A w)) *
              (Complex.normSq alpha + 1) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
      exact pos_of_mul_pos_left hprod' (le_of_lt hs1_pos)

    exact lt_of_sub_pos hdiff_pos

  have h_num_lt_den : ‖num A w‖ < ‖den A w‖ := by
    have hn0 : 0 ≤ ‖num A w‖ := norm_nonneg _
    have hd0 : 0 ≤ ‖den A w‖ := norm_nonneg _
    have hsq : ‖num A w‖ ^ 2 < ‖den A w‖ ^ 2 := by
      simpa [Complex.normSq_eq_norm_sq] using h_numSq_lt_denSq
    have habs : |‖num A w‖| < |‖den A w‖| := (sq_lt_sq).1 hsq
    simpa [abs_of_nonneg hn0, abs_of_nonneg hd0] using habs

  have hden_pos : 0 < ‖den A w‖ := lt_of_le_of_lt (norm_nonneg _) h_num_lt_den

  -- Conclude from `‖num‖ < ‖den‖`.
  calc
    ‖mobius A w‖ = ‖num A w / den A w‖ := by simp [mobius, num, den]
    _ = ‖num A w‖ / ‖den A w‖ := by simp
    _ < 1 := (div_lt_one hden_pos).2 h_num_lt_den

end

end LeanV32
