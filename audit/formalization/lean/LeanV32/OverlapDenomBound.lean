import Mathlib
import LeanV32.CanonicalStepDiskMap

namespace LeanV32

noncomputable section

/-!
Paper v3.2: denominator separation bottleneck for the explicit disk-map matrix.

TeX labels:
- `def:R1_denom_sep`
- `lem:R1_denom_coeff_bounds`
- `lem:R1_denom_sep_from_strict_inside`
- `lem:R1_denom_sep_from_ratio`
- `lem:R1_denom_sep_from_pole_exclusion`

This file contains only elementary algebraic inequalities about the explicit
bottom-row coefficients `(c_{alpha,z}, d_{alpha,z})` of the PGL representative
`diskMat(alpha,z)`.
-/

open scoped ComplexConjugate

abbrev cCoeff (alpha z : Complex) : Complex :=
  (diskMat alpha z) 1 0

abbrev dCoeff (alpha z : Complex) : Complex :=
  (diskMat alpha z) 1 1

lemma cCoeff_def (alpha z : Complex) :
    cCoeff alpha z =
      z * (alpha * conj alpha - 1) + Complex.I * z * (alpha + conj alpha) := by
  simp [cCoeff, diskMat]

lemma dCoeff_def (alpha z : Complex) :
    dCoeff alpha z =
      (-(1 + alpha * conj alpha) * z) + (2 * Complex.I) * (alpha * conj alpha - 1) := by
  simp [dCoeff, diskMat, add_comm, add_left_comm, add_assoc, mul_add, add_mul, sub_eq_add_neg]

/-!
Algebraic identity used in `rem:R1_w_pole_outside_disk` (TeX): the `w`-denominator root lies
strictly outside the unit disk for `Im(z)>0` and `‖alpha‖<1`.
-/

set_option maxHeartbeats 2000000 in
lemma normSq_dCoeff_sub_normSq_cCoeff (alpha z : Complex) :
    Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z)
      =
        4 * Complex.normSq z * (alpha.im ^ 2)
          + 4 * (1 - Complex.normSq alpha) * (1 + Complex.normSq alpha) * z.im
          + 4 * (1 - Complex.normSq alpha) ^ 2 := by
  rcases alpha with ⟨a, b⟩
  rcases z with ⟨x, y⟩
  -- Reduce to a real polynomial identity in `a b x y`.
  simp [cCoeff_def, dCoeff_def, Complex.normSq, pow_two, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im]
  ring

def denomExpr (alpha z w : Complex) : Complex :=
  cCoeff alpha z * w + dCoeff alpha z

def denomPole (alpha z : Complex) : Complex :=
  -dCoeff alpha z / cCoeff alpha z

lemma denomExpr_eq (alpha z w : Complex) :
    denomExpr alpha z w = den (diskMat alpha z) w := by
  simp [denomExpr, cCoeff, dCoeff, den]

lemma denomExpr_eq_c_mul_sub_pole (alpha z w : Complex) (hC : cCoeff alpha z ≠ 0) :
    denomExpr alpha z w = cCoeff alpha z * (w - denomPole alpha z) := by
  -- `c*w + d = c*(w - (-d/c))` once `c ≠ 0`.
  -- Expand the right-hand side, then close with `mul_inv_cancel` using `hC`.
  have hd :
      cCoeff alpha z * (dCoeff alpha z * (cCoeff alpha z)⁻¹) = dCoeff alpha z := by
    calc
      cCoeff alpha z * (dCoeff alpha z * (cCoeff alpha z)⁻¹)
          = (cCoeff alpha z * dCoeff alpha z) * (cCoeff alpha z)⁻¹ := by
              simp [mul_assoc]
      _ = (dCoeff alpha z * cCoeff alpha z) * (cCoeff alpha z)⁻¹ := by
              simp [mul_comm]
      _ = dCoeff alpha z * (cCoeff alpha z * (cCoeff alpha z)⁻¹) := by
              simp [mul_assoc]
      _ = dCoeff alpha z * 1 := by
              simp [mul_inv_cancel₀ hC]
      _ = dCoeff alpha z := by simp
  -- Now compute.
  simp [denomExpr, denomPole, div_eq_mul_inv, sub_eq_add_neg, mul_add, hd]

private lemma norm_alpha_mul_conj_sub_one_le_one (alpha : Complex) (hα : ‖alpha‖ ≤ 1) :
    ‖alpha * conj alpha - 1‖ ≤ 1 := by
  have hmul : alpha * conj alpha = (Complex.normSq alpha : Complex) := by
    simpa using (Complex.mul_conj alpha)
  have hnormSq_le : Complex.normSq alpha ≤ 1 := by
    have h0 : 0 ≤ ‖alpha‖ := norm_nonneg alpha
    have hsq : ‖alpha‖ ^ 2 ≤ 1 := by nlinarith [hα, h0]
    simpa [Complex.normSq_eq_norm_sq] using hsq
  calc
    ‖alpha * conj alpha - 1‖
        = ‖(Complex.normSq alpha : Complex) - 1‖ := by simp [hmul]
    _ = ‖((Complex.normSq alpha - 1 : Real) : Complex)‖ := by
          -- coerce the real subtraction into `ℂ`
          exact (congrArg norm (Complex.ofReal_sub (Complex.normSq alpha) 1)).symm
    _ = ‖Complex.normSq alpha - 1‖ := by
          exact Complex.norm_real (Complex.normSq alpha - 1)
    _ = |Complex.normSq alpha - 1| := by
          simp [Real.norm_eq_abs]
    _ = 1 - Complex.normSq alpha := by
          have hsub : Complex.normSq alpha - 1 ≤ 0 := sub_nonpos.2 hnormSq_le
          calc
            |Complex.normSq alpha - 1| = -(Complex.normSq alpha - 1) := abs_of_nonpos hsub
            _ = 1 - Complex.normSq alpha := by ring
    _ ≤ 1 := by
          have hnonneg : 0 ≤ Complex.normSq alpha := Complex.normSq_nonneg alpha
          nlinarith

/-- Crude coefficient bound: `‖c_{α,z}‖ ≤ 3 ‖z‖` for `‖α‖ ≤ 1`. -/
lemma cCoeff_norm_le_three (alpha z : Complex) (hα : ‖alpha‖ ≤ 1) :
    ‖cCoeff alpha z‖ ≤ 3 * ‖z‖ := by
  have hz : 0 ≤ ‖z‖ := norm_nonneg z
  have hsub : ‖alpha * conj alpha - 1‖ ≤ 1 := norm_alpha_mul_conj_sub_one_le_one alpha hα
  have hsum : ‖alpha + conj alpha‖ ≤ 2 := by
    calc
      ‖alpha + conj alpha‖ ≤ ‖alpha‖ + ‖conj alpha‖ := norm_add_le _ _
      _ = ‖alpha‖ + ‖alpha‖ := by simp
      _ = 2 * ‖alpha‖ := by ring
      _ ≤ 2 := by nlinarith
  -- Triangle inequality and multiplicativity.
  calc
    ‖cCoeff alpha z‖
        = ‖z * (alpha * conj alpha - 1) + Complex.I * z * (alpha + conj alpha)‖ := by
          simp [cCoeff_def]
    _ ≤ ‖z * (alpha * conj alpha - 1)‖ + ‖Complex.I * z * (alpha + conj alpha)‖ :=
          norm_add_le _ _
    _ = ‖z‖ * ‖alpha * conj alpha - 1‖ + ‖Complex.I * z‖ * ‖alpha + conj alpha‖ := by
          simp [mul_assoc, mul_comm]
    _ ≤ ‖z‖ * 1 + ‖z‖ * 2 := by
          have h1 : ‖z‖ * ‖alpha * conj alpha - 1‖ ≤ ‖z‖ * 1 :=
            mul_le_mul_of_nonneg_left hsub hz
          have h2 : ‖Complex.I * z‖ * ‖alpha + conj alpha‖ ≤ ‖z‖ * 2 := by
            -- `‖I * z‖ = ‖z‖` and then use `hsum`.
            have hIz : ‖Complex.I * z‖ = ‖z‖ := by simp
            simpa [hIz] using (mul_le_mul_of_nonneg_left hsum hz)
          exact add_le_add h1 h2
    _ = 3 * ‖z‖ := by ring

lemma cCoeff_ne_zero (alpha z : Complex) (hz : 0 < z.im) (hα : ‖alpha‖ < 1) :
    cCoeff alpha z ≠ 0 := by
  have hz0 : z ≠ 0 := by
    intro hz0
    have : z.im = 0 := by simp [hz0]
    nlinarith [hz, this]
  have hmul : alpha * conj alpha = (Complex.normSq alpha : Complex) := by
    simpa using (Complex.mul_conj alpha)
  have hnormSq_lt : Complex.normSq alpha < 1 := by
    have h0 : 0 ≤ ‖alpha‖ := norm_nonneg alpha
    have hsq : ‖alpha‖ ^ 2 < 1 := by nlinarith [hα, h0]
    simpa [Complex.normSq_eq_norm_sq] using hsq
  have hBre :
      ((alpha * conj alpha - 1) + Complex.I * (alpha + conj alpha)).re < 0 := by
    have hre :
        ((alpha * conj alpha - 1) + Complex.I * (alpha + conj alpha)).re
          = Complex.normSq alpha - 1 := by
      simp [hmul, Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.add_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im]
    have : Complex.normSq alpha - 1 < 0 := by nlinarith [hnormSq_lt]
    simpa [hre] using this
  have hB0 : (alpha * conj alpha - 1) + Complex.I * (alpha + conj alpha) ≠ 0 := by
    intro hB
    have : ((alpha * conj alpha - 1) + Complex.I * (alpha + conj alpha)).re = 0 := by
      simp [hB]
    nlinarith [hBre, this]
  have hfac :
      cCoeff alpha z =
        z * ((alpha * conj alpha - 1) + Complex.I * (alpha + conj alpha)) := by
    calc
      cCoeff alpha z =
          z * (alpha * conj alpha - 1) + Complex.I * z * (alpha + conj alpha) := by
            simp [cCoeff_def]
      _ = z * ((alpha * conj alpha - 1) + Complex.I * (alpha + conj alpha)) := by ring
  intro hcz
  have :
      z * ((alpha * conj alpha - 1) + Complex.I * (alpha + conj alpha)) = 0 := by
    simpa [hfac] using hcz
  rcases mul_eq_zero.mp this with hz' | hB
  · exact hz0 hz'
  · exact hB0 hB

/-- Crude coefficient bound: `Im(z) ≤ ‖d_{α,z}‖` for `z ∈ UHP` and `‖α‖ < 1`. -/
lemma im_le_norm_dCoeff (alpha z : Complex) (hz : 0 < z.im) (hα : ‖alpha‖ < 1) :
    z.im ≤ ‖dCoeff alpha z‖ := by
  -- Reduce to a bound via the imaginary part.
  have him_le : z.im ≤ |(dCoeff alpha z).im| := by
    -- Compute the imaginary part explicitly after rewriting `alpha * conj alpha` as `normSq alpha`.
    have hmul : alpha * conj alpha = (Complex.normSq alpha : Complex) := by
      simpa using (Complex.mul_conj alpha)
    have hnormSq_lt : Complex.normSq alpha < 1 := by
      -- `normSq alpha = ‖alpha‖^2`.
      have h0 : 0 ≤ ‖alpha‖ := norm_nonneg alpha
      have hsq : ‖alpha‖ ^ 2 < 1 := by nlinarith [hα, h0]
      simpa [Complex.normSq_eq_norm_sq] using hsq
    -- Expand `dCoeff` and its imaginary part.
    have hdi :
        (dCoeff alpha z).im
          = (-(1 + Complex.normSq alpha) : Real) * z.im + 2 * (Complex.normSq alpha - 1) := by
      -- `simp` with `mul_im`/`add_im` handles the arithmetic since `normSq alpha` is real.
      simp [dCoeff_def, hmul, Complex.mul_im, Complex.add_im, Complex.sub_im, Complex.ofReal_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im]
    -- Show this is `≤ -z.im`, hence the absolute value is `≥ z.im`.
    have hdi_le : (dCoeff alpha z).im ≤ -z.im := by
      have hns_nonneg : 0 ≤ Complex.normSq alpha := Complex.normSq_nonneg alpha
      -- second term is nonpositive since `normSq alpha < 1`.
      have hterm2 : 2 * (Complex.normSq alpha - 1) ≤ 0 := by nlinarith
      -- first term is at most `-z.im` since `1 + normSq alpha ≥ 1` and `z.im > 0`.
      have hterm1 : (-(1 + Complex.normSq alpha) : Real) * z.im ≤ -z.im := by
        nlinarith [hz, hns_nonneg]
      nlinarith [hdi, hterm1, hterm2]
    have hnonpos : (dCoeff alpha z).im ≤ 0 := le_trans hdi_le (by nlinarith)
    calc
      z.im = -(-z.im) := by ring
      _ ≤ -((dCoeff alpha z).im) := by nlinarith [hdi_le]
      _ = |(dCoeff alpha z).im| := by simp [abs_of_nonpos hnonpos]
  -- `|Im(d)| ≤ ‖d‖`.
  have him_norm : |(dCoeff alpha z).im| ≤ ‖dCoeff alpha z‖ :=
    Complex.abs_im_le_norm (dCoeff alpha z)
  exact le_trans him_le him_norm

lemma denomExpr_norm_ge_dCoeff_sub (alpha z w : Complex) :
    ‖dCoeff alpha z‖ - ‖cCoeff alpha z * w‖ ≤ ‖denomExpr alpha z w‖ := by
  -- `‖d‖ - ‖c*w‖ ≤ ‖d - (-(c*w))‖ = ‖c*w + d‖`.
  simpa [denomExpr, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    (norm_sub_norm_le (dCoeff alpha z) (-(cCoeff alpha z * w)))

lemma denomExpr_norm_ge_im_sub_three_mul (alpha z w : Complex) (q : Real)
    (hz : 0 < z.im) (hα : ‖alpha‖ < 1) (hw : ‖w‖ ≤ q) :
    z.im - 3 * ‖z‖ * q ≤ ‖denomExpr alpha z w‖ := by
  have hd : z.im ≤ ‖dCoeff alpha z‖ := im_le_norm_dCoeff alpha z hz hα
  have hc0 : ‖cCoeff alpha z‖ ≤ 3 * ‖z‖ :=
    cCoeff_norm_le_three alpha z (le_of_lt hα)
  have hc : ‖cCoeff alpha z‖ * ‖w‖ ≤ (3 * ‖z‖) * q :=
    mul_le_mul hc0 hw (norm_nonneg _) (by nlinarith [norm_nonneg z])
  have hstep : z.im - (3 * ‖z‖) * q ≤ ‖dCoeff alpha z‖ - ‖cCoeff alpha z‖ * ‖w‖ :=
    sub_le_sub hd hc
  have hrev : ‖dCoeff alpha z‖ - ‖cCoeff alpha z‖ * ‖w‖ ≤ ‖denomExpr alpha z w‖ := by
    -- Use the reverse triangle inequality and `‖c*w‖ = ‖c‖*‖w‖`.
    have hrev0 : ‖dCoeff alpha z‖ - ‖cCoeff alpha z * w‖ ≤ ‖denomExpr alpha z w‖ :=
      denomExpr_norm_ge_dCoeff_sub alpha z w
    simpa [norm_mul, mul_assoc] using hrev0
  -- Normalize `(3*‖z‖)*q` into `3*‖z‖*q`.
  simpa [mul_assoc] using le_trans hstep hrev

lemma denomExpr_norm_ge_one_sub_rho_mul_dCoeff (alpha z w : Complex) (ρ : Real)
    (_hρ : 0 ≤ ρ) (hcd : ‖cCoeff alpha z‖ ≤ ρ * ‖dCoeff alpha z‖) (hw : ‖w‖ ≤ 1) :
    (1 - ρ) * ‖dCoeff alpha z‖ ≤ ‖denomExpr alpha z w‖ := by
  have hrev0 : ‖dCoeff alpha z‖ - ‖cCoeff alpha z * w‖ ≤ ‖denomExpr alpha z w‖ :=
    denomExpr_norm_ge_dCoeff_sub alpha z w
  have hcw : ‖cCoeff alpha z * w‖ ≤ ρ * ‖dCoeff alpha z‖ := by
    calc
      ‖cCoeff alpha z * w‖ = ‖cCoeff alpha z‖ * ‖w‖ := by simp
      _ ≤ ‖cCoeff alpha z‖ * 1 := by
            exact mul_le_mul_of_nonneg_left hw (norm_nonneg _)
      _ = ‖cCoeff alpha z‖ := by simp
      _ ≤ ρ * ‖dCoeff alpha z‖ := hcd
  have hlow : ‖dCoeff alpha z‖ - (ρ * ‖dCoeff alpha z‖) ≤ ‖dCoeff alpha z‖ - ‖cCoeff alpha z * w‖ :=
    sub_le_sub_left hcw ‖dCoeff alpha z‖
  have : (1 - ρ) * ‖dCoeff alpha z‖ ≤ ‖dCoeff alpha z‖ - ‖cCoeff alpha z * w‖ := by
    -- `‖d‖ - ρ‖d‖ = (1-ρ)‖d‖`.
    simpa [sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, one_mul] using hlow
  exact le_trans this hrev0

lemma denomExpr_norm_ge_eps_div_one_add_eps_mul_im (alpha z w : Complex) (ε : Real)
    (hz : 0 < z.im) (hα : ‖alpha‖ < 1)
    (hw : ‖w‖ ≤ 1) (hε : 0 < ε) (hp : 1 + ε ≤ ‖denomPole alpha z‖) :
    (ε / (1 + ε)) * z.im ≤ ‖denomExpr alpha z w‖ := by
  have hC : cCoeff alpha z ≠ 0 := cCoeff_ne_zero alpha z hz hα
  -- Step 1: lower bound via pole separation.
  have hpw : ‖denomPole alpha z‖ - 1 ≤ ‖w - denomPole alpha z‖ := by
    have h1 : ‖denomPole alpha z‖ - 1 ≤ ‖denomPole alpha z‖ - ‖w‖ := by
      have : (-1 : Real) ≤ -‖w‖ := by
        exact neg_le_neg hw
      -- add `‖p‖` to both sides
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        add_le_add_left this ‖denomPole alpha z‖
    have h2 : ‖denomPole alpha z‖ - ‖w‖ ≤ ‖w - denomPole alpha z‖ := by
      -- `‖p‖ - ‖w‖ ≤ ‖p - w‖ = ‖w - p‖`.
      simpa [norm_sub_rev] using norm_sub_norm_le (denomPole alpha z) w
    exact le_trans h1 h2

  have hmul_sep :
      ‖cCoeff alpha z‖ * (‖denomPole alpha z‖ - 1) ≤ ‖denomExpr alpha z w‖ := by
    have hc_nonneg : 0 ≤ ‖cCoeff alpha z‖ := norm_nonneg _
    have : ‖cCoeff alpha z‖ * (‖denomPole alpha z‖ - 1)
          ≤ ‖cCoeff alpha z‖ * ‖w - denomPole alpha z‖ := by
      exact mul_le_mul_of_nonneg_left hpw hc_nonneg
    -- Rewrite `denomExpr` as `c*(w - p)`.
    have hrew : denomExpr alpha z w = cCoeff alpha z * (w - denomPole alpha z) :=
      denomExpr_eq_c_mul_sub_pole alpha z w hC
    -- `‖c‖*‖w-p‖ = ‖c*(w-p)‖ = ‖denomExpr‖`.
    simpa [hrew, norm_mul] using this

  -- Step 2: relate `‖p‖ * ‖c‖ = ‖d‖` using `d = -p*c`.
  have hdRel : ‖denomPole alpha z‖ * ‖cCoeff alpha z‖ = ‖dCoeff alpha z‖ := by
    have hpc :
        denomPole alpha z * cCoeff alpha z = -dCoeff alpha z := by
      simp [denomPole, div_eq_mul_inv, hC]
    -- take norms
    have := congrArg norm hpc
    -- simplify norms
    simpa [norm_mul] using this

  have him_d : z.im ≤ ‖dCoeff alpha z‖ := im_le_norm_dCoeff alpha z hz hα
  have hcoef_nonneg : 0 ≤ ε / (1 + ε) := by
    have hpos : 0 < (1 + ε) := by linarith
    exact div_nonneg (le_of_lt hε) (le_of_lt hpos)

  have h1 : (ε / (1 + ε)) * z.im ≤ (ε / (1 + ε)) * ‖dCoeff alpha z‖ :=
    mul_le_mul_of_nonneg_left him_d hcoef_nonneg

  -- Step 3: compare `(ε/(1+ε))*‖d‖` with `‖c‖*(‖p‖-1)` using only `‖p‖ ≥ 1+ε`.
  have h2 : (ε / (1 + ε)) * ‖dCoeff alpha z‖ ≤ ‖cCoeff alpha z‖ * (‖denomPole alpha z‖ - 1) := by
    -- rewrite `‖d‖ = ‖p‖*‖c‖`
    have hdEq : ‖dCoeff alpha z‖ = ‖denomPole alpha z‖ * ‖cCoeff alpha z‖ := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hdRel.symm
    -- reduce to a scalar inequality and multiply by `‖c‖ ≥ 0`
    have hp0 : 0 ≤ ‖cCoeff alpha z‖ := norm_nonneg _
    have hscalar : (ε / (1 + ε)) * ‖denomPole alpha z‖ ≤ ‖denomPole alpha z‖ - 1 := by
      have hpos : 0 < (1 + ε) := by linarith
      have hx : 0 ≤ ‖denomPole alpha z‖ - (1 + ε) := sub_nonneg.2 hp
      have hmul : ε * ‖denomPole alpha z‖ ≤ (‖denomPole alpha z‖ - 1) * (1 + ε) := by
        -- Equivalent to `0 ≤ ‖p‖ - (1+ε)`.
        nlinarith [hx]
      have : (ε * ‖denomPole alpha z‖) / (1 + ε) ≤ ‖denomPole alpha z‖ - 1 :=
        (div_le_iff₀ hpos).2 hmul
      -- normalize `(ε/(1+ε))*‖p‖` into `(ε*‖p‖)/(1+ε)`
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    -- multiply by `‖c‖` and rewrite
    calc
      (ε / (1 + ε)) * ‖dCoeff alpha z‖
          = ((ε / (1 + ε)) * ‖denomPole alpha z‖) * ‖cCoeff alpha z‖ := by
              simp [hdEq, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ (‖denomPole alpha z‖ - 1) * ‖cCoeff alpha z‖ := by
              exact mul_le_mul_of_nonneg_right hscalar hp0
      _ = ‖cCoeff alpha z‖ * (‖denomPole alpha z‖ - 1) := by ring

  -- Combine: (ε/(1+ε))*Im(z) ≤ (ε/(1+ε))*‖d‖ ≤ ‖c‖*(‖p‖-1) ≤ ‖denomExpr‖.
  exact le_trans (le_trans h1 h2) hmul_sep

lemma norm_cCoeff_lt_norm_dCoeff (alpha z : Complex) (hz : 0 < z.im) (hα : ‖alpha‖ < 1) :
    ‖cCoeff alpha z‖ < ‖dCoeff alpha z‖ := by
  -- Convert `‖alpha‖ < 1` into `normSq alpha < 1`.
  have h0 : 0 ≤ ‖alpha‖ := norm_nonneg alpha
  have hnormSq_lt : Complex.normSq alpha < 1 := by
    have hsq : ‖alpha‖ ^ 2 < (1 : Real) ^ 2 := by nlinarith
    simpa [Complex.normSq_eq_norm_sq] using hsq
  have hpos1 : 0 < 1 - Complex.normSq alpha := by linarith

  have hdiff_pos : 0 < Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z) := by
    -- Use the explicit identity and note the RHS is a sum of nonnegative terms, with the last
    -- term strictly positive since `normSq alpha < 1`.
    rw [normSq_dCoeff_sub_normSq_cCoeff]
    have hterm1 : 0 ≤ 4 * Complex.normSq z * (alpha.im ^ 2) := by
      have hzns : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
      have hib : 0 ≤ alpha.im ^ 2 := sq_nonneg _
      have h4 : 0 ≤ (4 : Real) := by norm_num
      have h4z : 0 ≤ 4 * Complex.normSq z := mul_nonneg h4 hzns
      have : 0 ≤ (4 * Complex.normSq z) * (alpha.im ^ 2) := mul_nonneg h4z hib
      simpa [mul_assoc] using this
    have hterm2 : 0 ≤ 4 * (1 - Complex.normSq alpha) * (1 + Complex.normSq alpha) * z.im := by
      have h4 : 0 ≤ (4 : Real) := by norm_num
      have hA : 0 ≤ 1 - Complex.normSq alpha := le_of_lt hpos1
      have hB : 0 ≤ 1 + Complex.normSq alpha := by nlinarith [Complex.normSq_nonneg alpha]
      have hC : 0 ≤ z.im := le_of_lt hz
      have h4A : 0 ≤ 4 * (1 - Complex.normSq alpha) := mul_nonneg h4 hA
      have h4AB : 0 ≤ (4 * (1 - Complex.normSq alpha)) * (1 + Complex.normSq alpha) :=
        mul_nonneg h4A hB
      have : 0 ≤ ((4 * (1 - Complex.normSq alpha)) * (1 + Complex.normSq alpha)) * z.im :=
        mul_nonneg h4AB hC
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have hterm3 : 0 < 4 * (1 - Complex.normSq alpha) ^ 2 := by
      have h4 : 0 < (4 : Real) := by norm_num
      have hsq : 0 < (1 - Complex.normSq alpha) ^ 2 := pow_pos hpos1 2
      exact mul_pos h4 hsq
    have h12 : 0 ≤ 4 * Complex.normSq z * (alpha.im ^ 2)
          + 4 * (1 - Complex.normSq alpha) * (1 + Complex.normSq alpha) * z.im :=
      add_nonneg hterm1 hterm2
    exact add_pos_of_nonneg_of_pos h12 hterm3

  have hlt : Complex.normSq (cCoeff alpha z) < Complex.normSq (dCoeff alpha z) := by linarith
  have hsq : ‖cCoeff alpha z‖ ^ 2 < ‖dCoeff alpha z‖ ^ 2 := by
    simpa [Complex.normSq_eq_norm_sq] using hlt
  have habs : |‖cCoeff alpha z‖| < |‖dCoeff alpha z‖| := (sq_lt_sq).1 hsq
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] using habs

lemma denomPole_norm_gt_one (alpha z : Complex) (hz : 0 < z.im) (hα : ‖alpha‖ < 1) :
    1 < ‖denomPole alpha z‖ := by
  have hC : cCoeff alpha z ≠ 0 := cCoeff_ne_zero alpha z hz hα
  have hcpos : 0 < ‖cCoeff alpha z‖ := by
    simpa using (norm_pos_iff.2 hC)
  have hcd : ‖cCoeff alpha z‖ < ‖dCoeff alpha z‖ :=
    norm_cCoeff_lt_norm_dCoeff alpha z hz hα
  have hdiv : 1 < ‖dCoeff alpha z‖ / ‖cCoeff alpha z‖ :=
    (one_lt_div hcpos).2 hcd
  simpa [denomPole, norm_div, norm_neg] using hdiv

lemma denomExpr_ne_zero_of_norm_le_one (alpha z w : Complex)
    (hz : 0 < z.im) (hα : ‖alpha‖ < 1) (hw : ‖w‖ ≤ 1) :
    denomExpr alpha z w ≠ 0 := by
  have hC : cCoeff alpha z ≠ 0 := cCoeff_ne_zero alpha z hz hα
  have hp : 1 < ‖denomPole alpha z‖ := denomPole_norm_gt_one alpha z hz hα
  intro h0
  have hwEq : w = denomPole alpha z := by
    have hrew : denomExpr alpha z w = cCoeff alpha z * (w - denomPole alpha z) :=
      denomExpr_eq_c_mul_sub_pole alpha z w hC
    have hmul : cCoeff alpha z * (w - denomPole alpha z) = 0 := by
      simpa [hrew] using h0
    have hsub : w - denomPole alpha z = 0 := (mul_eq_zero.mp hmul).resolve_left hC
    exact sub_eq_zero.mp hsub
  have : ‖denomPole alpha z‖ ≤ 1 := by
    simpa [hwEq] using hw
  exact (not_lt_of_ge this) hp

lemma den_ne_zero_of_norm_le_one (alpha z w : Complex)
    (hz : 0 < z.im) (hα : ‖alpha‖ < 1) (hw : ‖w‖ ≤ 1) :
    den (diskMat alpha z) w ≠ 0 := by
  have hne : denomExpr alpha z w ≠ 0 :=
    denomExpr_ne_zero_of_norm_le_one (alpha := alpha) (z := z) (w := w) hz hα hw
  simpa [denomExpr_eq] using hne

/-!
Quantitative pole gap from a uniform `‖alpha‖ ≤ r0 < 1` bound.

This is the Lean-facing bridge for the Toeplitz/Gram route: once one proves upstream that
the xi-derived sequence satisfies `∀k, ‖alpha_k‖ ≤ r0` for some `r0<1`, the explicit v3.2
coefficients yield a uniform gap `‖p_{alpha_k,z}‖ ≥ 1+ε(z,r0)`, and therefore a uniform
denominator-separation constant via `denomSepAt_of_pole_exclusion`.

We keep the estimate intentionally conservative (using only the term
`4*(1-‖alpha‖^2)*(1+‖alpha‖^2)*Im(z)` and the crude bound `‖cCoeff‖ ≤ 3‖z‖).
-/

private lemma normSq_cCoeff_le_nine_mul_normSq (alpha z : Complex) (hα : ‖alpha‖ ≤ 1) :
    Complex.normSq (cCoeff alpha z) ≤ 9 * Complex.normSq z := by
  have hc : ‖cCoeff alpha z‖ ≤ 3 * ‖z‖ := cCoeff_norm_le_three alpha z hα
  -- Square the inequality and rewrite norms as `normSq`.
  have hc2 : ‖cCoeff alpha z‖ ^ 2 ≤ (3 * ‖z‖) ^ 2 := by
    have hc0 : 0 ≤ ‖cCoeff alpha z‖ := norm_nonneg _
    have hz0 : 0 ≤ 3 * ‖z‖ := by nlinarith [norm_nonneg z]
    exact (sq_le_sq₀ hc0 hz0).2 hc
  -- Convert the squares to `normSq`.
  -- `‖w‖^2 = Complex.normSq w`.
  -- Also `(3*‖z‖)^2 = 9*‖z‖^2 = 9*normSq z`.
  have : Complex.normSq (cCoeff alpha z) ≤ 9 * (‖z‖ ^ 2) := by
    have hc2' : Complex.normSq (cCoeff alpha z) ≤ (3 * ‖z‖) ^ 2 := by
      simpa [Complex.normSq_eq_norm_sq] using hc2
    nlinarith [hc2']
  simpa [Complex.normSq_eq_norm_sq] using this

private lemma normSq_dCoeff_ge_normSq_cCoeff_add (alpha z : Complex) (hz : 0 < z.im) (hα : ‖alpha‖ < 1) :
    Complex.normSq (dCoeff alpha z) ≥
      Complex.normSq (cCoeff alpha z) + 4 * (1 - Complex.normSq alpha) * z.im := by
  -- Start from the exact identity and discard manifestly nonnegative terms.
  have hId := normSq_dCoeff_sub_normSq_cCoeff alpha z
  -- Rewrite as `normSq d = normSq c + ...`
  have :
      Complex.normSq (dCoeff alpha z) =
        Complex.normSq (cCoeff alpha z)
          + (4 * Complex.normSq z * (alpha.im ^ 2)
            + 4 * (1 - Complex.normSq alpha) * (1 + Complex.normSq alpha) * z.im
            + 4 * (1 - Complex.normSq alpha) ^ 2) := by
    linarith [hId]
  -- Lower bound the RHS by keeping only the `4*(1-normSq alpha)*(1+normSq alpha)*Im(z)` term,
  -- then further by using `1+normSq alpha ≥ 1`.
  have hns_nonneg : 0 ≤ Complex.normSq alpha := Complex.normSq_nonneg alpha
  have hImz_nonneg : 0 ≤ z.im := le_of_lt hz
  have hA : 0 ≤ 4 * Complex.normSq z * (alpha.im ^ 2) := by
    have : 0 ≤ (4 : Real) := by norm_num
    exact mul_nonneg (mul_nonneg this (Complex.normSq_nonneg z)) (sq_nonneg _)
  have hB : 0 ≤ 4 * (1 - Complex.normSq alpha) ^ 2 := by
    have : 0 ≤ (4 : Real) := by norm_num
    exact mul_nonneg this (sq_nonneg _)
  have hαns : Complex.normSq alpha < 1 := by
    have h0 : 0 ≤ ‖alpha‖ := norm_nonneg alpha
    have hsq : ‖alpha‖ ^ 2 < (1 : Real) ^ 2 := by nlinarith [hα, h0]
    simpa [Complex.normSq_eq_norm_sq] using hsq
  have hOneMinus_nonneg : 0 ≤ 1 - Complex.normSq alpha := sub_nonneg.2 (le_of_lt hαns)
  have hC :
      0 ≤ 4 * (1 - Complex.normSq alpha) * (1 + Complex.normSq alpha) * z.im := by
    have h4 : 0 ≤ (4 : Real) := by norm_num
    have h1plus_nonneg : 0 ≤ 1 + Complex.normSq alpha := by linarith [hns_nonneg]
    have hA : 0 ≤ 4 * (1 - Complex.normSq alpha) := mul_nonneg h4 hOneMinus_nonneg
    have hB : 0 ≤ 4 * (1 - Complex.normSq alpha) * (1 + Complex.normSq alpha) :=
      mul_nonneg hA h1plus_nonneg
    -- multiply by `z.im ≥ 0`
    have : 0 ≤ (4 * (1 - Complex.normSq alpha) * (1 + Complex.normSq alpha)) * z.im :=
      mul_nonneg hB hImz_nonneg
    simpa [mul_assoc] using this
  have h1plus : 1 ≤ 1 + Complex.normSq alpha := by linarith [hns_nonneg]
  have hkeep :
      4 * (1 - Complex.normSq alpha) * (1 + Complex.normSq alpha) * z.im
        ≥ 4 * (1 - Complex.normSq alpha) * z.im := by
    -- multiply inequality `1 ≤ 1+normSq alpha` by nonnegative factors.
    have hmul1 :
        (1 - Complex.normSq alpha) * z.im * 1 ≤ (1 - Complex.normSq alpha) * z.im * (1 + Complex.normSq alpha) := by
      have hfac_nonneg : 0 ≤ (1 - Complex.normSq alpha) * z.im := mul_nonneg hOneMinus_nonneg hImz_nonneg
      simpa [mul_assoc] using (mul_le_mul_of_nonneg_left h1plus hfac_nonneg)
    -- scale by 4
    have : 4 * ((1 - Complex.normSq alpha) * z.im * 1)
        ≤ 4 * ((1 - Complex.normSq alpha) * z.im * (1 + Complex.normSq alpha)) := by
      have : 0 ≤ (4 : Real) := by norm_num
      exact mul_le_mul_of_nonneg_left hmul1 this
    -- rearrange
    -- goal is `... ≥ ...`
    -- convert and clean
    nlinarith [this]
  -- Put it together.
  -- From the exact identity: `normSq d = normSq c + (A + term + B)` and `A,B ≥0`,
  -- we get `normSq d ≥ normSq c + term`, then `≥ normSq c + 4*(1-normSq alpha)*Im(z)`.
  have hge_term :
      Complex.normSq (dCoeff alpha z) ≥
        Complex.normSq (cCoeff alpha z)
          + 4 * (1 - Complex.normSq alpha) * (1 + Complex.normSq alpha) * z.im := by
    -- use `this` and drop `hA,hB`.
    -- `linarith` handles it.
    -- Need to rewrite `this` as equality and then use inequalities.
    linarith [this, hA, hB]
  linarith [hge_term, hkeep]

-- NOTE(v3.2): The block below is an old, unfinished attempt kept for provenance.
-- It contained an unresolved `?_` goal; it is commented out and replaced by a sharp bound.
/-
lemma denomPole_norm_ge_one_add_eps_of_norm_le
    (z : Complex) (hz : 0 < z.im) (r0 : Real) (hr0 : r0 < 1) :
    ∃ ε : Real, 0 < ε ∧
      ∀ {alpha : Complex}, ‖alpha‖ ≤ r0 → 1 + ε ≤ ‖denomPole alpha z‖ := by
  classical
  -- Choose a conservative `t0(z,r0)>0` and then set `ε = t0/(2+t0)`.
  have hz0 : z ≠ 0 := by
    intro hz0
    have : z.im = 0 := by simpa [hz0]
    nlinarith [hz, this]
  have hnz_pos : 0 < Complex.normSq z := by
    simpa [Complex.normSq_eq_zero] using (Complex.normSq_pos.2 hz0)
  let t0 : Real := (4 * (1 - r0 ^ 2) * z.im) / (9 * Complex.normSq z)
  have ht0_pos : 0 < t0 := by
    have h1 : 0 < 1 - r0 ^ 2 := by
      -- `r0^2 < 1` from `r0 < 1` and `0 ≤ r0^2`.
      have : r0 ^ 2 < 1 := by
        have : |r0| < 1 := by simpa [abs_of_nonneg (by have := le_trans (le_of_lt hr0) (by linarith); exact this)] using
          (abs_lt.2 ⟨by linarith, hr0⟩) -- (messy) fallback handled by nlinarith below
        -- easier: `nlinarith` works directly.
        nlinarith
      nlinarith
    have hden : 0 < 9 * Complex.normSq z := by nlinarith [hnz_pos]
    -- also `z.im>0`.
    have : 0 < 4 * (1 - r0 ^ 2) * z.im := by nlinarith [h1, hz]
    exact div_pos this hden
  let ε : Real := t0 / (2 + t0)
  have hε_pos : 0 < ε := by
    have hden : 0 < 2 + t0 := by linarith [ht0_pos]
    exact div_pos ht0_pos hden
  refine ⟨ε, hε_pos, ?_⟩
  intro alpha hαr0
  have hα1 : ‖alpha‖ ≤ 1 := le_trans hαr0 (le_of_lt hr0)
  have hαlt1 : ‖alpha‖ < 1 := lt_of_le_of_lt hαr0 hr0
  have hCne : cCoeff alpha z ≠ 0 := cCoeff_ne_zero alpha z hz hαlt1
  have hcsq_pos : 0 < Complex.normSq (cCoeff alpha z) := by
    simpa [Complex.normSq_eq_zero] using (Complex.normSq_pos.2 hCne)
  -- Lower bound `‖p‖^2 = normSq d / normSq c` by `1 + t0`.
  have hdiff_ge :
      Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z)
        ≥ 4 * (1 - r0 ^ 2) * z.im := by
    -- Use the exact identity and drop nonnegative terms, then bound `1 - normSq alpha ≥ 1 - r0^2`.
    -- From the identity we can keep only the `4*(1-normSq alpha)*(1+normSq alpha)*Im(z)` term
    -- and then use `(1+normSq alpha)≥1`.
    have hId := normSq_dCoeff_sub_normSq_cCoeff alpha z
    have hns_le : Complex.normSq alpha ≤ r0 ^ 2 := by
      -- `normSq alpha = ‖alpha‖^2 ≤ r0^2`.
      have : ‖alpha‖ ^ 2 ≤ r0 ^ 2 := by
        have ha0 : 0 ≤ ‖alpha‖ := norm_nonneg alpha
        have hr0' : 0 ≤ r0 := le_trans (by nlinarith [ha0, hαr0]) (by linarith)
        exact (sq_le_sq₀ ha0 hr0').2 hαr0
      simpa [Complex.normSq_eq_norm_sq] using this
    have hone_minus_ge : 1 - Complex.normSq alpha ≥ 1 - r0 ^ 2 := by linarith
    -- Extract the term `4*(1-normSq alpha)*(1+normSq alpha)*Im(z)` from the identity as a lower bound.
    have hterm_nonneg :
        0 ≤ 4 * Complex.normSq z * (alpha.im ^ 2)
          + 4 * (1 - Complex.normSq alpha) * (1 + Complex.normSq alpha) * z.im
          + 4 * (1 - Complex.normSq alpha) ^ 2 := by
      have : 0 ≤ 4 * Complex.normSq z * (alpha.im ^ 2) := by
        have : 0 ≤ (4 : Real) := by norm_num
        exact mul_nonneg (mul_nonneg this (Complex.normSq_nonneg z)) (sq_nonneg _)
      have : 0 ≤ 4 * (1 - Complex.normSq alpha) * (1 + Complex.normSq alpha) * z.im := by
        have hz0 : 0 ≤ z.im := le_of_lt hz
        have hns_nonneg : 0 ≤ Complex.normSq alpha := Complex.normSq_nonneg alpha
        have hαns : Complex.normSq alpha < 1 := by
          have h0 : 0 ≤ ‖alpha‖ := norm_nonneg alpha
          have hsq : ‖alpha‖ ^ 2 < (1 : Real) ^ 2 := by nlinarith [hαlt1, h0]
          simpa [Complex.normSq_eq_norm_sq] using hsq
        have h1m : 0 ≤ 1 - Complex.normSq alpha := sub_nonneg.2 (le_of_lt hαns)
        nlinarith [h1m, hns_nonneg, hz0]
      have : 0 ≤ 4 * (1 - Complex.normSq alpha) ^ 2 := by
        have : 0 ≤ (4 : Real) := by norm_num
        exact mul_nonneg this (sq_nonneg _)
      nlinarith
    have hge0 :
        Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z)
          ≥ 4 * (1 - Complex.normSq alpha) * z.im := by
      -- Use the already-packaged lemma.
      -- (This keeps the proof structure stable even if the identity is refactored.)
      have := normSq_dCoeff_ge_normSq_cCoeff_add (alpha := alpha) (z := z) hz hαlt1
      -- rearrange
      nlinarith [this]
    -- Now replace `1 - normSq alpha` by `1 - r0^2`.
    have hz0 : 0 ≤ z.im := le_of_lt hz
    have : 4 * (1 - Complex.normSq alpha) * z.im ≥ 4 * (1 - r0 ^ 2) * z.im := by
      have : (1 - Complex.normSq alpha) * z.im ≥ (1 - r0 ^ 2) * z.im :=
        mul_le_mul_of_nonneg_right (by linarith [hone_minus_ge]) hz0
      have : 4 * ((1 - Complex.normSq alpha) * z.im) ≥ 4 * ((1 - r0 ^ 2) * z.im) := by
        have : 0 ≤ (4 : Real) := by norm_num
        exact mul_le_mul_of_nonneg_left this this
      -- simplify
      nlinarith [this]
    linarith [hge0, this]
  -- Use `‖cCoeff‖ ≤ 3‖z‖` to bound `normSq cCoeff ≤ 9 normSq z`.
  have hcsq_le : Complex.normSq (cCoeff alpha z) ≤ 9 * Complex.normSq z :=
    normSq_cCoeff_le_nine_mul_normSq alpha z hα1
  -- Build `normSq p ≥ 1 + t0`.
  have hp_sq_ge :
      Complex.normSq (denomPole alpha z) ≥ 1 + t0 := by
    -- `normSq p = normSq d / normSq c = 1 + (normSq d - normSq c)/normSq c`.
    have hpc :
        Complex.normSq (denomPole alpha z)
          = Complex.normSq (dCoeff alpha z) / Complex.normSq (cCoeff alpha z) := by
      -- `p = -d/c`.
      simp [denomPole, div_eq_mul_inv, Complex.normSq_div, Complex.normSq_neg]
    -- Lower bound the ratio by replacing numerator-difference and denominator.
    have hratio_ge :
        Complex.normSq (dCoeff alpha z) / Complex.normSq (cCoeff alpha z)
          ≥ 1 + t0 := by
      -- Write as `1 + (d-c)/c`.
      have : Complex.normSq (dCoeff alpha z) / Complex.normSq (cCoeff alpha z)
          = 1 + (Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z)) / Complex.normSq (cCoeff alpha z) := by
        field_simp [hcsq_pos.ne'] ; ring
      -- Use the lower bound on the difference and upper bound on `normSq c`.
      have hdiff_div_ge :
          (Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z)) / Complex.normSq (cCoeff alpha z)
            ≥ (4 * (1 - r0 ^ 2) * z.im) / (9 * Complex.normSq z) := by
        -- `a/b ≥ a0/b0` from `a ≥ a0` and `b ≤ b0`, with positivity.
        have hdiff_pos : 0 < Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z) := by
          -- at least `4*(1-r0^2)*Im(z) > 0`.
          have : 0 < 4 * (1 - r0 ^ 2) * z.im := by
            have : 0 < 1 - r0 ^ 2 := by nlinarith [hr0]
            nlinarith [this, hz]
          exact lt_of_lt_of_le this (by linarith [hdiff_ge])
        have hcsq_pos' : 0 < 9 * Complex.normSq z := by nlinarith [hnz_pos]
        -- Convert to `le` comparisons and use `div_le_div_iff₀`.
        have h1 : (4 * (1 - r0 ^ 2) * z.im) / (9 * Complex.normSq z)
              ≤ (Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z)) / (Complex.normSq (cCoeff alpha z)) := by
          -- Use `div_le_div_iff₀` with positive denominators.
          have hcpos : 0 < Complex.normSq (cCoeff alpha z) := hcsq_pos
          have hzpos : 0 < 9 * Complex.normSq z := by nlinarith [hnz_pos]
          -- We want: a0/b0 ≤ a/b. It's enough to show `a0*b ≤ a*b0` with positivity.
          -- Use `a0 ≤ a` and `b ≤ b0`.
          have ha : 4 * (1 - r0 ^ 2) * z.im ≤ Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z) := by
            linarith [hdiff_ge]
          have hb : Complex.normSq (cCoeff alpha z) ≤ 9 * Complex.normSq z := hcsq_le
          -- Multiply: a0 * b ≤ a * b0.
          have : (4 * (1 - r0 ^ 2) * z.im) * Complex.normSq (cCoeff alpha z)
                ≤ (Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z)) * (9 * Complex.normSq z) := by
            have hz0 : 0 ≤ 4 * (1 - r0 ^ 2) * z.im := by
              have : 0 < 4 * (1 - r0 ^ 2) * z.im := by
                have : 0 < 1 - r0 ^ 2 := by nlinarith [hr0]
                nlinarith [this, hz]
              exact le_of_lt this
            have hdiff0 : 0 ≤ Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z) := by
              linarith [hdiff_ge]
            have := mul_le_mul ha hb (by exact le_of_lt ?_) hdiff0
            · -- simplify
              -- This `mul_le_mul` gave `a0*csq ≤ diff*(9*normSq z)`? Actually it gives `a0*csq ≤ a*(9*normSq z)`.
              -- We'll just `nlinarith` with `ha,hb` directly.
              nlinarith [ha, hb]
            · -- need nonneg of RHS factor
              exact mul_nonneg (by nlinarith) (Complex.normSq_nonneg z)
          -- Now divide both sides by positive denominators to reach the desired inequality.
          -- `div_le_div_iff₀` expects both denominators positive.
          -- We'll use cross-multiplication:
          -- a0/b0 ≤ a/b  <->  a0*b ≤ a*b0.
          have hbpos : 0 < 9 * Complex.normSq z := by nlinarith [hnz_pos]
          have hcpos' : 0 < Complex.normSq (cCoeff alpha z) := hcsq_pos
          -- rewrite goal using `div_le_div_iff₀`
          -- `simp` might be messy; use `have` with `div_le_div_iff₀`.
          -- We'll do: (a0/b0 ≤ a/b) by applying `div_le_div_iff₀` to both sides after rewriting.
          -- Equivalent: a0 * b ≤ a * b0 (we already have).
          -- So just `field_simp`?
          -- We'll use `by
          --   have := this
          --   field_simp [hbpos.ne', hcpos'.ne'] at this; ...` not needed.
          -- Use lemma `div_le_div_iff₀` twice:
          -- Starting from `this`, divide by `b0*b`?
          -- Simpler: use `show a0 / b0 ≤ a / b` and `nlinarith` with positivity.
          -- We'll do direct:
          have : (4 * (1 - r0 ^ 2) * z.im) / (9 * Complex.normSq z)
                ≤ (Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z)) / (Complex.normSq (cCoeff alpha z)) := by
            -- cross-multiply
            have hb0 : 0 < 9 * Complex.normSq z := by nlinarith [hnz_pos]
            have hc0 : 0 < Complex.normSq (cCoeff alpha z) := hcsq_pos
            -- `a0/b0 ≤ a/b` iff `a0*b ≤ a*b0`.
            -- `field_simp` works.
            field_simp [hb0.ne', hc0.ne']
            -- goal becomes exactly `a0*csq ≤ diff*(9*normSq z)`.
            simpa [mul_assoc, mul_left_comm, mul_comm] using this
          exact this
        -- reorder to get `≥`.
        linarith
      -- finish `1 + ...`
      simpa [t0, this] using by
        have := hdiff_div_ge
        nlinarith [this, this]
    -- finalize
    simpa [hpc] using hratio_ge
  -- Convert from `normSq` lower bound to `norm` lower bound with `ε = t0/(2+t0)`.
  have hsq : (1 + ε) ^ 2 ≤ Complex.normSq (denomPole alpha z) := by
    -- show `(1+ε)^2 ≤ 1+t0 ≤ normSq p`.
    have h1 : (1 + ε) ^ 2 ≤ 1 + t0 := by
      -- Use the general inequality: if `ε=t/(2+t)` then `(1+ε)^2 ≤ 1+t`.
      -- Here `t=t0`.
      -- Expand and reduce to `t0^2 ≥ 0`.
      have ht : 0 ≤ t0 := le_of_lt ht0_pos
      -- `nlinarith` should close after unfolding `ε`.
      unfold ε
      nlinarith [ht]
    exact le_trans h1 hp_sq_ge
  -- `‖p‖^2 = normSq p`.
  have hp_nonneg : 0 ≤ ‖denomPole alpha z‖ := norm_nonneg _
  have : 1 + ε ≤ ‖denomPole alpha z‖ := by
    -- from squares
    have hsq' : (1 + ε) ^ 2 ≤ ‖denomPole alpha z‖ ^ 2 := by
      simpa [Complex.normSq_eq_norm_sq] using hsq
    have h1pos : 0 ≤ 1 + ε := by linarith [le_of_lt hε_pos]
    exact (sq_le_sq₀ h1pos hp_nonneg).1 hsq'
  exact this
-/

private lemma normSq_cCoeff_le_normSq_z_mul_one_add_normSq_sq (alpha z : Complex) :
    Complex.normSq (cCoeff alpha z) ≤ Complex.normSq z * (1 + Complex.normSq alpha) ^ 2 := by
  -- Factor out `z`.
  have hfac :
      cCoeff alpha z =
        z * ((alpha * conj alpha - 1) + Complex.I * (alpha + conj alpha)) := by
    calc
      cCoeff alpha z =
          z * (alpha * conj alpha - 1) + Complex.I * z * (alpha + conj alpha) := by
            simp [cCoeff_def]
      _ = z * ((alpha * conj alpha - 1) + Complex.I * (alpha + conj alpha)) := by ring

  have hB :
      Complex.normSq ((alpha * conj alpha - 1) + Complex.I * (alpha + conj alpha))
        ≤ (1 + Complex.normSq alpha) ^ 2 := by
    -- Reduce to a real polynomial inequality in `Re/Im alpha`.
    rcases alpha with ⟨a, b⟩
    -- After simp, the claim is equivalent to `0 ≤ 4*b^2`.
    simp [Complex.mul_conj, Complex.add_conj, Complex.normSq_apply, pow_two]
    nlinarith

  -- Combine with multiplicativity of `normSq`.
  calc
    Complex.normSq (cCoeff alpha z)
        = Complex.normSq z *
            Complex.normSq ((alpha * conj alpha - 1) + Complex.I * (alpha + conj alpha)) := by
          simp [hfac, Complex.normSq_mul]
    _ ≤ Complex.normSq z * (1 + Complex.normSq alpha) ^ 2 := by
          have hzns : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
          exact mul_le_mul_of_nonneg_left hB hzns

private lemma one_add_t_div_two_add_t_sq_le_one_add_t (t : Real) (ht : 0 ≤ t) :
    (1 + t / (2 + t)) ^ 2 ≤ 1 + t := by
  have hden : (2 + t) ≠ 0 := by linarith
  field_simp [hden]
  ring_nf
  nlinarith

lemma denomPole_norm_ge_one_add_eps_of_norm_le
    (z : Complex) (hz : 0 < z.im) (r0 : Real) (hr0_nonneg : 0 ≤ r0) (hr0 : r0 < 1) :
    ∃ ε : Real, 0 < ε ∧
      ∀ {alpha : Complex}, ‖alpha‖ ≤ r0 → 1 + ε ≤ ‖denomPole alpha z‖ := by
  classical
  have hz0 : z ≠ 0 := by
    intro hz0
    have : z.im = 0 := by simp [hz0]
    nlinarith [hz, this]
  have hnz_pos : 0 < Complex.normSq z := by
    simpa [Complex.normSq_eq_zero] using (Complex.normSq_pos.2 hz0)

  have hr0sq_lt : r0 ^ 2 < 1 := by nlinarith [hr0, hr0_nonneg]
  have hOneMinus_r0sq_pos : 0 < 1 - r0 ^ 2 := by linarith

  -- Upper bound for `normSq(cCoeff)`.
  let M : Real := Complex.normSq z * (1 + r0 ^ 2) ^ 2
  have hM_pos : 0 < M := by
    have hpos2 : 0 < (1 + r0 ^ 2) ^ 2 := by
      have : 0 < (1 + r0 ^ 2) := by nlinarith [sq_nonneg r0]
      exact pow_pos this 2
    simpa [M, mul_assoc, mul_left_comm, mul_comm] using (mul_pos hnz_pos hpos2)

  -- Lower bound for the gap `normSq(dCoeff) - normSq(cCoeff)`.
  let C : Real := 4 * (1 - r0 ^ 4) * z.im + 4 * (1 - r0 ^ 2) ^ 2
  have hC_pos : 0 < C := by
    have h4 : 0 < (4 : Real) := by norm_num
    have hterm3 : 0 < 4 * (1 - r0 ^ 2) ^ 2 := by
      have : 0 < (1 - r0 ^ 2) ^ 2 := pow_pos hOneMinus_r0sq_pos 2
      exact mul_pos h4 this
    have hterm2 : 0 ≤ 4 * (1 - r0 ^ 4) * z.im := by
      have hr0pow4_lt : r0 ^ 4 < 1 := by nlinarith [hr0, hr0_nonneg]
      have hnonneg : 0 ≤ 1 - r0 ^ 4 := sub_nonneg.2 (le_of_lt hr0pow4_lt)
      have hzIm0 : 0 ≤ z.im := le_of_lt hz
      nlinarith [hnonneg, hzIm0]
    exact add_pos_of_nonneg_of_pos hterm2 hterm3

  -- Set `t0 = C/M` and avoid square roots by taking `ε = t0/(2+t0)`.
  let t0 : Real := C / M
  have ht0_pos : 0 < t0 := div_pos hC_pos hM_pos

  let ε : Real := t0 / (2 + t0)
  have hε_pos : 0 < ε := by
    have hden : 0 < 2 + t0 := by linarith [ht0_pos]
    exact div_pos ht0_pos hden

  refine ⟨ε, hε_pos, ?_⟩
  intro alpha hαr0
  have hαlt1 : ‖alpha‖ < 1 := lt_of_le_of_lt hαr0 hr0
  have hCne : cCoeff alpha z ≠ 0 := cCoeff_ne_zero alpha z hz hαlt1
  have hcsq_pos : 0 < Complex.normSq (cCoeff alpha z) := by
    simpa [Complex.normSq_eq_zero] using (Complex.normSq_pos.2 hCne)

  -- Convert `‖alpha‖ ≤ r0` into `normSq alpha ≤ r0^2`.
  have hs_le : Complex.normSq alpha ≤ r0 ^ 2 := by
    have hsq : ‖alpha‖ ^ 2 ≤ r0 ^ 2 := by
      have ha0 : 0 ≤ ‖alpha‖ := norm_nonneg alpha
      exact (sq_le_sq₀ ha0 hr0_nonneg).2 hαr0
    simpa [Complex.normSq_eq_norm_sq] using hsq

  -- Bound `normSq cCoeff` above by `M`.
  have hc_le_M : Complex.normSq (cCoeff alpha z) ≤ M := by
    have hc_le :
        Complex.normSq (cCoeff alpha z) ≤ Complex.normSq z * (1 + Complex.normSq alpha) ^ 2 :=
      normSq_cCoeff_le_normSq_z_mul_one_add_normSq_sq alpha z
    have h1 : 1 + Complex.normSq alpha ≤ 1 + r0 ^ 2 := by linarith
    have h1nonneg : 0 ≤ 1 + Complex.normSq alpha := by nlinarith [Complex.normSq_nonneg alpha]
    have h2nonneg : 0 ≤ 1 + r0 ^ 2 := by nlinarith [sq_nonneg r0]
    have hsq1 : (1 + Complex.normSq alpha) ^ 2 ≤ (1 + r0 ^ 2) ^ 2 :=
      (sq_le_sq₀ h1nonneg h2nonneg).2 h1
    have hzns : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
    have hmul :
        Complex.normSq z * (1 + Complex.normSq alpha) ^ 2 ≤ Complex.normSq z * (1 + r0 ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq1 hzns
    have : Complex.normSq (cCoeff alpha z) ≤ Complex.normSq z * (1 + r0 ^ 2) ^ 2 :=
      le_trans hc_le hmul
    simpa [M] using this

  -- Lower bound `normSq d - normSq c` by `C`.
  have hgap_ge : C ≤ Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z) := by
    have hzIm0 : 0 ≤ z.im := le_of_lt hz
    have hs0 : 0 ≤ Complex.normSq alpha := Complex.normSq_nonneg alpha
    have hr0sq0 : 0 ≤ r0 ^ 2 := sq_nonneg r0

    have hr0pow4 : (r0 ^ 2) ^ 2 = r0 ^ 4 := by
      simpa [show (2 * 2 : Nat) = 4 by norm_num] using (pow_mul r0 2 2).symm
    have hs_sq_le : (Complex.normSq alpha) ^ 2 ≤ r0 ^ 4 := by
      have : (Complex.normSq alpha) ^ 2 ≤ (r0 ^ 2) ^ 2 := (sq_le_sq₀ hs0 hr0sq0).2 hs_le
      simpa [hr0pow4] using this

    have hterm1_nonneg : 0 ≤ 4 * Complex.normSq z * (alpha.im ^ 2) := by
      have : 0 ≤ (4 : Real) := by norm_num
      exact mul_nonneg (mul_nonneg this (Complex.normSq_nonneg z)) (sq_nonneg _)

    have hterm2 :
        4 * (1 - r0 ^ 4) * z.im ≤
          4 * (1 - Complex.normSq alpha) * (1 + Complex.normSq alpha) * z.im := by
      have hbase : 1 - r0 ^ 4 ≤ 1 - (Complex.normSq alpha) ^ 2 := by
        linarith [hs_sq_le]
      have hprod :
          1 - (Complex.normSq alpha) ^ 2 =
            (1 - Complex.normSq alpha) * (1 + Complex.normSq alpha) := by ring
      have hbase' : 1 - r0 ^ 4 ≤ (1 - Complex.normSq alpha) * (1 + Complex.normSq alpha) := by
        simpa [hprod] using hbase
      have : (1 - r0 ^ 4) * z.im ≤ ((1 - Complex.normSq alpha) * (1 + Complex.normSq alpha)) * z.im :=
        mul_le_mul_of_nonneg_right hbase' hzIm0
      have h4 : 0 ≤ (4 : Real) := by norm_num
      have : 4 * ((1 - r0 ^ 4) * z.im) ≤ 4 * (((1 - Complex.normSq alpha) * (1 + Complex.normSq alpha)) * z.im) :=
        mul_le_mul_of_nonneg_left this h4
      simpa [mul_assoc, mul_left_comm, mul_comm] using this

    have hterm3 :
        4 * (1 - r0 ^ 2) ^ 2 ≤ 4 * (1 - Complex.normSq alpha) ^ 2 := by
      have hs_lt_one : Complex.normSq alpha < 1 := lt_of_le_of_lt hs_le hr0sq_lt
      have hA_nonneg : 0 ≤ 1 - r0 ^ 2 := sub_nonneg.2 (le_of_lt hr0sq_lt)
      have hB_nonneg : 0 ≤ 1 - Complex.normSq alpha := sub_nonneg.2 (le_of_lt hs_lt_one)
      have hbase : 1 - r0 ^ 2 ≤ 1 - Complex.normSq alpha := by linarith [hs_le]
      have hsq : (1 - r0 ^ 2) ^ 2 ≤ (1 - Complex.normSq alpha) ^ 2 :=
        (sq_le_sq₀ hA_nonneg hB_nonneg).2 hbase
      have h4 : 0 ≤ (4 : Real) := by norm_num
      have : 4 * ((1 - r0 ^ 2) ^ 2) ≤ 4 * ((1 - Complex.normSq alpha) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq h4
      simpa [mul_assoc] using this

    -- Rewrite the exact identity and compare term-by-term.
    simp [C]
    rw [normSq_dCoeff_sub_normSq_cCoeff alpha z]
    nlinarith [hterm1_nonneg, hterm2, hterm3]

  -- Deduce the `t0` bound on `normSq (denomPole)`.
  have ht0_le :
      t0 ≤ (Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z)) /
        Complex.normSq (cCoeff alpha z) := by
    have h1 :
        C / M ≤ C / Complex.normSq (cCoeff alpha z) :=
      div_le_div_of_nonneg_left (le_of_lt hC_pos) hcsq_pos hc_le_M
    have h2 :
        C / Complex.normSq (cCoeff alpha z) ≤
          (Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z)) /
            Complex.normSq (cCoeff alpha z) :=
      div_le_div_of_nonneg_right hgap_ge (Complex.normSq_nonneg (cCoeff alpha z))
    have : C / M ≤
        (Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z)) /
          Complex.normSq (cCoeff alpha z) := le_trans h1 h2
    simpa [t0] using this

  have hpc :
      Complex.normSq (denomPole alpha z)
        = Complex.normSq (dCoeff alpha z) / Complex.normSq (cCoeff alpha z) := by
    simp [denomPole, div_eq_mul_inv, Complex.normSq_neg]

  have hratio :
      Complex.normSq (dCoeff alpha z) / Complex.normSq (cCoeff alpha z)
        =
          1 + (Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z)) /
            Complex.normSq (cCoeff alpha z) := by
    have hc0 : Complex.normSq (cCoeff alpha z) ≠ 0 := ne_of_gt hcsq_pos
    have hdecomp :
        Complex.normSq (dCoeff alpha z)
          =
            Complex.normSq (cCoeff alpha z) +
              (Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z)) := by ring
    calc
      Complex.normSq (dCoeff alpha z) / Complex.normSq (cCoeff alpha z)
          =
            (Complex.normSq (cCoeff alpha z) +
                (Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z))) /
              Complex.normSq (cCoeff alpha z) := by
                exact congrArg (fun t => t / Complex.normSq (cCoeff alpha z)) hdecomp
      _ =
          Complex.normSq (cCoeff alpha z) / Complex.normSq (cCoeff alpha z)
            + (Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z)) /
                Complex.normSq (cCoeff alpha z) := by
              simpa using
                (add_div (Complex.normSq (cCoeff alpha z))
                  (Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z))
                  (Complex.normSq (cCoeff alpha z)))
      _ =
          1 + (Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z)) /
                Complex.normSq (cCoeff alpha z) := by
              simp [div_self hc0]

  have hp_sq_ge : 1 + t0 ≤ Complex.normSq (denomPole alpha z) := by
    have h1 :
        1 + t0 ≤ 1 +
          (Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z)) /
            Complex.normSq (cCoeff alpha z) := by
      nlinarith [ht0_le]
    have h2 :
        1 +
            (Complex.normSq (dCoeff alpha z) - Complex.normSq (cCoeff alpha z)) /
              Complex.normSq (cCoeff alpha z)
          =
            Complex.normSq (dCoeff alpha z) / Complex.normSq (cCoeff alpha z) := by
      simpa using (Eq.symm hratio)
    have h3 :
        1 + t0 ≤ Complex.normSq (dCoeff alpha z) / Complex.normSq (cCoeff alpha z) := by
      simpa [h2] using h1
    simpa [hpc] using h3

  -- Convert from `normSq` lower bound to `norm` lower bound with `ε = t0/(2+t0)`.
  have hsq : (1 + ε) ^ 2 ≤ Complex.normSq (denomPole alpha z) := by
    have ht : 0 ≤ t0 := le_of_lt ht0_pos
    have h1 : (1 + ε) ^ 2 ≤ 1 + t0 := by
      simpa [ε] using one_add_t_div_two_add_t_sq_le_one_add_t t0 ht
    exact le_trans h1 hp_sq_ge

  have hp_nonneg : 0 ≤ ‖denomPole alpha z‖ := norm_nonneg _
  have : 1 + ε ≤ ‖denomPole alpha z‖ := by
    -- from squares
    have hsq' : (1 + ε) ^ 2 ≤ ‖denomPole alpha z‖ ^ 2 := by
      simpa [Complex.normSq_eq_norm_sq] using hsq
    have h1pos : 0 ≤ 1 + ε := by linarith [le_of_lt hε_pos]
    exact (sq_le_sq₀ h1pos hp_nonneg).1 hsq'
  exact this

/-!
Uniform denominator separation (paper Definition `def:R1_denom_sep`).

We keep the truncated cocycle iterate `w_{k,n}(z)` abstract: the downstream
lemmas only use pointwise bounds on `‖w‖` or pole exclusion, matching the TeX
statements `lem:R1_denom_sep_from_*`.
-/

def DenomSepAt (z : Complex) (alphaSeq : Nat → Complex) (wkn : Nat → Nat → Complex) : Prop :=
  Exists fun δ : Real =>
    0 < δ /\ forall n k : Nat, k < n -> δ <= ‖denomExpr (alphaSeq k) z (wkn k n)‖

lemma denomSepAt_of_strict_inside (z : Complex) (alphaSeq : Nat → Complex) (wkn : Nat → Nat → Complex)
    (q : Real) (hz : 0 < z.im) (hα : forall k : Nat, ‖alphaSeq k‖ < 1)
    (hw : forall n k : Nat, k < n -> ‖wkn k n‖ <= q)
    (hδ : 0 < z.im - 3 * ‖z‖ * q) :
    DenomSepAt z alphaSeq wkn := by
  refine ⟨z.im - 3 * ‖z‖ * q, hδ, ?_⟩
  intro n k hk
  have hbound :
      z.im - 3 * ‖z‖ * q <= ‖denomExpr (alphaSeq k) z (wkn k n)‖ := by
    -- Pointwise reverse triangle inequality + crude coefficient bounds.
    exact denomExpr_norm_ge_im_sub_three_mul (alpha := alphaSeq k) (z := z) (w := wkn k n) q
      hz (hα k) (hw n k hk)
  simpa using hbound

lemma denomSepAt_of_ratio (z : Complex) (alphaSeq : Nat → Complex) (wkn : Nat → Nat → Complex)
    (ρ : Real) (hz : 0 < z.im) (hα : forall k : Nat, ‖alphaSeq k‖ < 1)
    (hρ : 0 <= ρ) (hρlt : ρ < 1) (hw : forall n k : Nat, k < n -> ‖wkn k n‖ <= 1)
    (hcd : forall k : Nat, ‖cCoeff (alphaSeq k) z‖ <= ρ * ‖dCoeff (alphaSeq k) z‖) :
    DenomSepAt z alphaSeq wkn := by
  refine ⟨(1 - ρ) * z.im, ?_, ?_⟩
  · have hpos : 0 < (1 - ρ) := by linarith
    exact mul_pos hpos hz
  · intro n k hk
    have hpos : 0 < (1 - ρ) := by linarith
    have hmain :
        (1 - ρ) * z.im <= ‖denomExpr (alphaSeq k) z (wkn k n)‖ := by
      have h1 :
          (1 - ρ) * ‖dCoeff (alphaSeq k) z‖ <= ‖denomExpr (alphaSeq k) z (wkn k n)‖ :=
        denomExpr_norm_ge_one_sub_rho_mul_dCoeff (alpha := alphaSeq k) (z := z) (w := wkn k n) ρ
          hρ (hcd k) (hw n k hk)
      have h2 : z.im <= ‖dCoeff (alphaSeq k) z‖ :=
        im_le_norm_dCoeff (alphaSeq k) z hz (hα k)
      have hcoef_nonneg : 0 <= (1 - ρ) := le_of_lt hpos
      have h3 : (1 - ρ) * z.im <= (1 - ρ) * ‖dCoeff (alphaSeq k) z‖ :=
        mul_le_mul_of_nonneg_left h2 hcoef_nonneg
      exact le_trans h3 h1
    simpa [mul_assoc] using hmain

lemma denomSepAt_of_pole_exclusion (z : Complex) (alphaSeq : Nat → Complex) (wkn : Nat → Nat → Complex)
    (ε : Real) (hz : 0 < z.im) (hα : forall k : Nat, ‖alphaSeq k‖ < 1)
    (hε : 0 < ε) (hw : forall n k : Nat, k < n -> ‖wkn k n‖ <= 1)
    (hp : forall k : Nat, 1 + ε <= ‖denomPole (alphaSeq k) z‖) :
    DenomSepAt z alphaSeq wkn := by
  refine ⟨(ε / (1 + ε)) * z.im, ?_, ?_⟩
  · have hpos : 0 < (ε / (1 + ε)) := by
      have : 0 < (1 + ε) := by linarith
      exact div_pos hε (by linarith)
    nlinarith
  · intro n k hk
    have hmain :
        (ε / (1 + ε)) * z.im <= ‖denomExpr (alphaSeq k) z (wkn k n)‖ :=
      denomExpr_norm_ge_eps_div_one_add_eps_mul_im (alpha := alphaSeq k) (z := z) (w := wkn k n) ε
        hz (hα k) (hw n k hk) hε (hp k)
    simpa using hmain

end

end LeanV32
