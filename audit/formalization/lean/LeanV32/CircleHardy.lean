import Mathlib.Analysis.Fourier.AddCircle

namespace LeanV32

noncomputable section

open scoped Real
open AddCircle

/-!
Circle–Hardy (roadmap item (2), paper v3.2 alignment).

This file sets up an `L²`-level notion of “no negative Fourier modes” on the (additive) circle.

TeX intent: for a boundary trace `g ∈ L²(∂𝔻)`, the circle–Hardy certificate is
`P_- g = 0`, i.e. all negative Fourier coefficients vanish.  We represent this as an
explicit predicate on `fourierCoeff`.

Note: the deeper analytic implications (Hardy space, pole-locator rigidity, etc.) are
intentionally *not* asserted here yet; this module is just the strict, kernel-checked
Fourier interface used by those arguments.
-/

abbrev circleT : ℝ :=
  2 * Real.pi

instance : Fact (0 < circleT) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

abbrev Circle :=
  AddCircle circleT

abbrev CircleL2 :=
  MeasureTheory.Lp ℂ 2 (AddCircle.haarAddCircle (T := circleT) (hT := (by infer_instance)))

/-- Circle–Hardy “no negative Fourier modes” certificate: all coefficients at indices `-(n+1)` vanish. -/
def CircleHardyNoNegModes (g : CircleL2) : Prop :=
  ∀ n : ℕ, fourierCoeff (T := circleT) g (- (n + 1 : ℤ)) = 0

lemma fourierCoeff_fourierLp (k n : ℤ) :
    fourierCoeff (T := circleT) (fourierLp (T := circleT) (p := 2) k) n =
      if n = k then (1 : ℂ) else 0 := by
  classical
  -- Use the Hilbert basis representation formula for `fourierBasis`.
  let b : HilbertBasis ℤ ℂ
      (MeasureTheory.Lp ℂ 2 <|
        AddCircle.haarAddCircle (T := circleT) (hT := (by infer_instance))) :=
    fourierBasis (T := circleT) (hT := (by infer_instance))
  have hrepr : b.repr (b k) = lp.single 2 k (1 : ℂ) :=
    HilbertBasis.repr_self b k
  have hcoeff : b.repr (b k) n = if n = k then (1 : ℂ) else 0 := by
    -- Evaluate `hrepr` at `n`.
    have := congrArg (fun f => f n) hrepr
    simpa [lp.single_apply, Pi.single_apply] using this
  -- Convert `b.repr` into `fourierCoeff` and simplify `b k` to `fourierLp 2 k`.
  have hrepl : b.repr (b k) n = fourierCoeff (T := circleT) (b k) n := by
    simpa [b] using (fourierBasis_repr (T := circleT) (hT := (by infer_instance)) (f := b k) (i := n))
  -- Finish.
  have : fourierCoeff (T := circleT) (b k) n = if n = k then (1 : ℂ) else 0 := by
    simpa [hrepl] using hcoeff
  simpa [b] using this

theorem CircleHardyNoNegModes_fourierLp_of_nonneg (k : ℤ) (hk : 0 ≤ k) :
    CircleHardyNoNegModes (fourierLp (T := circleT) (p := 2) k) := by
  intro n
  have h := fourierCoeff_fourierLp (k := k) (n := - (n + 1 : ℤ))
  have hne : (- (n + 1 : ℤ)) ≠ k := by
    intro hEq
    have hlt : (- (n + 1 : ℤ)) < 0 :=
      neg_neg_of_pos (show (0 : ℤ) < (n + 1 : ℤ) from by exact_mod_cast Nat.succ_pos n)
    have : k < 0 := by
      simpa [hEq] using hlt
    exact (not_lt_of_ge hk) this
  have hne' : (-1 + - (n : ℤ)) ≠ k := by
    simpa using hne
  simpa [hne'] using h

/-! ### `P_-` and the negative-mode energy -/

abbrev CircleCoeff :=
  lp (fun _ : ℤ => ℂ) 2

private def circleFourierBasis : HilbertBasis ℤ ℂ CircleL2 :=
  fourierBasis (T := circleT) (hT := (by infer_instance))

private def circleCoeffs (g : CircleL2) : CircleCoeff :=
  circleFourierBasis.repr g

private def circleNegCoeff (c : CircleCoeff) : CircleCoeff :=
  ⟨fun i : ℤ => if i < 0 then c i else 0, by
    -- `Memℓp` for the truncated coefficient sequence: dominated by the original `ℓ²` series.
    have hp : 0 < (2 : ENNReal).toReal := by norm_num
    have hsum : Summable (fun i : ℤ => ‖c i‖ ^ (2 : ENNReal).toReal) :=
      (lp.memℓp c).summable hp
    have hnonneg : ∀ i : ℤ, 0 ≤ ‖(if i < 0 then c i else 0)‖ ^ (2 : ENNReal).toReal := by
      intro i
      exact Real.rpow_nonneg (norm_nonneg _) _
    have hle :
        ∀ i : ℤ,
          ‖(if i < 0 then c i else 0)‖ ^ (2 : ENNReal).toReal ≤ ‖c i‖ ^ (2 : ENNReal).toReal := by
      intro i
      by_cases hi : i < 0 <;> simp [hi]
    refine memℓp_gen (p := (2 : ENNReal)) <|
      (Summable.of_nonneg_of_le (f := fun i : ℤ => ‖c i‖ ^ (2 : ENNReal).toReal)
        (g := fun i : ℤ => ‖(if i < 0 then c i else 0)‖ ^ (2 : ENNReal).toReal)
        hnonneg hle hsum)⟩

/-- The circle–Hardy negative-mode projection `P_- : L² → L²` (defined via Fourier coefficients). -/
def CircleHardyProjNeg (g : CircleL2) : CircleL2 :=
  circleFourierBasis.repr.symm (circleNegCoeff (circleCoeffs g))

/-- Negative-mode energy `E_-(g) := ‖P_- g‖²`. -/
def CircleHardyEnergyNeg (g : CircleL2) : ℝ :=
  ‖CircleHardyProjNeg g‖ ^ 2

theorem CircleHardyProjNeg_eq_zero_iff (g : CircleL2) :
    CircleHardyProjNeg g = 0 ↔ CircleHardyNoNegModes g := by
  constructor
  · intro hP
    -- Push `P_- g = 0` to coefficients.
    have hcoeff0 : circleNegCoeff (circleCoeffs g) = 0 := by
      have := congrArg circleFourierBasis.repr hP
      simpa [CircleHardyProjNeg, circleCoeffs] using this
    intro n
    have hneg : (Int.negSucc n : ℤ) < 0 := Int.negSucc_lt_zero n
    have hcn : circleCoeffs g (Int.negSucc n) = 0 := by
      have := congrArg (fun c : CircleCoeff => c (Int.negSucc n)) hcoeff0
      simpa [circleNegCoeff, circleCoeffs, hneg] using this
    -- Convert from `repr` to `fourierCoeff`.
    have hrepr :
        circleFourierBasis.repr g (Int.negSucc n) =
          fourierCoeff (T := circleT) g (Int.negSucc n) := by
      simpa [circleFourierBasis] using
        (fourierBasis_repr (T := circleT) (hT := (by infer_instance)) (f := g) (i := Int.negSucc n))
    have hFour : fourierCoeff (T := circleT) g (Int.negSucc n) = 0 := by
      simpa [circleCoeffs, hrepr] using hcn
    have : (Int.negSucc n : ℤ) = (- (n + 1 : ℤ)) := by simp [Int.negSucc_eq]
    simpa [this] using hFour
  · intro hNoNeg
    -- Show the truncated coefficient sequence is identically zero.
    have hcoeff0 : circleNegCoeff (circleCoeffs g) = 0 := by
      ext i
      by_cases hi : i < 0
      · obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hi
        have hrepr :
            circleFourierBasis.repr g (Int.negSucc n) =
              fourierCoeff (T := circleT) g (Int.negSucc n) := by
          simpa [circleFourierBasis] using
            (fourierBasis_repr (T := circleT) (hT := (by infer_instance)) (f := g) (i := Int.negSucc n))
        have hFour : fourierCoeff (T := circleT) g (Int.negSucc n) = 0 := by
          have : (Int.negSucc n : ℤ) = (- (n + 1 : ℤ)) := by simp [Int.negSucc_eq]
          simpa [this] using hNoNeg n
        simp [circleNegCoeff, hi, circleCoeffs, hrepr, hFour]
      · simp [circleNegCoeff, hi]
    -- Coefficients are zero ⇒ projection is zero.
    simpa [CircleHardyProjNeg, circleCoeffs, hcoeff0]

theorem CircleHardyEnergyNeg_eq_zero_iff (g : CircleL2) :
    CircleHardyEnergyNeg g = 0 ↔ CircleHardyNoNegModes g := by
  constructor
  · intro hE
    have hnorm : ‖CircleHardyProjNeg g‖ = 0 := by
      exact (sq_eq_zero_iff.mp hE)
    have hP : CircleHardyProjNeg g = 0 := by
      exact norm_eq_zero.mp hnorm
    exact (CircleHardyProjNeg_eq_zero_iff g).1 hP
  · intro hNoNeg
    have hP : CircleHardyProjNeg g = 0 := (CircleHardyProjNeg_eq_zero_iff g).2 hNoNeg
    simp [CircleHardyEnergyNeg, hP]

private lemma circleCoeffs_apply (g : CircleL2) (i : ℤ) :
    circleCoeffs g i = fourierCoeff (T := circleT) g i := by
  simpa [circleCoeffs, circleFourierBasis] using
    (fourierBasis_repr (T := circleT) (hT := (by infer_instance)) (f := g) (i := i))

theorem CircleHardyProjNeg_fourierCoeff (g : CircleL2) (i : ℤ) :
    fourierCoeff (T := circleT) (CircleHardyProjNeg g) i =
      if i < 0 then fourierCoeff (T := circleT) g i else 0 := by
  -- Unfold through the Hilbert-basis coefficient representation.
  have hrepr : circleCoeffs (CircleHardyProjNeg g) i = circleNegCoeff (circleCoeffs g) i := by
    simp [CircleHardyProjNeg, circleCoeffs]
  -- Convert both sides from `repr` coefficients to `fourierCoeff`.
  have hcoeffP :
      circleCoeffs (CircleHardyProjNeg g) i = fourierCoeff (T := circleT) (CircleHardyProjNeg g) i := by
    simpa [circleCoeffs, circleFourierBasis] using
      (fourierBasis_repr (T := circleT) (hT := (by infer_instance)) (f := CircleHardyProjNeg g)
        (i := i))
  have hcoeffG :
      circleCoeffs g i = fourierCoeff (T := circleT) g i := by
    simpa using circleCoeffs_apply (g := g) (i := i)
  -- Finish by rewriting the truncated coefficient function.
  simp [circleNegCoeff, hcoeffG, hcoeffP] at hrepr
  simpa using hrepr

theorem CircleHardyEnergyNeg_eq_tsum_sq_fourierCoeff (g : CircleL2) :
    CircleHardyEnergyNeg g =
      ∑' i : ℤ, ‖if i < 0 then fourierCoeff (T := circleT) g i else 0‖ ^ 2 := by
  classical
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  -- Move the norm computation to coefficient space using the isometry `repr`.
  have hnorm :
      ‖CircleHardyProjNeg g‖ = ‖circleNegCoeff (circleCoeffs g)‖ := by
    simp [CircleHardyProjNeg]
  -- Express the squared norm of the coefficient vector as a `tsum` of squared pointwise norms.
  have htsum :
      ‖circleNegCoeff (circleCoeffs g)‖ ^ (2 : ENNReal).toReal =
        ∑' i : ℤ, ‖circleNegCoeff (circleCoeffs g) i‖ ^ (2 : ENNReal).toReal := by
    exact lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) hp (circleNegCoeff (circleCoeffs g))
  -- Combine the isometry, the `lp` norm formula, and rewrite coefficients back to `fourierCoeff`.
  have hpow : ‖circleNegCoeff (circleCoeffs g)‖ ^ 2 = ∑' i : ℤ, ‖circleNegCoeff (circleCoeffs g) i‖ ^ 2 := by
    -- Convert nat-powers to `Real.rpow` at exponent 2, then apply `htsum`.
    calc
      ‖circleNegCoeff (circleCoeffs g)‖ ^ 2
          = ‖circleNegCoeff (circleCoeffs g)‖ ^ (2 : ENNReal).toReal := by
              norm_cast
      _ = ∑' i : ℤ, ‖circleNegCoeff (circleCoeffs g) i‖ ^ (2 : ENNReal).toReal := htsum
      _ = ∑' i : ℤ, ‖circleNegCoeff (circleCoeffs g) i‖ ^ 2 := by
            norm_cast
  -- Final simplification of the coefficient truncation and the `repr`-to-`fourierCoeff` bridge.
  -- Rewrite the `CircleHardyProjNeg` norm to coefficient-space and apply `hpow`.
  have :
      CircleHardyEnergyNeg g = ∑' i : ℤ, ‖circleNegCoeff (circleCoeffs g) i‖ ^ 2 := by
    simp [CircleHardyEnergyNeg, hnorm, hpow]
  -- Expand the truncation and convert coefficients to `fourierCoeff`.
  simpa [circleNegCoeff, circleCoeffs_apply] using this

end

end LeanV32
