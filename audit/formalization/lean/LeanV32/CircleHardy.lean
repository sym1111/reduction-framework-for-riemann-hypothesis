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

end

end LeanV32
