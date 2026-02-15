import Mathlib

namespace LeanV32

noncomputable section

/-!
Basic RH-style predicates for a function `f : ℂ → ℂ`.

These are *paper-level* formulations in the `z`-variable (e.g. for `XiModel z`),
distinct from Mathlib's `_root_.RiemannHypothesis` which is a statement about
zeros of `riemannZeta s` in the `s`-variable.
-/

def ZeroFreeOnUpper (f : Complex → Complex) : Prop :=
  ∀ z : Complex, 0 < z.im → f z ≠ 0

def HasOnlyRealZeros (f : Complex → Complex) : Prop :=
  ∀ z : Complex, f z = 0 → z.im = 0

def RiemannHypothesis (f : Complex → Complex) : Prop :=
  HasOnlyRealZeros f

def ConjugationSymmetric (f : Complex → Complex) : Prop :=
  ∀ z : Complex, f (star z) = star (f z)

def EvenSymmetric (f : Complex → Complex) : Prop :=
  ∀ z : Complex, f (-z) = f z

theorem conj_zero_of_conjugation_symmetric
    {f : Complex → Complex}
    (hConjSymm : ConjugationSymmetric f) :
    ∀ z : Complex, f z = 0 → f (star z) = 0 := by
  intro z hz
  calc
    f (star z) = star (f z) := hConjSymm z
    _ = 0 := by simp [hz]

/-!
Core closure lemma: zero-freeness on `ℂ_+` plus reflection of zeros across conjugation
forces all zeros to lie on the real axis.
-/
theorem rh_from_lstar_core
    {f : Complex → Complex}
    (hZeroFree : ZeroFreeOnUpper f)
    (hConjZero : ∀ z : Complex, f z = 0 → f (star z) = 0) :
    RiemannHypothesis f := by
  intro z hz
  by_cases hzIm : z.im = 0
  · exact hzIm
  · rcases lt_or_gt_of_ne hzIm with hImNeg | hImPos
    · have hzReflected : f (star z) = 0 := hConjZero z hz
      have hImReflectedPos : 0 < (star z).im := by
        simpa using (neg_pos.mpr hImNeg)
      exact False.elim ((hZeroFree (star z) hImReflectedPos) hzReflected)
    · exact False.elim ((hZeroFree z hImPos) hz)

/-!
Alternative closure lemma: zero-freeness on `ℂ_+` plus even symmetry
(`f(-z)=f(z)`) rules out zeros in `ℂ_-`, hence forces all zeros to be real.

This is the xi-route version of the usual `s ↦ 1 - s` functional equation.
-/
theorem rh_from_lstar_core_via_even
    {f : Complex → Complex}
    (hZeroFree : ZeroFreeOnUpper f)
    (hEven : EvenSymmetric f) :
    RiemannHypothesis f := by
  intro z hz
  by_cases hzIm : z.im = 0
  · exact hzIm
  · rcases lt_or_gt_of_ne hzIm with hImNeg | hImPos
    · have hzNeg : f (-z) = 0 := by
        calc
          f (-z) = f z := hEven z
          _ = 0 := hz
      have hImNegPos : 0 < (-z).im := by
        simpa using (neg_pos.mpr hImNeg)
      exact False.elim ((hZeroFree (-z) hImNegPos) hzNeg)
    · exact False.elim ((hZeroFree z hImPos) hz)

end

end LeanV32
