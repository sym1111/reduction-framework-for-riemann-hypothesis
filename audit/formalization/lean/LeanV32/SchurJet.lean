import Mathlib
import LeanV32.SchurStep
import LeanV32.HAlpha

namespace LeanV32

noncomputable section

/-!
Jet-level algebra for the Schur one-step map

This file formalizes the exact cross-multiplied identity behind the "jet propagation" step
used in the manuscript's target-identification layer (Schur recursion consistency).

TeX reference: the denominator computation in the proof fragment around `eq:jet_match_strong`.
-/

open scoped ComplexConjugate

lemma schurStep_sub (gamma lam A B : Complex)
    (hA : 1 + conj gamma * lam * A ≠ 0)
    (hB : 1 + conj gamma * lam * B ≠ 0) :
    schurStep gamma lam A - schurStep gamma lam B =
      lam * (A - B) * denomAlpha gamma /
        ((1 + conj gamma * lam * A) * (1 + conj gamma * lam * B)) := by
  -- Pure algebra: use the standard `div_sub_div` normal form, then close by `ring`.
  unfold schurStep
  have hdiv :
      (gamma + lam * A) / (1 + conj gamma * lam * A) - (gamma + lam * B) / (1 + conj gamma * lam * B) =
        ((gamma + lam * A) * (1 + conj gamma * lam * B) - (1 + conj gamma * lam * A) * (gamma + lam * B)) /
          ((1 + conj gamma * lam * A) * (1 + conj gamma * lam * B)) := by
    simpa using
      (div_sub_div (gamma + lam * A) (gamma + lam * B) hA hB)
  have hnum :
      (gamma + lam * A) * (1 + conj gamma * lam * B) - (1 + conj gamma * lam * A) * (gamma + lam * B) =
        lam * (A - B) * denomAlpha gamma := by
    unfold denomAlpha
    ring
  -- Substitute the normalized division form, then replace the numerator.
  simp [hdiv, hnum]

lemma schurStep_sub_mul (gamma lam A B : Complex)
    (hA : 1 + conj gamma * lam * A ≠ 0)
    (hB : 1 + conj gamma * lam * B ≠ 0) :
    (schurStep gamma lam A - schurStep gamma lam B) *
        ((1 + conj gamma * lam * A) * (1 + conj gamma * lam * B)) =
      lam * (A - B) * denomAlpha gamma := by
  have h := schurStep_sub (gamma := gamma) (lam := lam) (A := A) (B := B) hA hB
  set D : Complex := (1 + conj gamma * lam * A) * (1 + conj gamma * lam * B)
  have hD : D ≠ 0 := by
    simpa [D] using (mul_ne_zero hA hB)
  -- Multiply the exact subtraction identity by the (nonzero) product denominator.
  calc
    (schurStep gamma lam A - schurStep gamma lam B) * D
        = (lam * (A - B) * denomAlpha gamma / D) * D := by
            simp [D, h]
    _ = lam * (A - B) * denomAlpha gamma := by
          -- `x / D * D = x` for `D ≠ 0` (avoid rewriting by `mul_eq_mul_left_iff`).
          have hInv : D⁻¹ * D = (1 : Complex) := inv_mul_cancel₀ hD
          simp [div_eq_mul_inv, mul_assoc, hInv]

end

end LeanV32
