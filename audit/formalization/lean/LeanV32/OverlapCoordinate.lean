import Mathlib
import LeanV32.HAlpha

namespace LeanV32

noncomputable section

/-!
Paper v3.2: overlap coordinate identity.

TeX label: `lem:R1_overlap_coordinate`, equation `eq:R1_overlap_coordinate_formula`.

We work with explicit coordinates on `Fin 2 → Complex` to avoid relying on any
particular `InnerProductSpace` instance.
-/

open scoped ComplexConjugate

-- Standard `ℂ^2` inner product: ⟪x,y⟫ = Σ conj(xᵢ) * yᵢ.
def inner2 (x y : Fin 2 → Complex) : Complex :=
  ∑ i : Fin 2, conj (x i) * y i

lemma overlap_coordinate_normSq (alpha : Complex) (y : Fin 2 → Complex) :
    Complex.normSq (inner2 (uVec alpha) y)
      = Complex.normSq (y 0 - alpha * y 1) / (1 + Complex.normSq alpha) := by
  classical
  -- Expand the inner product and simplify the conjugates.
  have hinner :
      inner2 (uVec alpha) y
        = (y 0 - alpha * y 1) / (Real.sqrt (1 + Complex.normSq alpha) : Real) := by
    -- Write `⟪u,y⟫ = conj(u₀) y₀ + conj(u₁) y₁` and simplify `conj`.
    simp [inner2, uVec, Fin.sum_univ_two, div_eq_mul_inv, sub_eq_add_neg, add_mul,
      mul_assoc, mul_left_comm, mul_comm]

  have hsqrt :
      Complex.normSq ((Real.sqrt (1 + Complex.normSq alpha) : Real) : Complex)
        = (1 + Complex.normSq alpha) := by
    have hnonneg : 0 <= (1 + Complex.normSq alpha) := by
      nlinarith [Complex.normSq_nonneg alpha]
    -- `normSq` of a real is the square; `sqrt` squared gives the original nonnegative value.
    simp [Complex.normSq_ofReal, Real.mul_self_sqrt hnonneg]

  calc
    Complex.normSq (inner2 (uVec alpha) y)
        = Complex.normSq ((y 0 - alpha * y 1) / (Real.sqrt (1 + Complex.normSq alpha) : Real)) := by
          simp [hinner]
    _ = Complex.normSq (y 0 - alpha * y 1) /
          Complex.normSq ((Real.sqrt (1 + Complex.normSq alpha) : Real) : Complex) := by
          simp
    _ = Complex.normSq (y 0 - alpha * y 1) / (1 + Complex.normSq alpha) := by
          simp [hsqrt]

end

end LeanV32
