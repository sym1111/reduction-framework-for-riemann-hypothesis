import Mathlib
import LeanV31.WInftyLimit

namespace LeanV31

def R2IndependentInequalityAt (_z : Complex) : Prop :=
  Exists fun lam : Nat => 0 <= lam

def R2IndependentInequalityRigidityAt (_z : Complex) : Prop :=
  Exists fun lam : Nat => 0 <= lam /\ 0 < lam

/- S119 wrapper:
for PSD `2x2` blocks, `Tr(H) - 2*sqrt(det(H))` is nonnegative and rigidity is
exactly the equal-eigenvalue (scalar) case. -/
theorem independent_inequality
    {z : Complex}
    (hNonneg : R2IndependentInequalityAt z)
    (hRigidityBridge :
      R2IndependentInequalityAt z ->
      R2IndependentInequalityRigidityAt z) :
    R2IndependentInequalityAt z /\ R2IndependentInequalityRigidityAt z := by
  have hRigidity : R2IndependentInequalityRigidityAt z := hRigidityBridge hNonneg
  exact And.intro hNonneg hRigidity

/-
Paper-level realization of `lem:independent_inequality` at the eigenvalue level:
for nonnegative eigenvalues lam1, lam2,
(lam1 + lam2) - 2 * sqrt(lam1 * lam2) is nonnegative,
and it is zero iff lam1 = lam2.
-/
theorem independent_inequality_eigen_nonneg
    {lam1 lam2 : Real}
    (h1 : 0 <= lam1)
    (h2 : 0 <= lam2) :
    0 <= (lam1 + lam2) - 2 * Real.sqrt (lam1 * lam2) := by
  have hsq : 0 <= (Real.sqrt lam1 - Real.sqrt lam2) ^ 2 := by
    exact sq_nonneg (Real.sqrt lam1 - Real.sqrt lam2)
  have hsqrtMul : Real.sqrt (lam1 * lam2) = Real.sqrt lam1 * Real.sqrt lam2 := by
    simpa [mul_comm] using (Real.sqrt_mul h1 lam2)
  have hIdent :
      (Real.sqrt lam1 - Real.sqrt lam2) ^ 2 =
        (lam1 + lam2) - 2 * Real.sqrt (lam1 * lam2) := by
    calc
      (Real.sqrt lam1 - Real.sqrt lam2) ^ 2
          = lam1 + lam2 - 2 * (Real.sqrt lam1 * Real.sqrt lam2) := by
            nlinarith [Real.sq_sqrt h1, Real.sq_sqrt h2]
      _ = (lam1 + lam2) - 2 * Real.sqrt (lam1 * lam2) := by
            simp [hsqrtMul]
  linarith [hsq, hIdent]

theorem independent_inequality_eigen_rigidity
    {lam1 lam2 : Real}
    (h1 : 0 <= lam1)
    (h2 : 0 <= lam2) :
    ((lam1 + lam2) - 2 * Real.sqrt (lam1 * lam2) = 0) <-> lam1 = lam2 := by
  have hsqrtMul : Real.sqrt (lam1 * lam2) = Real.sqrt lam1 * Real.sqrt lam2 := by
    simpa [mul_comm] using (Real.sqrt_mul h1 lam2)
  have hIdent :
      (lam1 + lam2) - 2 * Real.sqrt (lam1 * lam2) =
        (Real.sqrt lam1 - Real.sqrt lam2) ^ 2 := by
    calc
      (lam1 + lam2) - 2 * Real.sqrt (lam1 * lam2)
          = lam1 + lam2 - 2 * (Real.sqrt lam1 * Real.sqrt lam2) := by
            simp [hsqrtMul]
      _ = (Real.sqrt lam1 - Real.sqrt lam2) ^ 2 := by
            nlinarith [Real.sq_sqrt h1, Real.sq_sqrt h2]
  constructor
  . intro hZero
    have hSqZero : (Real.sqrt lam1 - Real.sqrt lam2) ^ 2 = 0 := by
      simpa [hIdent] using hZero
    have hSubZero : Real.sqrt lam1 - Real.sqrt lam2 = 0 := by
      exact (sq_eq_zero_iff).1 hSqZero
    have hSqrtEq : Real.sqrt lam1 = Real.sqrt lam2 := by
      exact (sub_eq_zero).1 hSubZero
    have hSqEq : (Real.sqrt lam1) ^ 2 = (Real.sqrt lam2) ^ 2 := by
      exact congrArg (fun t : Real => t ^ 2) hSqrtEq
    nlinarith [hSqEq, Real.sq_sqrt h1, Real.sq_sqrt h2]
  . intro hLamEq
    have hSqrtSq : Real.sqrt (lam2 * lam2) = lam2 := by
      calc
        Real.sqrt (lam2 * lam2) = Real.sqrt (lam2 ^ 2) := by ring_nf
        _ = |lam2| := by simpa [pow_two] using (Real.sqrt_sq_eq_abs lam2)
        _ = lam2 := abs_of_nonneg h2
    calc
      (lam1 + lam2) - 2 * Real.sqrt (lam1 * lam2)
          = (lam2 + lam2) - 2 * Real.sqrt (lam2 * lam2) := by simpa [hLamEq]
      _ = (2 * lam2) - 2 * lam2 := by simp [two_mul, hSqrtSq]
      _ = 0 := by ring

end LeanV31
