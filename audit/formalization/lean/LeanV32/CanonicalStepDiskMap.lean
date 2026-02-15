import Mathlib
import LeanV32.Cayley
import LeanV32.HAlpha

namespace LeanV32

noncomputable section

-- This file performs a large symbolic simplification; increase the heartbeat budget locally.
set_option maxHeartbeats 4000000

/-!
Paper v3.2: canonical one-step disk map (explicit PGL representative).

TeX labels:
- `lem:R1_step_disk_map_pgl`
- `eq:R1_step_disk_map_formula`

We implement the statement in an algebraic, division-free way: we prove the
cross-multiplied identity of the induced disk Mobius maps.
-/

open scoped ComplexConjugate

-- Mobius action of a `2x2` matrix on `w` (total function; use cross-multiplication for rigor).
def mobius (A : Mat2) (w : Complex) : Complex :=
  (A 0 0 * w + A 0 1) / (A 1 0 * w + A 1 1)

def num (A : Mat2) (w : Complex) : Complex :=
  A 0 0 * w + A 0 1

def den (A : Mat2) (w : Complex) : Complex :=
  A 1 0 * w + A 1 1

-- Cayley value map `C_val(m) = (m - i) / (m + i)` as a matrix.
def CvalMat : Mat2 :=
  !![(1 : Complex), (-Complex.I); (1 : Complex), (Complex.I)]

-- Inverse Cayley value map `C_val_inv(w) = i (1+w)/(1-w)` as a matrix.
def CvalInvMat : Mat2 :=
  !![(Complex.I), (Complex.I); (-1 : Complex), (1 : Complex)]

lemma mobius_Cval (m : Complex) : mobius CvalMat m = C_val m := by
  simp [mobius, CvalMat, C_val, sub_eq_add_neg]

lemma mobius_CvalInv (w : Complex) : mobius CvalInvMat w = C_val_inv w := by
  -- `simp` needs help to see `-w + 1 = 1 + (-w)`.
  simp [mobius, CvalInvMat, C_val_inv, sub_eq_add_neg, mul_add, add_mul, div_eq_mul_inv, add_comm]

-- `A(z) := (z/2) J H(alpha)` in the paper.
def stepA (alpha z : Complex) : Mat2 :=
  (z / 2 : Complex) • (J * Halpha alpha)

def stepL (alpha z : Complex) : Mat2 :=
  (1 : Mat2) - stepA alpha z

def stepR (alpha z : Complex) : Mat2 :=
  (1 : Mat2) + stepA alpha z

-- Adjugate for `2x2` matrices.
def adj2 (M : Mat2) : Mat2 :=
  !![M 1 1, -M 0 1; -M 1 0, M 0 0]

-- PGL-representative for `R(z)^{-1} L(z)` (scalar factor ignored in Mobius action).
def stepMpgl (alpha z : Complex) : Mat2 :=
  adj2 (stepR alpha z) * stepL alpha z

-- Conjugated disk map matrix: `C_val * stepMpgl * C_val_inv`.
def conjMat (alpha z : Complex) : Mat2 :=
  CvalMat * stepMpgl alpha z * CvalInvMat

-- Explicit PGL representative from TeX `eq:R1_step_disk_map_formula`.
def diskMat (alpha z : Complex) : Mat2 :=
  let s : Complex := alpha * conj alpha
  !![((1 + s) * z + (2 * Complex.I) * (s - 1)),
     (z * (1 - s) + Complex.I * z * (alpha + conj alpha));
     (z * (s - 1) + Complex.I * z * (alpha + conj alpha)),
     (-(1 + s) * z + (2 * Complex.I) * (s - 1))]

lemma conjMat_eq_smul_diskMat (alpha z : Complex) (hα : denomAlpha alpha ≠ 0) :
    conjMat alpha z = ((-1 : Complex) / denomAlpha alpha) • diskMat alpha z := by
  classical
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjMat, diskMat, stepMpgl, stepL, stepR, stepA, adj2,
      CvalMat, CvalInvMat, J, Halpha,
      Matrix.mul_apply, Matrix.vecCons, Matrix.vecEmpty,
      Fin.sum_univ_two] <;>
    field_simp [hα] <;>
    simp [denomAlpha] <;>
    ring_nf <;>
    simp <;>
    ring_nf

theorem canonical_step_is_disk_map_cross (alpha z w : Complex)
    (hα : denomAlpha alpha ≠ 0) :
    num (conjMat alpha z) w * den (diskMat alpha z) w
      = num (diskMat alpha z) w * den (conjMat alpha z) w := by
  classical
  have hmat : conjMat alpha z = ((-1 : Complex) / denomAlpha alpha) • diskMat alpha z :=
    conjMat_eq_smul_diskMat alpha z hα
  -- Reduce to commutativity: scaling a PGL representative does not change its Möbius action.
  simp [hmat, num, den, diskMat, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm]
  ring_nf

end

end LeanV32
