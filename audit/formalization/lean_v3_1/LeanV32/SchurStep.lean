import Mathlib

namespace LeanV32

noncomputable section

/-!
Paper v3.2: elementary Schur one-step map on the disk.
-/

open scoped ComplexConjugate

def schurStep (alpha lam w : Complex) : Complex :=
  (alpha + lam * w) / (1 + conj alpha * lam * w)

end

end LeanV32
