import LeanV31.LimitPointUniqueLimit
import LeanV31.R1CanonicalFormulaCore

namespace LeanV31

def R1StepTransferDetOneAt (k : Nat) (z : Complex) : Prop :=
  (R1StepMAt k z).det = 1

def R1TruncationTransferDetOneAt (n : Nat) (z : Complex) : Prop :=
  (R1StepProductAt n z).det = 1

/- S038 wrapper:
each one-step transfer matrix is unimodular; products preserve determinant one,
hence every truncation transfer matrix remains unimodular. -/
theorem R1_det1
    {z : Complex}
    (hStepDetOne : forall k : Nat, R1StepTransferDetOneAt k z) :
    (forall k : Nat, R1StepTransferDetOneAt k z) /\
      (forall n : Nat, R1TruncationTransferDetOneAt n z) := by
  have hTruncDetOne : forall n : Nat, R1TruncationTransferDetOneAt n z := by
    intro n
    induction n with
    | zero =>
        simp [R1TruncationTransferDetOneAt, R1StepProductAt]
    | succ n ih =>
        dsimp [R1TruncationTransferDetOneAt, R1StepProductAt]
        rw [Matrix.det_mul]
        calc
          Matrix.det (R1StepMAt n z) * Matrix.det (R1StepProductAt n z) = 1 * 1 := by
            rw [hStepDetOne n, ih]
          _ = 1 := by norm_num
  exact And.intro hStepDetOne hTruncDetOne

end LeanV31
