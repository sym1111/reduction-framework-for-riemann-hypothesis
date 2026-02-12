import Mathlib

namespace LeanV31

/- Core objects mirroring v3.1 R1 canonical-chain formulas. -/
noncomputable section

abbrev R1Mat2 := Matrix (Fin 2) (Fin 2) Complex

def R1J : R1Mat2 :=
  !![(0 : Complex), (-1 : Complex); (1 : Complex), (0 : Complex)]

def R1HamiltonianTraceAt (k : Nat) : Real := (k : Real) + 1

def R1PrefixTraceMassAt (N : Nat) : Real :=
  ∑ k ∈ Finset.range N, R1HamiltonianTraceAt k

def R1HamiltonianBlockAt (k : Nat) : R1Mat2 :=
  !![(R1HamiltonianTraceAt k : Complex), (0 : Complex);
     (0 : Complex), (0 : Complex)]

def R1StepLAt (k : Nat) (z : Complex) : R1Mat2 :=
  1 - SMul.smul (z / 2) (R1J * R1HamiltonianBlockAt k)

def R1StepRAt (k : Nat) (z : Complex) : R1Mat2 :=
  1 + SMul.smul (z / 2) (R1J * R1HamiltonianBlockAt k)

def R1StepMAt (k : Nat) (z : Complex) : R1Mat2 :=
  (R1StepRAt k z)⁻¹ * R1StepLAt k z

def R1StepProductAt : Nat -> Complex -> R1Mat2
  | 0, _z => 1
  | n + 1, z => R1StepMAt n z * R1StepProductAt n z

def R1QAt (n : Nat) (z : Complex) : R1Mat2 :=
  (R1StepProductAt n z)⁻¹.conjTranspose * R1J * (R1StepProductAt n z)⁻¹

def R1QtildeAt (n : Nat) (z : Complex) : R1Mat2 :=
  SMul.smul ((1 / (2 * Complex.I : Complex))) (R1QAt n z)

def R1q11At (n : Nat) (z : Complex) : Complex :=
  R1QtildeAt n z 0 0

def R1KappaGaugeAt (n : Nat) (z : Complex) : Real :=
  Real.sqrt (
    Complex.normSq (R1QtildeAt n z 0 0) +
      Complex.normSq (R1QtildeAt n z 1 1))

def R1WeylRadiusFormulaAt (n : Nat) (z : Complex) : Real :=
  Real.sqrt (max 0 (-(R1QtildeAt n z).det.re)) /
    Real.sqrt (Complex.normSq (R1q11At n z))

def R1WeylRadiusAt (n : Nat) (z : Complex) : Real :=
  R1WeylRadiusFormulaAt n z

def R1CanonicalStepResidualAt (n : Nat) (z : Complex) : R1Mat2 :=
  R1StepMAt n z - (R1StepRAt n z)⁻¹ * R1StepLAt n z

def R1RadiusSequenceAt (n : Nat) (z : Complex) : Real :=
  R1WeylRadiusAt n z

end

end LeanV31
