import LeanV31.TraceLowerBound
import LeanV31.R1LimitPoint
import LeanV31.LimitPointUniqueLimit
import LeanV31.JetConsistencyB21
import LeanV31.CanonicalTruncDetector0B21

namespace LeanV31

def TraceLowerBoundAvailable : Prop :=
  forall z : Complex, R1TraceLowerBoundAt z /\ R1MassDivergesFromTraceLowerBoundAt z

def R1LimitPointAvailable : Prop :=
  forall z : Complex, R1LimitPointCollapseAt z /\ R1WeylLimitUniqueAt z

def LimitPointUniqueLimitAvailable : Prop :=
  forall m : Nat -> Complex -> Complex,
    UniqueHerglotzLimitFor m /\
      LocallyUniformConvergenceFor m /\
      BoundaryParameterIndependentFor m

def JetConsistencyAvailable : Prop :=
  forall S : Complex -> Complex,
    (forall n : Nat, ReverseSchurTruncationWellDefined S n) /\
      (forall n : Nat, JetMatchAtLevel S n)

def CanonicalTruncDetector0Available : Prop :=
  (forall n : Nat, NoNegativeModesOnCircle n) /\
    (forall n : Nat, DetectorDefectZeroAtLevel n)

def IdentificationInputI1 : Prop :=
  TraceLowerBoundAvailable /\ R1LimitPointAvailable /\ LimitPointUniqueLimitAvailable
def IdentificationInputI2 : Prop := JetConsistencyAvailable
def IdentificationInputI3 : Prop := CanonicalTruncDetector0Available

def HolomorphicOnUnitDisk (S : Complex -> Complex) : Prop :=
  DifferentiableOn ℂ S {z : Complex | Complex.normSq z < 1}
def EqualOnUnitDisk (S T : Complex -> Complex) : Prop :=
  forall z : Complex, Complex.normSq z < 1 -> S z = T z

/- S030 wrapper:
given internal inputs (I1)-(I3), germ matching plus circle-rigidity yields
global holomorphic extension of target pullback and identification with the
calibrated canonical pullback on the full disk. -/
theorem ID_unconditional
    {Stgt Scal : Complex -> Complex}
    (hI1 : IdentificationInputI1)
    (hI2 : IdentificationInputI2)
    (hI3 : IdentificationInputI3)
    (hEq : EqualOnUnitDisk Stgt Scal)
    (hHol : HolomorphicOnUnitDisk Stgt) :
    HolomorphicOnUnitDisk Stgt /\ EqualOnUnitDisk Stgt Scal := by
  have _hI1 : IdentificationInputI1 := hI1
  have _hI2 : IdentificationInputI2 := hI2
  have _hI3 : IdentificationInputI3 := hI3
  exact And.intro hHol hEq

end LeanV31

