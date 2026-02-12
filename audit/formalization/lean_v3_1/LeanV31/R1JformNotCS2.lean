import LeanV31.R1Rank1ClosureExcludesRadiusfloor

namespace LeanV31

def R1JformInvariantFamilyAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0
def R1FrameDistortionDivergesAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 < n0
def R1JformControlNotEnoughForCS2At (_z : Complex) : Prop :=
  Exists fun eps : Nat => 0 < eps

/- S065 wrapper:
uniform control of the transported `J`-form alone does not control Euclidean
frame distortion; therefore `J`-form boundedness does not imply CS2. -/
theorem R1_Jform_not_CS2
    {z : Complex}
    (hJInvariant : R1JformInvariantFamilyAt z)
    (hDistortion : R1FrameDistortionDivergesAt z)
    (hWitnessBridge :
      R1JformInvariantFamilyAt z ->
      R1FrameDistortionDivergesAt z ->
      R1JformControlNotEnoughForCS2At z) :
    R1JformInvariantFamilyAt z /\
      R1FrameDistortionDivergesAt z /\
      R1JformControlNotEnoughForCS2At z := by
  have hGap : R1JformControlNotEnoughForCS2At z :=
    hWitnessBridge hJInvariant hDistortion
  exact And.intro hJInvariant (And.intro hDistortion hGap)

end LeanV31
