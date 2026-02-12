import LeanV31.HardyPoleLocator

namespace LeanV31

def BDetectorFunctionalOnCircle (H : Complex -> Complex) : Prop :=
  NegativeModesVanishOnCircle H

/- S008 wrapper:
the b-detector functional is obtained as the operational certificate derived
from the circle Hardy pole-locator identity. -/
theorem b_detector
    {H : Complex -> Complex}
    (hLocator : HardyPoleLocatorOnCircle H) :
    BDetectorFunctionalOnCircle H := by
  exact hLocator

end LeanV31
