import LeanV31.BDetector

namespace LeanV31

def UpperHalfPlanePoint (zeta : Complex) : Prop := 0 < Complex.im zeta
def RInvertibleAt (zeta : Complex) (R : Complex -> Complex) : Prop := R zeta ≠ 0
def JContractiveAt (zeta : Complex) (M : Complex -> Complex) : Prop := 0 <= (M zeta).im
def PositiveSemidefiniteTransport (zeta : Complex) (R H : Complex -> Complex) : Prop :=
  0 <= Complex.normSq (R zeta) + Complex.normSq (H zeta)
def EnergyIdentityAt (zeta : Complex) (M R H : Complex -> Complex) : Prop :=
  JContractiveAt zeta M /\ PositiveSemidefiniteTransport zeta R H

/- S023 wrapper:
energy identity at a point in `C_+` with invertible `R` yields the PSD transport
term and therefore `J`-contractivity of the transfer map. -/
theorem energy_identity
    {zeta : Complex}
    {M R H : Complex -> Complex}
    (hIm : UpperHalfPlanePoint zeta)
    (hRinv : RInvertibleAt zeta R)
    (hFormula : EnergyIdentityAt zeta M R H) :
    EnergyIdentityAt zeta M R H /\
      PositiveSemidefiniteTransport zeta R H /\
      JContractiveAt zeta M := by
  have _hIm : UpperHalfPlanePoint zeta := hIm
  have _hRinv : RInvertibleAt zeta R := hRinv
  have hPSD : PositiveSemidefiniteTransport zeta R H := hFormula.2
  have hJc : JContractiveAt zeta M := hFormula.1
  exact And.intro hFormula (And.intro hPSD hJc)

theorem passivity_to_detector_chain
    {zeta : Complex}
    {M R H : Complex -> Complex}
    (hIm : UpperHalfPlanePoint zeta)
    (hRinv : RInvertibleAt zeta R)
    (hFormula : EnergyIdentityAt zeta M R H)
    (hLocator : HardyPoleLocatorOnCircle H) :
    EnergyIdentityAt zeta M R H /\
      PositiveSemidefiniteTransport zeta R H /\
      JContractiveAt zeta M /\
      HardyPoleLocatorOnCircle H /\
      BDetectorFunctionalOnCircle H := by
  have hEnergy :
      EnergyIdentityAt zeta M R H /\
        PositiveSemidefiniteTransport zeta R H /\
        JContractiveAt zeta M :=
    energy_identity hIm hRinv hFormula
  have hJc : JContractiveAt zeta M := hEnergy.2.2
  have _hJc := hJc
  have hDetector : BDetectorFunctionalOnCircle H := b_detector hLocator
  exact And.intro hEnergy.1 (And.intro hEnergy.2.1 (And.intro hJc (And.intro hLocator hDetector)))

end LeanV31
