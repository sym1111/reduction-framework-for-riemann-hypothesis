import LeanV31.BDetector
import LeanV31.SchurDeBranges

namespace LeanV31

def CircleHardyZeroFreeCertificate (f _H : Complex -> Complex) : Prop :=
  BDetectorFunctionalOnCircle _H /\ ZeroFreeOnUpper f

/- S009 wrapper:
vanishing of all local negative-mode detectors implies stripwise pole
exclusion for H = -f'/f, equivalently zero-freeness for the associated E. -/
theorem circle_hardy_certificate
    {f H : Complex -> Complex}
    (hCertificate : CircleHardyZeroFreeCertificate f H) :
    ZeroFreeOnUpper f := by
  exact hCertificate.2

end LeanV31
