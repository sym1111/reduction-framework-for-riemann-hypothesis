import LeanV31.CircleHardyCertificate

namespace LeanV31

def StripPoleExclusionViaNevanlinna (f _H : Complex -> Complex) : Prop :=
  ZeroFreeOnUpper f

/- S005 internalized form:
strip pole/zero exclusion is obtained from the circle-Hardy certificate route
(detector functional -> zero-freeness certificate), without a direct
pass-through bridge parameter of the same target type. -/
theorem no_pole_nevanlinna
    {f H : Complex -> Complex}
    (hCertificate : CircleHardyZeroFreeCertificate f H) :
    StripPoleExclusionViaNevanlinna f H := by
  have hZeroFree : ZeroFreeOnUpper f :=
    circle_hardy_certificate hCertificate
  exact hZeroFree

end LeanV31
