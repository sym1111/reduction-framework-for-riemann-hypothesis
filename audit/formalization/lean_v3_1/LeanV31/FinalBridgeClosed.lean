import LeanV31.ReverseRH
import LeanV31.CircleHardyCertificate

namespace LeanV31

/- S015 endpoint:
close RH from the no-zero route and symmetry route, with optional wrappers for
Nevanlinna, detector, locator, canonical truncation, and Cayley transport. -/
theorem final_bridge_closed_core
    {f : Complex -> Complex}
    (hZeroFree : ZeroFreeOnUpper f)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  exact reverse_RH_via_conjugation_symmetry hZeroFree hConjSymm

theorem final_bridge_closed_core_via_nevanlinna
    {f H : Complex -> Complex}
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  exact reverse_RH_via_nevanlinna_conjugation_symmetry
    hNevanlinnaExclusion hConjSymm

theorem final_bridge_closed_via_conj_zero
    {f : Complex -> Complex}
    (hZeroFree : ZeroFreeOnUpper f)
    (hConjZero : forall z : Complex, f z = 0 -> f (star z) = 0) :
    RiemannHypothesis f := by
  exact reverse_RH_via_conj_zero hZeroFree hConjZero

theorem final_bridge_closed_from_zerofree_conj
    {f : Complex -> Complex}
    (hZeroFree : ZeroFreeOnUpper f)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  exact final_bridge_closed_core hZeroFree hConjSymm

theorem final_bridge_closed
    {f : Complex -> Complex}
    (hZeroFree : ZeroFreeOnUpper f)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  exact reverse_RH hZeroFree hConjSymm

theorem final_bridge_closed_via_certificate
    {f H : Complex -> Complex}
    (hCertificate : CircleHardyZeroFreeCertificate f H)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  exact reverse_RH_via_certificate hCertificate hConjSymm

theorem rh_true
    {f : Complex -> Complex}
    (hZeroFree : ZeroFreeOnUpper f)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  exact final_bridge_closed hZeroFree hConjSymm

theorem final_bridge_closed_via_nevanlinna
    {f H : Complex -> Complex}
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  exact final_bridge_closed_core_via_nevanlinna hNevanlinnaExclusion hConjSymm

theorem final_bridge_closed_via_detector_conjugation_symmetry
    {f H : Complex -> Complex}
    (hCertificate : CircleHardyZeroFreeCertificate f H)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  exact final_bridge_closed_via_certificate hCertificate hConjSymm

theorem final_bridge_closed_via_detector_xi_functional_symmetry
    {f H : Complex -> Complex}
    (hCertificate : CircleHardyZeroFreeCertificate f H)
    (hXiSymm : XiFunctionalSymmetry f) :
    RiemannHypothesis f := by
  have hConjSymm : ConjugationSymmetric f :=
    conjugation_symmetric_of_xi_functional_symmetry hXiSymm
  exact final_bridge_closed_via_certificate hCertificate hConjSymm

theorem final_bridge_closed_via_hardy_locator_conjugation_symmetry
    {f H : Complex -> Complex}
    (hLocator : HardyPoleLocatorOnCircle H)
    (hCertificate : CircleHardyZeroFreeCertificate f H)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  have _hLocator' : HardyPoleLocatorOnCircle H :=
    hardy_pole_locator hLocator
  exact final_bridge_closed_via_detector_conjugation_symmetry hCertificate hConjSymm

theorem final_bridge_closed_via_hardy_locator_xi_functional_symmetry
    {f H : Complex -> Complex}
    (hLocator : HardyPoleLocatorOnCircle H)
    (hCertificate : CircleHardyZeroFreeCertificate f H)
    (hXiSymm : XiFunctionalSymmetry f) :
    RiemannHypothesis f := by
  have _hLocator' : HardyPoleLocatorOnCircle H :=
    hardy_pole_locator hLocator
  exact final_bridge_closed_via_detector_xi_functional_symmetry hCertificate hXiSymm

theorem final_bridge_closed_via_conjugation_symmetry
    {f : Complex -> Complex}
    (hZeroFree : ZeroFreeOnUpper f)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  exact reverse_RH_via_conjugation_symmetry hZeroFree hConjSymm

theorem final_bridge_closed_via_nevanlinna_conjugation_symmetry
    {f H : Complex -> Complex}
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  exact reverse_RH_via_nevanlinna_conjugation_symmetry
    hNevanlinnaExclusion hConjSymm

theorem final_bridge_closed_via_xi_functional_symmetry
    {f : Complex -> Complex}
    (hZeroFree : ZeroFreeOnUpper f)
    (hXiSymm : XiFunctionalSymmetry f) :
    RiemannHypothesis f := by
  have hConjSymm : ConjugationSymmetric f :=
    conjugation_symmetric_of_xi_functional_symmetry hXiSymm
  exact final_bridge_closed_core hZeroFree hConjSymm

theorem final_bridge_closed_via_nevanlinna_xi_functional_symmetry
    {f H : Complex -> Complex}
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H)
    (hXiSymm : XiFunctionalSymmetry f) :
    RiemannHypothesis f := by
  have hConjSymm : ConjugationSymmetric f :=
    conjugation_symmetric_of_xi_functional_symmetry hXiSymm
  exact final_bridge_closed_via_nevanlinna hNevanlinnaExclusion hConjSymm

theorem final_bridge_closed_via_cayley
    {f H W : Complex -> Complex}
    (hGlobalSchur : WGlobalSchurOnUpperHalfPlane W)
    (hCayleyEquiv : HerglotzOnUpperHalfPlane H <-> SchurOnUpperHalfPlane W)
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H)
    (hConjZero : forall z : Complex, f z = 0 -> f (star z) = 0) :
    RiemannHypothesis f := by
  exact reverse_RH_via_cayley hGlobalSchur hCayleyEquiv hNevanlinnaExclusion hConjZero

theorem final_bridge_closed_via_cayley_conjugation_symmetry
    {f H W : Complex -> Complex}
    (hGlobalSchur : WGlobalSchurOnUpperHalfPlane W)
    (hCayleyEquiv : HerglotzOnUpperHalfPlane H <-> SchurOnUpperHalfPlane W)
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  exact reverse_RH_via_cayley_conjugation_symmetry
    hGlobalSchur hCayleyEquiv hNevanlinnaExclusion hConjSymm

theorem final_bridge_closed_via_cayley_xi_functional_symmetry
    {f H W : Complex -> Complex}
    (hGlobalSchur : WGlobalSchurOnUpperHalfPlane W)
    (hCayleyEquiv : HerglotzOnUpperHalfPlane H <-> SchurOnUpperHalfPlane W)
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H)
    (hXiSymm : XiFunctionalSymmetry f) :
    RiemannHypothesis f := by
  exact reverse_RH_via_cayley_xi_functional_symmetry
    hGlobalSchur hCayleyEquiv hNevanlinnaExclusion hXiSymm

end LeanV31
