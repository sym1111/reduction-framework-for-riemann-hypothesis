import LeanV31.FinalBridgeClosed
import LeanV31.CanonicalTruncDetector0B21

namespace LeanV31

theorem final_bridge_closed_via_canonical_trunc_conjugation_symmetry
    {f H : Complex -> Complex}
    (hFamily : TruncationWeylHerglotzFamily (fun _ _ => 0))
    (hModes : forall (n : Nat), NoNegativeModesOnCircle n)
    (hDefectAll : forall (n : Nat), DetectorDefectZeroAtLevel n)
    (hLocator : HardyPoleLocatorOnCircle H)
    (hCertificate : CircleHardyZeroFreeCertificate f H)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  have hCanon : (forall (n : Nat), NoNegativeModesOnCircle n) /\
      (forall (n : Nat), DetectorDefectZeroAtLevel n) :=
    canonical_trunc_detector0 hFamily hModes hDefectAll
  have _hDefectAll : forall (n : Nat), DetectorDefectZeroAtLevel n := hCanon.2
  exact final_bridge_closed_via_hardy_locator_conjugation_symmetry
    hLocator hCertificate hConjSymm

theorem final_bridge_closed_via_canonical_trunc_xi_functional_symmetry
    {f H : Complex -> Complex}
    (hFamily : TruncationWeylHerglotzFamily (fun _ _ => 0))
    (hModes : forall (n : Nat), NoNegativeModesOnCircle n)
    (hDefectAll : forall (n : Nat), DetectorDefectZeroAtLevel n)
    (hLocator : HardyPoleLocatorOnCircle H)
    (hCertificate : CircleHardyZeroFreeCertificate f H)
    (hXiSymm : XiFunctionalSymmetry f) :
    RiemannHypothesis f := by
  have hCanon : (forall (n : Nat), NoNegativeModesOnCircle n) /\
      (forall (n : Nat), DetectorDefectZeroAtLevel n) :=
    canonical_trunc_detector0 hFamily hModes hDefectAll
  have _hDefectAll : forall (n : Nat), DetectorDefectZeroAtLevel n := hCanon.2
  exact final_bridge_closed_via_hardy_locator_xi_functional_symmetry
    hLocator hCertificate hXiSymm

end LeanV31
