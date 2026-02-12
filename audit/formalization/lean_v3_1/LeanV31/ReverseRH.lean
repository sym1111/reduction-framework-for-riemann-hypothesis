import LeanV31.WGlobalSchur
import LeanV31.RHFromLstar

namespace LeanV31

/- S014 wrapper:
global Schur control for W implies Herglotz for H = -f'/f; holomorphy of H
excludes upper-half zeros and symmetry closes RH. -/
/-
Core map to paper closure:
- `hZeroFree`: no-zero conclusion at the RH endpoint.
- `hConjZero`: symmetry closure step used by `cor:rh_from_Lstar`.
- `hNevanlinnaExclusion` remains as the explicit no-pole/no-zero wrapper route
  (`lem:no_zeros_from_herglotz` / `lem:no_pole_nevanlinna` path).
-/
theorem reverse_RH_core
    {f : Complex -> Complex}
    (hZeroFree : ZeroFreeOnUpper f)
    (hConjZero : forall z : Complex, f z = 0 -> f (star z) = 0) :
    RiemannHypothesis f := by
  exact rh_from_lstar_core hZeroFree hConjZero

theorem reverse_RH_core_via_nevanlinna
    {f H : Complex -> Complex}
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H)
    (hConjZero : forall z : Complex, f z = 0 -> f (star z) = 0) :
    RiemannHypothesis f := by
  have hZeroFree : ZeroFreeOnUpper f :=
    zero_free_of_nevanlinna hNevanlinnaExclusion
  exact reverse_RH_core hZeroFree hConjZero

theorem reverse_RH_via_conj_zero
    {f : Complex -> Complex}
    (hZeroFree : ZeroFreeOnUpper f)
    (hConjZero : forall z : Complex, f z = 0 -> f (star z) = 0) :
    RiemannHypothesis f := by
  exact reverse_RH_core hZeroFree hConjZero

theorem reverse_RH_from_zerofree_conj
    {f : Complex -> Complex}
    -- Core closure endpoint used for root-assumption reduction batches.
    (hZeroFree : ZeroFreeOnUpper f)
    (hConjZero : forall z : Complex, f z = 0 -> f (star z) = 0) :
    RiemannHypothesis f := by
  exact reverse_RH_core hZeroFree hConjZero

/- Core endpoint:
close RH from `ZeroFreeOnUpper` + conjugation symmetry. -/
theorem reverse_RH
    {f : Complex -> Complex}
    (hZeroFree : ZeroFreeOnUpper f)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  exact rh_from_lstar hZeroFree hConjSymm

/- Paper wrapper endpoint:
`lem:no_pole_nevanlinna` -> `lem:no_zeros_from_herglotz` -> core reverse RH closure. -/
theorem reverse_RH_via_certificate
    {f H : Complex -> Complex}
    (hCertificate : CircleHardyZeroFreeCertificate f H)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  exact rh_from_lstar_via_certificate hCertificate hConjSymm

theorem reverse_RH_via_nevanlinna
    {f H : Complex -> Complex}
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H)
    (hConjZero : forall z : Complex, f z = 0 -> f (star z) = 0) :
    RiemannHypothesis f := by
  have hZeroFree : ZeroFreeOnUpper f :=
    zero_free_of_nevanlinna hNevanlinnaExclusion
  exact reverse_RH_from_zerofree_conj hZeroFree hConjZero

theorem reverse_RH_via_conjugation_symmetry
    {f : Complex -> Complex}
    (hZeroFree : ZeroFreeOnUpper f)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  have hConjZero : forall z : Complex, f z = 0 -> f (star z) = 0 :=
    conj_zero_of_conjugation_symmetric hConjSymm
  exact reverse_RH_via_conj_zero hZeroFree hConjZero

theorem reverse_RH_via_nevanlinna_conjugation_symmetry
    {f H : Complex -> Complex}
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  have hZeroFree : ZeroFreeOnUpper f :=
    zero_free_of_nevanlinna hNevanlinnaExclusion
  exact reverse_RH_via_conjugation_symmetry hZeroFree hConjSymm

theorem reverse_RH_via_xi_functional_symmetry
    {f : Complex -> Complex}
    (hZeroFree : ZeroFreeOnUpper f)
    (hXiSymm : XiFunctionalSymmetry f) :
    RiemannHypothesis f := by
  have hConjSymm : ConjugationSymmetric f :=
    conjugation_symmetric_of_xi_functional_symmetry hXiSymm
  exact reverse_RH_via_conjugation_symmetry hZeroFree hConjSymm

theorem reverse_RH_via_nevanlinna_xi_functional_symmetry
    {f H : Complex -> Complex}
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H)
    (hXiSymm : XiFunctionalSymmetry f) :
    RiemannHypothesis f := by
  have hZeroFree : ZeroFreeOnUpper f :=
    zero_free_of_nevanlinna hNevanlinnaExclusion
  exact reverse_RH_via_xi_functional_symmetry hZeroFree hXiSymm

theorem reverse_RH_via_cayley
    {f H W : Complex -> Complex}
    -- `hGlobalSchur` + `hCayleyEquiv` corresponds to `prop:W_global_schur` + `lem:cayley_equiv`.
    (hGlobalSchur : WGlobalSchurOnUpperHalfPlane W)
    (hCayleyEquiv : HerglotzOnUpperHalfPlane H <-> SchurOnUpperHalfPlane W)
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H)
    (hConjZero : forall z : Complex, f z = 0 -> f (star z) = 0) :
    RiemannHypothesis f := by
  have _hHer : HerglotzOnUpperHalfPlane H := hCayleyEquiv.mpr hGlobalSchur
  exact reverse_RH_via_nevanlinna hNevanlinnaExclusion hConjZero

theorem reverse_RH_via_cayley_conjugation_symmetry
    {f H W : Complex -> Complex}
    (hGlobalSchur : WGlobalSchurOnUpperHalfPlane W)
    (hCayleyEquiv : HerglotzOnUpperHalfPlane H <-> SchurOnUpperHalfPlane W)
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  have _hHer : HerglotzOnUpperHalfPlane H := hCayleyEquiv.mpr hGlobalSchur
  exact reverse_RH_via_nevanlinna_conjugation_symmetry hNevanlinnaExclusion hConjSymm

theorem reverse_RH_via_cayley_xi_functional_symmetry
    {f H W : Complex -> Complex}
    (hGlobalSchur : WGlobalSchurOnUpperHalfPlane W)
    (hCayleyEquiv : HerglotzOnUpperHalfPlane H <-> SchurOnUpperHalfPlane W)
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H)
    (hXiSymm : XiFunctionalSymmetry f) :
    RiemannHypothesis f := by
  have _hHer : HerglotzOnUpperHalfPlane H := hCayleyEquiv.mpr hGlobalSchur
  exact reverse_RH_via_nevanlinna_xi_functional_symmetry hNevanlinnaExclusion hXiSymm

end LeanV31
