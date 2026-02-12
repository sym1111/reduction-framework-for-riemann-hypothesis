import LeanV31.NoZerosFromHerglotz

namespace LeanV31

def RiemannHypothesis (f : Complex -> Complex) : Prop := HasOnlyRealZeros f

def ConjugationSymmetric (f : Complex -> Complex) : Prop :=
  forall z : Complex, f (star z) = star (f z)

def XiFunctionalSymmetry (f : Complex -> Complex) : Prop :=
  (forall z : Complex, f (star z) = star (f z)) /\
    (forall z : Complex, f (-star z) = f z)

theorem conjugation_symmetric_of_xi_functional_symmetry
    {f : Complex -> Complex}
    (hXiSymm : XiFunctionalSymmetry f) :
    ConjugationSymmetric f := by
  exact hXiSymm.1

theorem conj_zero_of_conjugation_symmetric
    {f : Complex -> Complex}
    (hConjSymm : ConjugationSymmetric f) :
    forall z : Complex, f z = 0 -> f (star z) = 0 := by
  intro z hz
  calc
    f (star z) = star (f z) := hConjSymm z
    _ = 0 := by simp [hz]

/- S022 wrapper:
L* (via Herglotz for `H = -f'/f`) excludes zeros in `C_+`; symmetry then forces
all zeros onto `R`, yielding RH. -/
/-
Paper-label map for core closure assumptions:
- `hZeroFree` corresponds to the no-zero conclusion used in `lem:no_zeros_from_herglotz`.
- `hConjZero` is the zero-reflection symmetry closure used in `cor:rh_from_Lstar`.
-/
theorem rh_from_lstar_core
    {f : Complex -> Complex}
    (hZeroFree : ZeroFreeOnUpper f)
    (hConjZero : forall z : Complex, f z = 0 -> f (star z) = 0) :
    RiemannHypothesis f := by
  intro z hz
  by_cases hzIm : z.im = 0
  case pos =>
    exact hzIm
  case neg =>
    rcases lt_or_gt_of_ne hzIm with hImNeg | hImPos
    case inl =>
      have hzReflected : f (star z) = 0 := hConjZero z hz
      have hImReflectedPos : 0 < (star z).im := by
        simpa using (neg_pos.mpr hImNeg)
      exact False.elim ((hZeroFree (star z) hImReflectedPos) hzReflected)
    case inr =>
      exact False.elim ((hZeroFree z hImPos) hz)

theorem zero_free_of_nevanlinna
    {f H : Complex -> Complex}
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H) :
    ZeroFreeOnUpper f := by
  exact no_zeros_from_herglotz hNevanlinnaExclusion

theorem rh_from_lstar_core_via_nevanlinna
    {f H : Complex -> Complex}
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H)
    (hConjZero : forall z : Complex, f z = 0 -> f (star z) = 0) :
    RiemannHypothesis f := by
  have hZeroFree : ZeroFreeOnUpper f :=
    zero_free_of_nevanlinna hNevanlinnaExclusion
  exact rh_from_lstar_core hZeroFree hConjZero

theorem rh_from_lstar_via_nevanlinna_conj_zero
    {f H : Complex -> Complex}
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H)
    (hConjZero : forall z : Complex, f z = 0 -> f (star z) = 0) :
    RiemannHypothesis f := by
  exact rh_from_lstar_core_via_nevanlinna hNevanlinnaExclusion hConjZero

/- Core endpoint for `cor:rh_from_Lstar` closure:
close RH from zero-free upper-half-plane + conjugation symmetry. -/
theorem rh_from_lstar
    {f : Complex -> Complex}
    (hZeroFree : ZeroFreeOnUpper f)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  have hConjZero : forall z : Complex, f z = 0 -> f (star z) = 0 :=
    conj_zero_of_conjugation_symmetric hConjSymm
  exact rh_from_lstar_core hZeroFree hConjZero

/- Paper wrapper route (`lem:no_pole_nevanlinna` + `lem:no_zeros_from_herglotz` + `cor:rh_from_Lstar`):
derive the no-zero input from detector/certificate data, then call the core endpoint. -/
theorem rh_from_lstar_via_certificate
    {f H : Complex -> Complex}
    (hCertificate : CircleHardyZeroFreeCertificate f H)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  have hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H := no_pole_nevanlinna hCertificate
  have hZeroFree : ZeroFreeOnUpper f :=
    zero_free_of_nevanlinna hNevanlinnaExclusion
  exact rh_from_lstar hZeroFree hConjSymm

theorem rh_from_lstar_via_conjugation_symmetry
    {f H : Complex -> Complex}
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  have hConjZero : forall z : Complex, f z = 0 -> f (star z) = 0 :=
    conj_zero_of_conjugation_symmetric hConjSymm
  exact rh_from_lstar_via_nevanlinna_conj_zero hNevanlinnaExclusion hConjZero

theorem rh_from_lstar_via_xi_functional_symmetry
    {f H : Complex -> Complex}
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H)
    (hXiSymm : XiFunctionalSymmetry f) :
    RiemannHypothesis f := by
  have hConjSymm : ConjugationSymmetric f :=
    conjugation_symmetric_of_xi_functional_symmetry hXiSymm
  exact rh_from_lstar_via_conjugation_symmetry hNevanlinnaExclusion hConjSymm

theorem zero_free_and_conjugation_symmetry_suffice
    {f : Complex -> Complex}
    (hZeroFree : ZeroFreeOnUpper f)
    (hConjSymm : ConjugationSymmetric f) :
    RiemannHypothesis f := by
  have hConjZero : forall z : Complex, f z = 0 -> f (star z) = 0 :=
    conj_zero_of_conjugation_symmetric hConjSymm
  exact rh_from_lstar_core hZeroFree hConjZero

theorem zero_free_on_upper_not_sufficient :
    Exists fun f : Complex -> Complex => ZeroFreeOnUpper f /\ Not (RiemannHypothesis f) := by
  refine Exists.intro (fun z : Complex => z + Complex.I) ?_
  constructor
  case left =>
    intro z hzIm hzZero
    have hz : z = -Complex.I := by
      simpa using eq_neg_of_add_eq_zero_left hzZero
    have hzImEq : z.im = -1 := by
      simp [hz]
    linarith [hzIm, hzImEq]
  case right =>
    intro hRH
    have hZero : (fun z : Complex => z + Complex.I) (-Complex.I) = 0 := by
      simp
    have hImZero : (-Complex.I).im = 0 := hRH (-Complex.I) hZero
    norm_num at hImZero

theorem conjugation_symmetric_not_sufficient :
    Exists fun f : Complex -> Complex => ConjugationSymmetric f /\ Not (RiemannHypothesis f) := by
  refine Exists.intro (fun _ : Complex => 0) ?_
  constructor
  case left =>
    intro z
    simp
  case right =>
    intro hRH
    have hImZero : Complex.I.im = 0 := hRH Complex.I (by simp)
    norm_num at hImZero

end LeanV31
