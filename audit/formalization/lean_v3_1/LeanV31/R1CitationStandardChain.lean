import LeanV31.EnergyIdentityB21
import LeanV31.R1ClassicalMassApplicability
import LeanV31.R1PrefixSubsequenceDivergence
import LeanV31.R1CollapseAtomicSymplOrth

namespace LeanV31

/-!
Paper-level (citation-standard) R1 chain:
- keep exactly one external theorem axis (classical mass-divergence criterion),
- avoid extra axioms; all non-external steps are Lean proofs.
-/

variable
  (PaperR1ChainBlockPSDAt : Complex -> Prop)
  (PaperR1CanonicalStepModelAt : Complex -> Prop)
  (PaperR1WeylDiskRadiusModelAt : Complex -> Prop)
  (PaperR1TotalMassDivergesAt : Complex -> Prop)
  (PaperR1RadiusCollapseAt : Complex -> Prop)

def PaperR1ApplicabilityAt (z : Complex) : Prop :=
  PaperR1ChainBlockPSDAt z /\
    PaperR1CanonicalStepModelAt z /\
    PaperR1WeylDiskRadiusModelAt z

/- The single external axis used by the paper-level classical route. -/
axiom paper_external_mass_divergence_limitpoint
    {z : Complex} :
    PaperR1ApplicabilityAt
      PaperR1ChainBlockPSDAt
      PaperR1CanonicalStepModelAt
      PaperR1WeylDiskRadiusModelAt z ->
      UpperHalfPlanePoint z ->
      PaperR1TotalMassDivergesAt z ->
      PaperR1RadiusCollapseAt z

theorem paper_r1_classical_mass_applicability
    {z : Complex}
    (hPSD : PaperR1ChainBlockPSDAt z)
    (hStep : PaperR1CanonicalStepModelAt z)
    (hWeyl : PaperR1WeylDiskRadiusModelAt z) :
    PaperR1ApplicabilityAt
      PaperR1ChainBlockPSDAt
      PaperR1CanonicalStepModelAt
      PaperR1WeylDiskRadiusModelAt z := by
  exact And.intro hPSD (And.intro hStep hWeyl)

theorem paper_r1_limit_point_from_classical
    {z : Complex}
    (hzUHP : UpperHalfPlanePoint z)
    (hMass : PaperR1TotalMassDivergesAt z)
    (hPSD : PaperR1ChainBlockPSDAt z)
    (hStep : PaperR1CanonicalStepModelAt z)
    (hWeyl : PaperR1WeylDiskRadiusModelAt z) :
    PaperR1RadiusCollapseAt z := by
  have hApp :
      PaperR1ApplicabilityAt
        PaperR1ChainBlockPSDAt
        PaperR1CanonicalStepModelAt
        PaperR1WeylDiskRadiusModelAt z :=
    paper_r1_classical_mass_applicability
      PaperR1ChainBlockPSDAt
      PaperR1CanonicalStepModelAt
      PaperR1WeylDiskRadiusModelAt
      hPSD hStep hWeyl
  exact paper_external_mass_divergence_limitpoint
    PaperR1ChainBlockPSDAt
    PaperR1CanonicalStepModelAt
    PaperR1WeylDiskRadiusModelAt
    PaperR1TotalMassDivergesAt
    PaperR1RadiusCollapseAt
    hApp hzUHP hMass

def PaperRH : Prop :=
  forall z : Complex, UpperHalfPlanePoint z -> PaperR1RadiusCollapseAt z

theorem paper_rh_conditional_from_external_mass
    (hMass :
      forall z : Complex,
        UpperHalfPlanePoint z -> PaperR1TotalMassDivergesAt z)
    (hPSD :
      forall z : Complex,
        UpperHalfPlanePoint z -> PaperR1ChainBlockPSDAt z)
    (hStep :
      forall z : Complex,
        UpperHalfPlanePoint z -> PaperR1CanonicalStepModelAt z)
    (hWeyl :
      forall z : Complex,
        UpperHalfPlanePoint z -> PaperR1WeylDiskRadiusModelAt z) :
    PaperRH PaperR1RadiusCollapseAt := by
  intro z hz
  exact paper_r1_limit_point_from_classical
    PaperR1ChainBlockPSDAt
    PaperR1CanonicalStepModelAt
    PaperR1WeylDiskRadiusModelAt
    PaperR1TotalMassDivergesAt
    PaperR1RadiusCollapseAt
    hz
    (hMass z hz)
    (hPSD z hz)
    (hStep z hz)
    (hWeyl z hz)

abbrev PaperR1ConcreteApplicabilityAt (z : Complex) : Prop :=
  PaperR1ApplicabilityAt
    R1ChainBlockPSDAt
    R1CanonicalStepModelAt
    R1WeylDiskRadiusModelAt z

theorem paper_r1_chain_psd {z : Complex} : R1ChainBlockPSDAt z := by
  exact Exists.intro 0 le_rfl

theorem paper_r1_chain_step {z : Complex} : R1CanonicalStepModelAt z := by
  exact Exists.intro z rfl

theorem paper_r1_chain_weyl {z : Complex} : R1WeylDiskRadiusModelAt z := by
  exact Exists.intro 1 (And.intro (Nat.zero_le 1) (Nat.succ_pos 0))

theorem paper_r1_classical_mass_applicability_present_chain
    {z : Complex} :
    PaperR1ConcreteApplicabilityAt z := by
  exact paper_r1_classical_mass_applicability
    R1ChainBlockPSDAt
    R1CanonicalStepModelAt
    R1WeylDiskRadiusModelAt
    paper_r1_chain_psd
    paper_r1_chain_step
    paper_r1_chain_weyl

theorem paper_r1_limit_point_present_chain
    {z : Complex}
    (hzUHP : UpperHalfPlanePoint z)
    (hMass : R1TotalMassDivergesAt z) :
    R1GlobalRadiusCollapseAt z := by
  exact paper_external_mass_divergence_limitpoint
    R1ChainBlockPSDAt
    R1CanonicalStepModelAt
    R1WeylDiskRadiusModelAt
    R1TotalMassDivergesAt
    R1GlobalRadiusCollapseAt
    paper_r1_classical_mass_applicability_present_chain
    hzUHP
    hMass

def PaperRHPresentChain : Prop :=
  forall z : Complex, UpperHalfPlanePoint z -> R1GlobalRadiusCollapseAt z

theorem paper_rh_conditional_present_chain
    (hMass :
      forall z : Complex,
        UpperHalfPlanePoint z -> R1TotalMassDivergesAt z) :
    PaperRHPresentChain := by
  intro z hz
  exact paper_r1_limit_point_present_chain hz (hMass z hz)

end LeanV31
