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

/-!
Mainline theorem-shape matching layer for the external mass-divergence axis.
This isolates interface-level matching from deeper semantic internalization.
-/

def CanonicalMassHamiltonianRegularityAt (z : Complex) : Prop :=
  PaperR1ChainBlockPSDAt z /\ PaperR1CanonicalStepModelAt z

def CanonicalMassWeylRadiusModelAt (z : Complex) : Prop :=
  PaperR1WeylDiskRadiusModelAt z

def CanonicalMassDivergenceAt (z : Complex) : Prop :=
  PaperR1TotalMassDivergesAt z

def CanonicalMassLimitPointAt (z : Complex) : Prop :=
  PaperR1RadiusCollapseAt z

def CanonicalMassTheoremInputAt (z : Complex) : Prop :=
  CanonicalMassHamiltonianRegularityAt
      PaperR1ChainBlockPSDAt
      PaperR1CanonicalStepModelAt z /\
    CanonicalMassWeylRadiusModelAt
      PaperR1WeylDiskRadiusModelAt z /\
    UpperHalfPlanePoint z /\
    CanonicalMassDivergenceAt
      PaperR1TotalMassDivergesAt z

theorem paper_r1_hamiltonian_shape_iff
    {z : Complex} :
    CanonicalMassHamiltonianRegularityAt
      PaperR1ChainBlockPSDAt
      PaperR1CanonicalStepModelAt z <->
    (PaperR1ChainBlockPSDAt z /\ PaperR1CanonicalStepModelAt z) := by
  exact Iff.rfl

theorem paper_r1_weyl_shape_iff
    {z : Complex} :
    CanonicalMassWeylRadiusModelAt
      PaperR1WeylDiskRadiusModelAt z <->
    PaperR1WeylDiskRadiusModelAt z := by
  exact Iff.rfl

theorem paper_r1_mass_divergence_shape_iff
    {z : Complex} :
    CanonicalMassDivergenceAt
      PaperR1TotalMassDivergesAt z <->
    PaperR1TotalMassDivergesAt z := by
  exact Iff.rfl

theorem paper_r1_limit_point_shape_iff
    {z : Complex} :
    CanonicalMassLimitPointAt
      PaperR1RadiusCollapseAt z <->
    PaperR1RadiusCollapseAt z := by
  exact Iff.rfl

theorem paper_r1_applicability_to_theorem_input
    {z : Complex}
    (hApp :
      PaperR1ApplicabilityAt
        PaperR1ChainBlockPSDAt
        PaperR1CanonicalStepModelAt
        PaperR1WeylDiskRadiusModelAt z)
    (hzUHP : UpperHalfPlanePoint z)
    (hMass : PaperR1TotalMassDivergesAt z) :
    CanonicalMassTheoremInputAt
      PaperR1ChainBlockPSDAt
      PaperR1CanonicalStepModelAt
      PaperR1WeylDiskRadiusModelAt
      PaperR1TotalMassDivergesAt z := by
  rcases hApp with ⟨hPSD, hStep, hWeyl⟩
  exact And.intro
    (And.intro hPSD hStep)
    (And.intro hWeyl (And.intro hzUHP hMass))

theorem paper_r1_theorem_input_to_axiom_premises
    {z : Complex}
    (hInput :
      CanonicalMassTheoremInputAt
        PaperR1ChainBlockPSDAt
        PaperR1CanonicalStepModelAt
        PaperR1WeylDiskRadiusModelAt
        PaperR1TotalMassDivergesAt z) :
    PaperR1ApplicabilityAt
      PaperR1ChainBlockPSDAt
      PaperR1CanonicalStepModelAt
      PaperR1WeylDiskRadiusModelAt z /\
      UpperHalfPlanePoint z /\
      PaperR1TotalMassDivergesAt z := by
  rcases hInput with ⟨hHam, hWeyl, hzUHP, hMass⟩
  rcases hHam with ⟨hPSD, hStep⟩
  exact And.intro
    (And.intro hPSD (And.intro hStep hWeyl))
    (And.intro hzUHP hMass)

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

theorem paper_external_mass_divergence_limitpoint_from_theorem_input
    {z : Complex}
    (hInput :
      CanonicalMassTheoremInputAt
        PaperR1ChainBlockPSDAt
        PaperR1CanonicalStepModelAt
        PaperR1WeylDiskRadiusModelAt
        PaperR1TotalMassDivergesAt z) :
    CanonicalMassLimitPointAt PaperR1RadiusCollapseAt z := by
  have hPrem :
      PaperR1ApplicabilityAt
        PaperR1ChainBlockPSDAt
        PaperR1CanonicalStepModelAt
        PaperR1WeylDiskRadiusModelAt z /\
        UpperHalfPlanePoint z /\
        PaperR1TotalMassDivergesAt z :=
    paper_r1_theorem_input_to_axiom_premises
      PaperR1ChainBlockPSDAt
      PaperR1CanonicalStepModelAt
      PaperR1WeylDiskRadiusModelAt
      PaperR1TotalMassDivergesAt
      hInput
  rcases hPrem with ⟨hApp, hzUHP, hMass⟩
  exact paper_external_mass_divergence_limitpoint
    PaperR1ChainBlockPSDAt
    PaperR1CanonicalStepModelAt
    PaperR1WeylDiskRadiusModelAt
    PaperR1TotalMassDivergesAt
    PaperR1RadiusCollapseAt
    hApp hzUHP hMass

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
  have hInput :
      CanonicalMassTheoremInputAt
        PaperR1ChainBlockPSDAt
        PaperR1CanonicalStepModelAt
        PaperR1WeylDiskRadiusModelAt
        PaperR1TotalMassDivergesAt z :=
    paper_r1_applicability_to_theorem_input
      PaperR1ChainBlockPSDAt
      PaperR1CanonicalStepModelAt
      PaperR1WeylDiskRadiusModelAt
      PaperR1TotalMassDivergesAt
      hApp hzUHP hMass
  have hCollapse :
      CanonicalMassLimitPointAt PaperR1RadiusCollapseAt z :=
    paper_external_mass_divergence_limitpoint_from_theorem_input
      PaperR1ChainBlockPSDAt
      PaperR1CanonicalStepModelAt
      PaperR1WeylDiskRadiusModelAt
      PaperR1TotalMassDivergesAt
      PaperR1RadiusCollapseAt
      hInput
  exact (paper_r1_limit_point_shape_iff PaperR1RadiusCollapseAt).mp hCollapse

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

theorem paper_r1_limit_point_present_chain_from_components
    {z : Complex}
    (hzUHP : UpperHalfPlanePoint z)
    (hMass : R1TotalMassDivergesAt z)
    (hPSD : R1ChainBlockPSDAt z)
    (hStep : R1CanonicalStepModelAt z)
    (hWeyl : R1WeylDiskRadiusModelAt z) :
    R1GlobalRadiusCollapseAt z := by
  exact paper_r1_limit_point_from_classical
    R1ChainBlockPSDAt
    R1CanonicalStepModelAt
    R1WeylDiskRadiusModelAt
    R1TotalMassDivergesAt
    R1GlobalRadiusCollapseAt
    hzUHP hMass hPSD hStep hWeyl

abbrev PaperR1ConcreteApplicabilityAt (z : Complex) : Prop :=
  PaperR1ApplicabilityAt
    R1ChainBlockPSDAt
    R1CanonicalStepModelAt
    R1WeylDiskRadiusModelAt z

theorem paper_r1_chain_psd {z : Complex} : R1ChainBlockPSDAt z := by
  intro k
  have hk : (0 : Real) <= (k : Real) := by
    exact_mod_cast (Nat.zero_le k)
  have h1 : (0 : Real) <= (1 : Real) := by
    norm_num
  simpa [R1HamiltonianTraceAt] using add_nonneg hk h1

theorem paper_r1_chain_step {z : Complex} : R1CanonicalStepModelAt z := by
  intro n
  simp [R1CanonicalStepResidualAt, R1StepMAt]

theorem paper_r1_chain_weyl {z : Complex} : R1WeylDiskRadiusModelAt z := by
  intro n
  simp [R1WeylRadiusAt]

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
