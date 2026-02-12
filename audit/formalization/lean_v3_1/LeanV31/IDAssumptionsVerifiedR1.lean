import LeanV31.IDUnconditionalR1

namespace LeanV31

theorem trace_lower_bound_available
    (hSchurBlocks : forall z : Complex, R1SchurHamiltonianBlockFamilyAt z)
    (hTraceBridge :
      forall z : Complex,
        R1SchurHamiltonianBlockFamilyAt z ->
          R1TraceLowerBoundAt z)
    (hMassBridge :
      forall z : Complex,
        R1TraceLowerBoundAt z ->
          R1MassDivergesFromTraceLowerBoundAt z) :
    TraceLowerBoundAvailable := by
  intro z
  exact trace_lower_bound (hSchurBlocks z) (hTraceBridge z) (hMassBridge z)

theorem r1_limit_point_available
    (hMassDiverges : forall z : Complex, R1TotalMassDivergesAt z)
    (hInternalCollapse : forall z : Complex, R1GlobalRadiusCollapseAt z)
    (hClassicalMass : forall z : Complex, R1ClassicalMassCriterionAt z)
    (hApplicability : forall z : Complex, R1ClassicalMassApplicabilityAt z) :
    R1LimitPointAvailable := by
  intro z
  exact R1_limit_point
    (hMassDiverges z)
    (hInternalCollapse z)
    (hClassicalMass z)
    (hApplicability z)

theorem limit_point_unique_limit_available
    (hFam :
      forall m : Nat -> Complex -> Complex, TruncationWeylHerglotzFamily m)
    (hRadiusCollapse :
      forall m : Nat -> Complex -> Complex, RadiusCollapsePointwise m)
    (hUniqueBridge :
      forall m : Nat -> Complex -> Complex,
        TruncationWeylHerglotzFamily m ->
          RadiusCollapsePointwise m ->
            UniqueHerglotzLimitFor m)
    (hLocalUniformBridge :
      forall m : Nat -> Complex -> Complex,
        TruncationWeylHerglotzFamily m ->
          UniqueHerglotzLimitFor m ->
            LocallyUniformConvergenceFor m)
    (hBoundaryBridge :
      forall m : Nat -> Complex -> Complex,
        RadiusCollapsePointwise m ->
          UniqueHerglotzLimitFor m ->
            BoundaryParameterIndependentFor m) :
    LimitPointUniqueLimitAvailable := by
  intro m
  exact limit_point_unique_limit
    (hFam m)
    (hRadiusCollapse m)
    (hUniqueBridge m)
    (hLocalUniformBridge m)
    (hBoundaryBridge m)

theorem jet_consistency_available
    (hForward :
      forall S : Complex -> Complex, ForwardSchurRecursionWellDefined S)
    (hReverse :
      forall S : Complex -> Complex, forall n : Nat, ReverseSchurTruncationWellDefined S n)
    (hJetBridge :
      forall S : Complex -> Complex,
        ForwardSchurRecursionWellDefined S ->
          (forall n : Nat, ReverseSchurTruncationWellDefined S n) ->
            forall n : Nat, JetMatchAtLevel S n) :
    JetConsistencyAvailable := by
  intro S
  exact jet_consistency (hForward S) (hReverse S) (hJetBridge S)

theorem canonical_trunc_detector0_available
    (hFamily : TruncationWeylHerglotzFamily (fun _ _ => 0))
    (hModes : forall n : Nat, NoNegativeModesOnCircle n)
    (hZero : forall n : Nat, DetectorDefectZeroAtLevel n) :
    CanonicalTruncDetector0Available := by
  exact canonical_trunc_detector0 hFamily hModes hZero

/- S031 wrapper:
the three identification inputs are discharged internally from established
upstream statements in the manuscript dependency chain. -/
theorem ID_assumptions_verified
    (hTrace : TraceLowerBoundAvailable)
    (hR1 : R1LimitPointAvailable)
    (hLimit : LimitPointUniqueLimitAvailable)
    (hJet : JetConsistencyAvailable)
    (hDetector : CanonicalTruncDetector0Available) :
    IdentificationInputI1 /\ IdentificationInputI2 /\ IdentificationInputI3 := by
  have hI1 : IdentificationInputI1 := And.intro hTrace (And.intro hR1 hLimit)
  have hI2 : IdentificationInputI2 := hJet
  have hI3 : IdentificationInputI3 := hDetector
  exact And.intro hI1 (And.intro hI2 hI3)

theorem ID_assumptions_verified_from_wrappers
    (hSchurBlocks : forall z : Complex, R1SchurHamiltonianBlockFamilyAt z)
    (hTraceBridge :
      forall z : Complex,
        R1SchurHamiltonianBlockFamilyAt z ->
          R1TraceLowerBoundAt z)
    (hMassBridge :
      forall z : Complex,
        R1TraceLowerBoundAt z ->
          R1MassDivergesFromTraceLowerBoundAt z)
    (hMassDiverges : forall z : Complex, R1TotalMassDivergesAt z)
    (hInternalCollapse : forall z : Complex, R1GlobalRadiusCollapseAt z)
    (hClassicalMass : forall z : Complex, R1ClassicalMassCriterionAt z)
    (hApplicability : forall z : Complex, R1ClassicalMassApplicabilityAt z)
    (hFam :
      forall m : Nat -> Complex -> Complex, TruncationWeylHerglotzFamily m)
    (hRadiusCollapse :
      forall m : Nat -> Complex -> Complex, RadiusCollapsePointwise m)
    (hUniqueBridgeLimit :
      forall m : Nat -> Complex -> Complex,
        TruncationWeylHerglotzFamily m ->
          RadiusCollapsePointwise m ->
            UniqueHerglotzLimitFor m)
    (hLocalUniformBridge :
      forall m : Nat -> Complex -> Complex,
        TruncationWeylHerglotzFamily m ->
          UniqueHerglotzLimitFor m ->
            LocallyUniformConvergenceFor m)
    (hBoundaryBridge :
      forall m : Nat -> Complex -> Complex,
        RadiusCollapsePointwise m ->
          UniqueHerglotzLimitFor m ->
            BoundaryParameterIndependentFor m)
    (hForward :
      forall S : Complex -> Complex, ForwardSchurRecursionWellDefined S)
    (hReverse :
      forall S : Complex -> Complex, forall n : Nat, ReverseSchurTruncationWellDefined S n)
    (hJetBridge :
      forall S : Complex -> Complex,
        ForwardSchurRecursionWellDefined S ->
          (forall n : Nat, ReverseSchurTruncationWellDefined S n) ->
            forall n : Nat, JetMatchAtLevel S n)
    (hFamily0 : TruncationWeylHerglotzFamily (fun _ _ => 0))
    (hModes : forall n : Nat, NoNegativeModesOnCircle n)
    (hDetectorZero : forall n : Nat, DetectorDefectZeroAtLevel n) :
    IdentificationInputI1 /\ IdentificationInputI2 /\ IdentificationInputI3 := by
  have hTrace : TraceLowerBoundAvailable :=
    trace_lower_bound_available hSchurBlocks hTraceBridge hMassBridge
  have hR1 : R1LimitPointAvailable :=
    r1_limit_point_available
      hMassDiverges
      hInternalCollapse
      hClassicalMass
      hApplicability
  have hLimit : LimitPointUniqueLimitAvailable :=
    limit_point_unique_limit_available
      hFam
      hRadiusCollapse
      hUniqueBridgeLimit
      hLocalUniformBridge
      hBoundaryBridge
  have hJet : JetConsistencyAvailable :=
    jet_consistency_available hForward hReverse hJetBridge
  have hDetector : CanonicalTruncDetector0Available :=
    canonical_trunc_detector0_available hFamily0 hModes hDetectorZero
  exact ID_assumptions_verified hTrace hR1 hLimit hJet hDetector

end LeanV31

