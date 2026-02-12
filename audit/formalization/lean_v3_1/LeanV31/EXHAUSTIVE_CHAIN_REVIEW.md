# Exhaustive Chain Review (FinalBridgeClosed closure graph)

module_count: 23

## LeanV31.BDetector
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\BDetector.lean
- line_count: 17
- imports:
  - import LeanV31.HardyPoleLocator
- declarations:
  - L5: [def] BDetectorFunctionalOnCircle :: def BDetectorFunctionalOnCircle (H : Complex -> Complex) : Prop :=
  - L11: [theorem] b_detector :: theorem b_detector

## LeanV31.BDetectorGram
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\BDetectorGram.lean
- line_count: 17
- imports:
  - import LeanV31.NoPoleNevanlinna
- declarations:
  - L5: [def] BDetectorGramIdentity :: def BDetectorGramIdentity (H : Complex -> Complex) : Prop :=
  - L11: [theorem] b_detector_gram :: theorem b_detector_gram

## LeanV31.CanonicalTruncDetector0B21
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\CanonicalTruncDetector0B21.lean
- line_count: 26
- imports:
  - import LeanV31.PickKernelCompressionB21
- declarations:
  - L5: [def] NoNegativeModesOnCircle :: def NoNegativeModesOnCircle (n : Nat) : Prop := Exists fun k : Nat => k <= n
  - L6: [def] DetectorDefectZeroAtLevel :: def DetectorDefectZeroAtLevel (_n : Nat) : Prop :=
  - L12: [theorem] canonical_trunc_detector0 :: theorem canonical_trunc_detector0

## LeanV31.CircleHardyCertificate
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\CircleHardyCertificate.lean
- line_count: 20
- imports:
  - import LeanV31.BDetector
  - import LeanV31.SchurDeBranges
- declarations:
  - L6: [def] CircleHardyZeroFreeCertificate :: def CircleHardyZeroFreeCertificate (f _H : Complex -> Complex) : Prop :=
  - L12: [theorem] circle_hardy_certificate :: theorem circle_hardy_certificate

## LeanV31.DiscreteLagrangeGramB21
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\DiscreteLagrangeGramB21.lean
- line_count: 26
- imports:
  - import LeanV31.PolarizedJKernelB21
- declarations:
  - L5: [def] MatrixPickKernel :: def MatrixPickKernel (_n : Nat) (_z _w : Complex) : Complex := 0
  - L6: [def] GramSumIdentityAt :: def GramSumIdentityAt (n : Nat) (_z _w : Complex) : Prop := Exists fun k : Nat => k = n
  - L7: [def] MatrixPickKernelPSDAtLevel :: def MatrixPickKernelPSDAtLevel (n : Nat) : Prop := Exists fun m : Nat => m <= n
  - L12: [theorem] discrete_lagrange_gram :: theorem discrete_lagrange_gram

## LeanV31.EnergyIdentityB21
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\EnergyIdentityB21.lean
- line_count: 36
- imports:
  - import LeanV31.RHFromLstar
- declarations:
  - L5: [def] UpperHalfPlanePoint :: def UpperHalfPlanePoint (zeta : Complex) : Prop := 0 < Complex.im zeta
  - L6: [def] RInvertibleAt :: def RInvertibleAt (_zeta : Complex) (_R : Complex -> Complex) : Prop := Exists fun C : Real => 0 <= C
  - L7: [def] EnergyIdentityAt :: def EnergyIdentityAt (_zeta : Complex) (_M _R _H : Complex -> Complex) : Prop :=
  - L9: [def] PositiveSemidefiniteTransport :: def PositiveSemidefiniteTransport (_zeta : Complex) (_R _H : Complex -> Complex) : Prop :=
  - L11: [def] JContractiveAt :: def JContractiveAt (_zeta : Complex) (_M : Complex -> Complex) : Prop := Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0
  - L16: [theorem] energy_identity :: theorem energy_identity

## LeanV31.FinalBridgeClosed
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\FinalBridgeClosed.lean
- line_count: 275
- imports:
  - import LeanV31.ReverseRH
  - import LeanV31.CircleHardyCertificate
  - import LeanV31.CanonicalTruncDetector0B21
- declarations:
  - L17: [theorem] final_bridge_closed_core :: theorem final_bridge_closed_core
  - L26: [theorem] final_bridge_closed_core_via_nevanlinna :: theorem final_bridge_closed_core_via_nevanlinna
  - L35: [theorem] final_bridge_closed_via_conj_zero :: theorem final_bridge_closed_via_conj_zero
  - L42: [theorem] final_bridge_closed :: theorem final_bridge_closed
  - L50: [theorem] final_bridge_closed_via_nevanlinna :: theorem final_bridge_closed_via_nevanlinna
  - L59: [theorem] final_bridge_closed_via_detector_conjugation_symmetry :: theorem final_bridge_closed_via_detector_conjugation_symmetry
  - L70: [theorem] final_bridge_closed_via_detector_xi_functional_symmetry :: theorem final_bridge_closed_via_detector_xi_functional_symmetry
  - L83: [theorem] final_bridge_closed_via_hardy_locator_conjugation_symmetry :: theorem final_bridge_closed_via_hardy_locator_conjugation_symmetry
  - L100: [theorem] final_bridge_closed_via_hardy_locator_xi_functional_symmetry :: theorem final_bridge_closed_via_hardy_locator_xi_functional_symmetry
  - L117: [theorem] final_bridge_closed_via_canonical_trunc_conjugation_symmetry :: theorem final_bridge_closed_via_canonical_trunc_conjugation_symmetry
  - L146: [theorem] final_bridge_closed_via_canonical_trunc_xi_functional_symmetry :: theorem final_bridge_closed_via_canonical_trunc_xi_functional_symmetry
  - L175: [theorem] final_bridge_closed_via_conjugation_symmetry :: theorem final_bridge_closed_via_conjugation_symmetry
  - L182: [theorem] final_bridge_closed_via_nevanlinna_conjugation_symmetry :: theorem final_bridge_closed_via_nevanlinna_conjugation_symmetry
  - L190: [theorem] final_bridge_closed_via_xi_functional_symmetry :: theorem final_bridge_closed_via_xi_functional_symmetry
  - L199: [theorem] final_bridge_closed_via_nevanlinna_xi_functional_symmetry :: theorem final_bridge_closed_via_nevanlinna_xi_functional_symmetry
  - L209: [theorem] final_bridge_closed_via_cayley :: theorem final_bridge_closed_via_cayley
  - L219: [theorem] final_bridge_closed_via_cayley_conjugation_symmetry :: theorem final_bridge_closed_via_cayley_conjugation_symmetry
  - L229: [theorem] final_bridge_closed_via_cayley_xi_functional_symmetry :: theorem final_bridge_closed_via_cayley_xi_functional_symmetry
  - L239: [theorem] nevanlinna_route_not_sufficient_without_symmetry :: theorem nevanlinna_route_not_sufficient_without_symmetry :

## LeanV31.HardyPoleLocator
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\HardyPoleLocator.lean
- line_count: 19
- imports:
  - import LeanV31.BDetectorGram
- declarations:
  - L5: [def] HardyPoleLocatorOnCircle :: def HardyPoleLocatorOnCircle (H : Complex -> Complex) : Prop :=
  - L11: [theorem] hardy_pole_locator :: theorem hardy_pole_locator

## LeanV31.LstarPackage
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\LstarPackage.lean
- line_count: 22
- imports:
  - import LeanV31.SchurDeBranges
- declarations:
  - L8: [theorem] lstar_equivalence_package :: theorem lstar_equivalence_package

## LeanV31.MobiusHerglotzB21
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\MobiusHerglotzB21.lean
- line_count: 32
- imports:
  - import LeanV31.EnergyIdentityB21
- declarations:
  - L5: [def] MapsUpperHalfPlaneToItself :: def MapsUpperHalfPlaneToItself (_T : Complex -> Complex) : Prop :=
  - L7: [def] TruncationWeylHerglotzFamily :: def TruncationWeylHerglotzFamily (_m : Nat -> Complex -> Complex) : Prop := Exists fun n0 : Nat => 0 <= n0
  - L13: [theorem] mobius_herglotz :: theorem mobius_herglotz

## LeanV31.NoPoleNevanlinna
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\NoPoleNevanlinna.lean
- line_count: 18
- imports:
  - import LeanV31.SchurDeBranges
- declarations:
  - L5: [def] StripPoleExclusionViaNevanlinna :: def StripPoleExclusionViaNevanlinna (f H : Complex -> Complex) : Prop :=
  - L12: [theorem] no_pole_nevanlinna :: theorem no_pole_nevanlinna

## LeanV31.NoZerosFromHerglotz
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\NoZerosFromHerglotz.lean
- line_count: 17
- imports:
  - import LeanV31.LstarPackage
  - import LeanV31.NoPoleNevanlinna
- declarations:
  - L9: [theorem] no_zeros_from_herglotz :: theorem no_zeros_from_herglotz

## LeanV31.PickHerglotz
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\PickHerglotz.lean
- line_count: 35
- imports:
  - import LeanV31.RHFromAnchor
- declarations:
  - L10: [def] KernelPSDOnUpper :: def KernelPSDOnUpper (K : Complex -> Complex -> Complex) : Prop :=
  - L20: [theorem] pick_herglotz :: theorem pick_herglotz

## LeanV31.PickKernelCompressionB21
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\PickKernelCompressionB21.lean
- line_count: 25
- imports:
  - import LeanV31.DiscreteLagrangeGramB21
- declarations:
  - L5: [def] ScalarPickKernelPSDAtLevel :: def ScalarPickKernelPSDAtLevel (n : Nat) : Prop := Exists fun m : Nat => m <= n
  - L6: [def] RankOneCompressionFormulaAtLevel :: def RankOneCompressionFormulaAtLevel (n : Nat) : Prop := Exists fun m : Nat => m <= n
  - L11: [theorem] pick_kernel_compression :: theorem pick_kernel_compression

## LeanV31.PickSchur
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\PickSchur.lean
- line_count: 28
- imports:
  - import LeanV31.PickHerglotz
- declarations:
  - L13: [theorem] pick_schur :: theorem pick_schur

## LeanV31.PolarizedJKernelB21
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\PolarizedJKernelB21.lean
- line_count: 33
- imports:
  - import LeanV31.MobiusHerglotzB21
- declarations:
  - L5: [def] InUpperB21 :: def InUpperB21 (z : Complex) : Prop := 0 < Complex.im z
  - L7: [def] PolarizedEnergyIdentityAt :: def PolarizedEnergyIdentityAt
  - L10: [def] PolarizedKernelPSDOnUpper :: def PolarizedKernelPSDOnUpper
  - L15: [theorem] polarized_J_kernel :: theorem polarized_J_kernel

## LeanV31.ReverseRH
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\ReverseRH.lean
- line_count: 130
- imports:
  - import LeanV31.WGlobalSchur
  - import LeanV31.RHFromAnchor
  - import LeanV31.RHFromLstar
- declarations:
  - L17: [theorem] reverse_RH_core :: theorem reverse_RH_core
  - L24: [theorem] reverse_RH_core_via_nevanlinna :: theorem reverse_RH_core_via_nevanlinna
  - L34: [theorem] reverse_RH_via_conj_zero :: theorem reverse_RH_via_conj_zero
  - L41: [theorem] reverse_RH :: theorem reverse_RH
  - L49: [theorem] reverse_RH_via_nevanlinna :: theorem reverse_RH_via_nevanlinna
  - L60: [theorem] reverse_RH_via_conjugation_symmetry :: theorem reverse_RH_via_conjugation_symmetry
  - L69: [theorem] reverse_RH_via_nevanlinna_conjugation_symmetry :: theorem reverse_RH_via_nevanlinna_conjugation_symmetry
  - L78: [theorem] reverse_RH_via_xi_functional_symmetry :: theorem reverse_RH_via_xi_functional_symmetry
  - L87: [theorem] reverse_RH_via_nevanlinna_xi_functional_symmetry :: theorem reverse_RH_via_nevanlinna_xi_functional_symmetry
  - L96: [theorem] reverse_RH_via_cayley :: theorem reverse_RH_via_cayley
  - L108: [theorem] reverse_RH_via_cayley_conjugation_symmetry :: theorem reverse_RH_via_cayley_conjugation_symmetry
  - L119: [theorem] reverse_RH_via_cayley_xi_functional_symmetry :: theorem reverse_RH_via_cayley_xi_functional_symmetry

## LeanV31.RHFromAnchor
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\RHFromAnchor.lean
- line_count: 64
- imports:
  - import Mathlib
- declarations:
  - L5: [def] HasOnlyRealZeros :: def HasOnlyRealZeros (f : Complex -> Complex) : Prop :=
  - L8: [def] HolomorphicOnUpperHalfPlane :: def HolomorphicOnUpperHalfPlane (F : Complex -> Complex) : Prop :=
  - L11: [def] HerglotzOnUpperHalfPlane :: def HerglotzOnUpperHalfPlane (H : Complex -> Complex) : Prop :=
  - L15: [def] SchurOnUpperHalfPlane :: def SchurOnUpperHalfPlane (W : Complex -> Complex) : Prop :=
  - L19: [def] HasCanonicalSystemEnergyRealization :: def HasCanonicalSystemEnergyRealization (_H : Complex -> Complex) : Prop :=
  - L26: [theorem] rh_from_anchor :: theorem rh_from_anchor

## LeanV31.RHFromLstar
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\RHFromLstar.lean
- line_count: 140
- imports:
  - import LeanV31.NoZerosFromHerglotz
- declarations:
  - L5: [def] RiemannHypothesis :: def RiemannHypothesis (f : Complex -> Complex) : Prop := HasOnlyRealZeros f
  - L7: [def] ConjugationSymmetric :: def ConjugationSymmetric (f : Complex -> Complex) : Prop :=
  - L10: [def] XiFunctionalSymmetry :: def XiFunctionalSymmetry (f : Complex -> Complex) : Prop :=
  - L14: [theorem] conjugation_symmetric_of_xi_functional_symmetry :: theorem conjugation_symmetric_of_xi_functional_symmetry
  - L20: [theorem] conj_zero_of_conjugation_symmetric :: theorem conj_zero_of_conjugation_symmetric
  - L37: [theorem] rh_from_lstar_core :: theorem rh_from_lstar_core
  - L56: [theorem] zero_free_of_nevanlinna :: theorem zero_free_of_nevanlinna
  - L63: [theorem] rh_from_lstar_core_via_nevanlinna :: theorem rh_from_lstar_core_via_nevanlinna
  - L73: [theorem] rh_from_lstar :: theorem rh_from_lstar
  - L81: [theorem] rh_from_lstar_via_conjugation_symmetry :: theorem rh_from_lstar_via_conjugation_symmetry
  - L91: [theorem] rh_from_lstar_via_xi_functional_symmetry :: theorem rh_from_lstar_via_xi_functional_symmetry
  - L101: [theorem] zero_free_and_conjugation_symmetry_suffice :: theorem zero_free_and_conjugation_symmetry_suffice
  - L110: [theorem] zero_free_on_upper_not_sufficient :: theorem zero_free_on_upper_not_sufficient :
  - L128: [theorem] conjugation_symmetric_not_sufficient :: theorem conjugation_symmetric_not_sufficient :

## LeanV31.SchurDeBranges
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\SchurDeBranges.lean
- line_count: 33
- imports:
  - import LeanV31.PickSchur
- declarations:
  - L5: [def] DeBrangesKernelPSD :: def DeBrangesKernelPSD (_E : Complex -> Complex) : Prop :=
  - L8: [def] WeakHermiteBiehler :: def WeakHermiteBiehler (_E : Complex -> Complex) : Prop :=
  - L11: [def] ZeroFreeOnUpper :: def ZeroFreeOnUpper (E : Complex -> Complex) : Prop :=
  - L21: [theorem] schur_debranges :: theorem schur_debranges

## LeanV31.WBoundedCharacteristic
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\WBoundedCharacteristic.lean
- line_count: 17
- imports:
  - import LeanV31.RHFromAnchor
- declarations:
  - L5: [def] WBoundedCharacteristicOnStrips :: def WBoundedCharacteristicOnStrips (W : Complex -> Complex) : Prop :=
  - L11: [theorem] W_bounded_characteristic :: theorem W_bounded_characteristic

## LeanV31.WGlobalSchur
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\WGlobalSchur.lean
- line_count: 17
- imports:
  - import LeanV31.WStripSchur
- declarations:
  - L5: [def] WGlobalSchurOnUpperHalfPlane :: def WGlobalSchurOnUpperHalfPlane (W : Complex -> Complex) : Prop :=
  - L11: [theorem] W_global_schur :: theorem W_global_schur

## LeanV31.WStripSchur
- file: c:\gp_work\수학\핵심증명\audit\formalization\lean_v3_1\LeanV31\WStripSchur.lean
- line_count: 18
- imports:
  - import LeanV31.WBoundedCharacteristic
- declarations:
  - L5: [def] WStripSchurOnUpperStrip :: def WStripSchurOnUpperStrip (W : Complex -> Complex) : Prop :=
  - L12: [theorem] W_strip_schur :: theorem W_strip_schur

