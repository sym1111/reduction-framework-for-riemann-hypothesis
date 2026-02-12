import LeanV31.LstarPackage
import LeanV31.RHFromLstar
import LeanV31.RHFromAnchor

namespace LeanV31

abbrev DeBrangesKernelPositiveSemidefinite (E : Complex -> Complex) : Prop :=
  DeBrangesKernelPSD E
abbrev CanonicalSystemGlobalJContractive (H : Complex -> Complex) : Prop :=
  HasCanonicalSystemEnergyRealization H

/- S001 wrapper:
main reduction packages the manuscript equivalences between RH, Herglotz/Schur,
Pick-kernel PSD, de Branges kernel PSD, and canonical-system realization. -/
theorem main_reduction
    {f H W E : Complex -> Complex}
    (hAB : RiemannHypothesis f -> HerglotzOnUpperHalfPlane H)
    (hBA : HerglotzOnUpperHalfPlane H -> RiemannHypothesis f)
    (hBC : HerglotzOnUpperHalfPlane H -> SchurOnUpperHalfPlane W)
    (hCB : SchurOnUpperHalfPlane W -> HerglotzOnUpperHalfPlane H)
    (hBD : HerglotzOnUpperHalfPlane H -> KernelPSDOnUpper (pickKernelH H))
    (hDB : KernelPSDOnUpper (pickKernelH H) -> HerglotzOnUpperHalfPlane H)
    (hCE : SchurOnUpperHalfPlane W -> DeBrangesKernelPositiveSemidefinite E)
    (hEC : DeBrangesKernelPositiveSemidefinite E -> SchurOnUpperHalfPlane W)
    (hBF : HerglotzOnUpperHalfPlane H -> CanonicalSystemGlobalJContractive H)
    (hFB : CanonicalSystemGlobalJContractive H -> HerglotzOnUpperHalfPlane H) :
    (RiemannHypothesis f <-> HerglotzOnUpperHalfPlane H) /\
      (HerglotzOnUpperHalfPlane H <-> SchurOnUpperHalfPlane W) /\
      (HerglotzOnUpperHalfPlane H <-> KernelPSDOnUpper (pickKernelH H)) /\
      (SchurOnUpperHalfPlane W <-> DeBrangesKernelPositiveSemidefinite E) /\
      (HerglotzOnUpperHalfPlane H <-> CanonicalSystemGlobalJContractive H) := by
  refine And.intro (Iff.intro hAB hBA) ?_
  refine And.intro (Iff.intro hBC hCB) ?_
  refine And.intro (Iff.intro hBD hDB) ?_
  exact And.intro (Iff.intro hCE hEC) (Iff.intro hBF hFB)

end LeanV31
