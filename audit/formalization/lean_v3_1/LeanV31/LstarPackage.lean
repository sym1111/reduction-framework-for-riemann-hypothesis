import LeanV31.SchurDeBranges

namespace LeanV31

/- S020 wrapper:
`L*` equivalence package as a bundled statement collecting the bridge
equivalences used in the manuscript chain. -/
theorem lstar_equivalence_package
    {H W E : Complex -> Complex}
    (h1 : HerglotzOnUpperHalfPlane H <-> SchurOnUpperHalfPlane W)
    (h2 : HerglotzOnUpperHalfPlane H <-> KernelPSDOnUpper (pickKernelH H))
    (h3 : SchurOnUpperHalfPlane W <-> KernelPSDOnUpper (pickKernelW W))
    (h4 : SchurOnUpperHalfPlane W <-> DeBrangesKernelPSD E)
    (h5 : SchurOnUpperHalfPlane W <-> WeakHermiteBiehler E) :
    (HerglotzOnUpperHalfPlane H <-> SchurOnUpperHalfPlane W) /\
      (HerglotzOnUpperHalfPlane H <-> KernelPSDOnUpper (pickKernelH H)) /\
      (SchurOnUpperHalfPlane W <-> KernelPSDOnUpper (pickKernelW W)) /\
      (SchurOnUpperHalfPlane W <-> DeBrangesKernelPSD E) /\
      (SchurOnUpperHalfPlane W <-> WeakHermiteBiehler E) := by
  exact And.intro h1 (And.intro h2 (And.intro h3 (And.intro h4 h5)))

end LeanV31
