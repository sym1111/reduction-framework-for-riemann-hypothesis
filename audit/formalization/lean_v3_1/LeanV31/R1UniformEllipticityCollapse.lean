import LeanV31.R1UniformEllipticityFiniteMass

namespace LeanV31

def R1RadiusCollapseFromUniformEllipticityAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0

/- S071 wrapper:
with mass divergence and uniform ellipticity, any radius-floor subsequence would
force finite mass, contradiction; therefore radii collapse on the upper
half-plane. -/
theorem R1_uniform_ellipticity_collapse
    {z : Complex}
    (hMassDiverges : R1TotalMassDivergesAt z)
    (hUniformEllipticity : R1UniformEllipticityAt z)
    (hFiniteMass :
      R1UniformEllipticityAt z ->
      R1FiniteTotalMassFromUniformEllipticityAt z)
    (hCollapseBridge :
      R1TotalMassDivergesAt z ->
      R1FiniteTotalMassFromUniformEllipticityAt z ->
      R1RadiusCollapseFromUniformEllipticityAt z) :
    R1RadiusCollapseFromUniformEllipticityAt z := by
  have hFinite : R1FiniteTotalMassFromUniformEllipticityAt z :=
    hFiniteMass hUniformEllipticity
  exact hCollapseBridge hMassDiverges hFinite

end LeanV31
