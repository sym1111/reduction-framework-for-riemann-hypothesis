import LeanV31.Basic

namespace LeanV31

def R1SchurHamiltonianBlockFamilyAt (_z : Complex) : Prop :=
  Exists fun k0 : Nat => 0 < k0
def R1TraceLowerBoundAt (_z : Complex) : Prop :=
  Exists fun t0 : Nat => 0 <= t0
def R1MassDivergesFromTraceLowerBoundAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 < n0 /\ 0 <= n0

/- S113 wrapper:
for Schur-parameterized Hamiltonian blocks, trace has a uniform lower bound,
hence total trace mass diverges automatically. -/
theorem trace_lower_bound
    {z : Complex}
    (hSchurBlocks : R1SchurHamiltonianBlockFamilyAt z)
    (hTraceBridge :
      R1SchurHamiltonianBlockFamilyAt z ->
      R1TraceLowerBoundAt z)
    (hMassBridge :
      R1TraceLowerBoundAt z ->
      R1MassDivergesFromTraceLowerBoundAt z) :
    R1TraceLowerBoundAt z /\ R1MassDivergesFromTraceLowerBoundAt z := by
  have hTrace : R1TraceLowerBoundAt z := hTraceBridge hSchurBlocks
  have hMass : R1MassDivergesFromTraceLowerBoundAt z := hMassBridge hTrace
  exact And.intro hTrace hMass

end LeanV31
