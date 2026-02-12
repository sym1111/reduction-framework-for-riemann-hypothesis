import LeanV31.R1Rank1RadiusfloorDichotomy
import LeanV31.R1CanonicalFormulaCore

namespace LeanV31

def R1TotalMassDivergesAt (_z : Complex) : Prop :=
  forall M : Real, Exists fun N : Nat => M <= R1PrefixTraceMassAt N
def R1PrefixMassDivergesAlongSubseqAt (_z : Complex) : Prop :=
  forall u : Nat -> Nat, StrictMono u ->
    forall M : Real, Exists fun N : Nat => M <= R1PrefixTraceMassAt (u N)

private theorem nat_le_strictMono_self
    {u : Nat -> Nat}
    (hu : StrictMono u) :
    forall n : Nat, n <= u n := by
  intro n
  induction n with
  | zero =>
      exact Nat.zero_le (u 0)
  | succ n ih =>
      have hsucc : Nat.succ n <= Nat.succ (u n) := Nat.succ_le_succ ih
      have hlt : u n < u (Nat.succ n) := hu (Nat.lt_succ_self n)
      exact le_trans hsucc (Nat.succ_le_of_lt hlt)

/- S062 wrapper:
with nonnegative trace increments, total-mass divergence forces divergence of
prefix masses along every strictly increasing subsequence. -/
theorem R1_prefix_subsequence_divergence
    {z : Complex}
    (hMassDiverges : R1TotalMassDivergesAt z) :
    R1PrefixMassDivergesAlongSubseqAt z := by
  intro u hu M
  cases hMassDiverges M with
  | intro N hMN =>
      refine Exists.intro N ?_
      have hNleuNnat : N <= u N := nat_le_strictMono_self hu N
      have hNleuNreal :
          R1PrefixTraceMassAt N <= R1PrefixTraceMassAt (u N) := by
        have hsubset : Finset.range N ⊆ Finset.range (u N) := by
          intro x hx
          exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hNleuNnat)
        have hnonneg :
            forall i, i ∈ Finset.range (u N) -> i ∉ Finset.range N -> 0 <= R1HamiltonianTraceAt i := by
          intro i _hi _hnin
          have hi0 : (0 : Real) <= (i : Real) := by
            exact_mod_cast (Nat.zero_le i)
          have h1 : (0 : Real) <= (1 : Real) := by
            norm_num
          simpa [R1HamiltonianTraceAt] using add_nonneg hi0 h1
        simpa [R1PrefixTraceMassAt] using
          (Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg)
      exact le_trans hMN hNleuNreal

end LeanV31
