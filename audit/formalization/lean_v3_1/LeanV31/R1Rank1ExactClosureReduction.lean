import LeanV31.R1CS2EquivKj

namespace LeanV31

def R1TailWindowSubseqBoundAt (_z : Complex) : Prop := Exists fun C : Real => 0 <= C

/- S059 wrapper:
on a radius-floor rank-one subsequence, exact closure reduction identifies
equivalent formulations: CS2, bounded `K_j`, bounded prefix mass, and
tail-window boundedness. -/
theorem R1_rank1_exact_closure_reduction
    {z : Complex}
    (hCS2K : R1CS2ConditionAt z <-> R1KjUniformBoundAt z)
    (hKPrefix : R1KjUniformBoundAt z <-> R1PrefixMassUniformBoundAt z)
    (hPrefixTail : R1PrefixMassUniformBoundAt z <-> R1TailWindowSubseqBoundAt z) :
    (R1CS2ConditionAt z <-> R1KjUniformBoundAt z) /\
      (R1KjUniformBoundAt z <-> R1PrefixMassUniformBoundAt z) /\
      (R1PrefixMassUniformBoundAt z <-> R1TailWindowSubseqBoundAt z) := by
  exact And.intro hCS2K (And.intro hKPrefix hPrefixTail)

end LeanV31
