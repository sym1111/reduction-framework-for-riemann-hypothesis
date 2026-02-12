import LeanV31.R1KjPrefixEquivRank1
import LeanV31.R1CS2Equiv

namespace LeanV31

/- S058 wrapper:
CS2 on the subsequence is equivalent to uniform boundedness of `K_j`. -/
theorem R1_CS2_equiv_Kj
    {z : Complex}
    (hForward :
      R1CS2ConditionAt z ->
      R1KjUniformBoundAt z)
    (hBackward :
      R1KjUniformBoundAt z ->
      R1CS2ConditionAt z) :
    R1CS2ConditionAt z <-> R1KjUniformBoundAt z := by
  exact Iff.intro hForward hBackward

end LeanV31
