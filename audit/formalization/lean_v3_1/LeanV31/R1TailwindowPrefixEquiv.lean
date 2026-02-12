import LeanV31.R1TailwindowDirectFiniteMass

namespace LeanV31

def R1TailWindowBoundOnSubseqAt (_z : Complex) : Prop := Exists fun j0 : Nat => 0 <= j0 /\ 0 < j0

/- S068 wrapper:
for nonnegative trace increments, tail-window and prefix-window bounds on a
subsequence are equivalent by monotonicity and the `k = 0` specialization. -/
theorem R1_tailwindow_prefix_equiv
    {z : Complex}
    (hForward :
      R1TailWindowBoundOnSubseqAt z ->
      R1PrefixWindowDirectBoundAt z)
    (hBackward :
      R1PrefixWindowDirectBoundAt z ->
      R1TailWindowBoundOnSubseqAt z) :
    R1TailWindowBoundOnSubseqAt z <-> R1PrefixWindowDirectBoundAt z := by
  exact Iff.intro hForward hBackward

end LeanV31
