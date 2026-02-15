import LeanV32
import LeanV32.GoldenAlphaWitness
import LeanV32.XiGoldenDocking

namespace LeanV32

/-!
Convenience build target for the v3.2 track.

`LeanV32` itself intentionally stays light-weight, while `GoldenAlphaWitness` is a
heavy, kernel-checked numeric certificate. Importing both here allows running:

`lake --wfail build LeanV32.BuildAll`

to ensure the full v3.2 algebraic chain + the golden witness stay compiling.
-/

end LeanV32
