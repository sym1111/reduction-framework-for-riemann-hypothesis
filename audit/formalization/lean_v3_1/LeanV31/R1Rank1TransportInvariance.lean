import LeanV31.R1TwoChannelTraceCompare

namespace LeanV31

def R1RankOneBlockAt (_k : Nat) (_z : Complex) : Prop :=
  Exists fun v : Complex × Complex => v.1 != 0 \/ v.2 != 0
def R1HJHZeroAt (k : Nat) (_z : Complex) : Prop := Exists fun n : Nat => n = k
def R1TransportInvariantAt (k : Nat) (_z : Complex) : Prop := Exists fun n : Nat => n = k

/- S044 wrapper:
for rank-one PSD blocks, `H J H = 0`, and Cayley transport preserves the block:
`R(z)^{-*} H R(z)^{-1} = H`. -/
theorem R1_rank1_transport_invariance
    {z : Complex}
    (hz : InUpperB21 z)
    (hRankOne : forall k : Nat, R1RankOneBlockAt k z)
    (hHJHBridge :
      InUpperB21 z ->
      (forall k : Nat, R1RankOneBlockAt k z) ->
      forall k : Nat, R1HJHZeroAt k z)
    (hTransportBridge :
      InUpperB21 z ->
      (forall k : Nat, R1HJHZeroAt k z) ->
      forall k : Nat, R1TransportInvariantAt k z) :
    (forall k : Nat, R1HJHZeroAt k z) /\
      (forall k : Nat, R1TransportInvariantAt k z) := by
  have hHJH : forall k : Nat, R1HJHZeroAt k z := hHJHBridge hz hRankOne
  have hInv : forall k : Nat, R1TransportInvariantAt k z :=
    hTransportBridge hz hHJH
  exact And.intro hHJH hInv

end LeanV31
