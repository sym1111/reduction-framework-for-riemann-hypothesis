import Mathlib

namespace LeanV31

open Set

/- Algebraic tail:
if `m1 - m2` is constant and vanishes at one anchor point, then `m1 = m2`. -/
theorem constantGap_anchor_eq
    {D : Type*} {m1 m2 : D -> Real}
    (hconst : exists c : Real, forall z : D, m1 z - m2 z = c)
    (z0 : D)
    (h0 : m1 z0 = m2 z0) :
    forall z : D, m1 z = m2 z := by
  rcases hconst with ⟨c, hc⟩
  have hc0 : c = 0 := by
    have hz0 : c = m1 z0 - m2 z0 := by simpa using (hc z0).symm
    simpa [h0] using hz0
  intro z
  have hz : m1 z - m2 z = 0 := by simpa [hc0] using hc z
  exact sub_eq_zero.mp hz

/- Identity-theorem wrapper for derivatives:
if derivative equality holds on a nonempty open subset `u`, then it holds on all connected `s`. -/
theorem deriv_eqOn_of_eqOn_nonempty_open_subset
    {s u : Set Complex}
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (hu : IsOpen u) (hu_sub : u ⊆ s) (hu_nonempty : u.Nonempty)
    {m1 m2 : Complex -> Complex}
    (hm1 : DifferentiableOn Complex m1 s)
    (hm2 : DifferentiableOn Complex m2 s)
    (hderiv_u : u.EqOn (deriv m1) (deriv m2)) :
    s.EqOn (deriv m1) (deriv m2) := by
  rcases hu_nonempty with ⟨z0, hz0u⟩
  have hz0s : z0 ∈ s := hu_sub hz0u
  have h_an1 : AnalyticOnNhd Complex (deriv m1) s := by
    exact (hm1.analyticOnNhd hs).deriv
  have h_an2 : AnalyticOnNhd Complex (deriv m2) s := by
    exact (hm2.analyticOnNhd hs).deriv
  have h_event : deriv m1 =ᶠ[nhds z0] deriv m2 := by
    filter_upwards [hu.mem_nhds hz0u] with z hzu
    exact hderiv_u hzu
  exact h_an1.eqOn_of_preconnected_of_eventuallyEq h_an2 hconn hz0s h_event

/- S138 wrapper:
on an open preconnected set `s`, local derivative equality on a nonempty open `u`
implies the difference `m1 - m2` is constant on all of `s`. -/
theorem local_diffquot_constant_gap
    {s u : Set Complex}
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (hu : IsOpen u) (hu_sub : u ⊆ s) (hu_nonempty : u.Nonempty)
    {m1 m2 : Complex -> Complex}
    (hm1 : DifferentiableOn Complex m1 s)
    (hm2 : DifferentiableOn Complex m2 s)
    (hderiv_u : u.EqOn (deriv m1) (deriv m2)) :
    exists c : Complex, s.EqOn (fun z => m1 z - m2 z) (fun _ => c) := by
  have hderiv_s : s.EqOn (deriv m1) (deriv m2) :=
    deriv_eqOn_of_eqOn_nonempty_open_subset hs hconn hu hu_sub hu_nonempty hm1 hm2 hderiv_u
  rcases hs.exists_eq_add_of_deriv_eq hconn hm1 hm2 hderiv_s with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro z hz
  have hz' : m1 z = m2 z + c := hc hz
  calc
    m1 z - m2 z = (m2 z + c) - m2 z := by simp [hz']
    _ = c := by ring

/- S139 wrapper:
local derivative match on a nonempty open set plus one anchor equality gives equality on all `s`. -/
theorem local_derivative_anchor_equal
    {s u : Set Complex}
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (hu : IsOpen u) (hu_sub : u ⊆ s) (hu_nonempty : u.Nonempty)
    {m1 m2 : Complex -> Complex}
    (hm1 : DifferentiableOn Complex m1 s)
    (hm2 : DifferentiableOn Complex m2 s)
    (hderiv_u : u.EqOn (deriv m1) (deriv m2))
    {z0 : Complex} (hz0u : z0 ∈ u) (h0 : m1 z0 = m2 z0) :
    s.EqOn m1 m2 := by
  rcases
      local_diffquot_constant_gap hs hconn hu hu_sub hu_nonempty hm1 hm2 hderiv_u with
    ⟨c, hgap⟩
  have hz0s : z0 ∈ s := hu_sub hz0u
  have hc0 : c = 0 := by
    have hz0gap : m1 z0 - m2 z0 = c := hgap hz0s
    have hz0gap' : c = m1 z0 - m2 z0 := hz0gap.symm
    simpa [h0] using hz0gap'
  intro z hz
  have hzgap : m1 z - m2 z = c := hgap hz
  have hz0eq : m1 z - m2 z = 0 := by simpa [hc0] using hzgap
  exact sub_eq_zero.mp hz0eq

/- S140 wrapper:
local derivative match plus anchor gives global equality, and then Pick kernels agree. -/
theorem pick_kernel_equal
    {s u : Set Complex}
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (hu : IsOpen u) (hu_sub : u ⊆ s) (hu_nonempty : u.Nonempty)
    {m1 m2 : Complex -> Complex}
    (hm1 : DifferentiableOn Complex m1 s)
    (hm2 : DifferentiableOn Complex m2 s)
    (hderiv_u : u.EqOn (deriv m1) (deriv m2))
    {z0 : Complex} (hz0u : z0 ∈ u) (h0 : m1 z0 = m2 z0) :
    s.EqOn m1 m2 ∧
      (forall z, z ∈ s -> forall w, w ∈ s -> z ≠ w ->
        (m1 w - m1 z) / (w - z) = (m2 w - m2 z) / (w - z)) := by
  have hEq : s.EqOn m1 m2 :=
    local_derivative_anchor_equal hs hconn hu hu_sub hu_nonempty hm1 hm2 hderiv_u hz0u h0
  refine ⟨hEq, ?_⟩
  intro z hz w hw hzw
  have hzEq : m1 z = m2 z := hEq hz
  have hwEq : m1 w = m2 w := hEq hw
  simp [hwEq, hzEq]

end LeanV31
