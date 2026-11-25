import FLatticePaper.Plane.Induction.FanAcyclic
import FLatticePaper.Plane.Induction.FanPropagation
import FLatticePaper.Plane.Induction.ContactCone
import FLatticePaper.Plane.Induction.ConeRoot
import FLatticePaper.Plane.Induction.RegionalCompat

/-! # The contact fan as an abstract region (the start is forced east)

`ReflectedFan.fan_start_forced` runs `RegionalCompat.regional_forced` on the contact fan of a cone, in the frame's strict interior. The
argument uses only: the binary laplacian, the cone window (`WindowOn`), the closure of the fan under its contact inputs (`hclose`, which
`AllBranchFan.contactFan_mem_of_input` supplies for a frame), the parabola Laplacians and the rank `fanRank`. This module states it for
an arbitrary field `F` and an arbitrary region `R`, so that it applies to the rotated residual of the long V case, whose strict
interior is the `(N, D)`-rectangle. The closure `hclose` is the named input of that instance. -/

namespace FLatticePaper.FanRegion

open FLatticePaper FLatticePaper.Induction FLatticePaper.ContactCone FLatticePaper.FanAcyclic FLatticePaper.FanPropagation
  FLatticePaper.CapRay

/-- The contact fan of the cone of base `b` and depth `K` in the region `R`: cone sites of `R` that are contacts of the parabola. -/
def fanSet (R : Site → Prop) (F : Field) (b : Site) (K : ℕ) : Set Site :=
  {x | (R x ∧ ConeRoot b K x) ∧ F x = parabolaField b.2 x}

/-- The two inputs of a fan site have nonnegative excess, and the sum is the laplacian excess: both are contacts. -/
theorem fan_both_inputs_R {R : Site → Prop} {F : Field} {b : Site} {K : ℕ}
    (hwin : WindowOn (fun x => R x ∧ ConeRoot b K x) F (fun i => parabolaField b.2 i))
    {x : Site} (hx : x ∈ fanSet R F b K)
    (hl : laplacian F x = laplacian (parabolaField b.2) x) :
    F (incomingNeg x) = parabolaField b.2 (incomingNeg x) ∧
      F (incomingPos x) = parabolaField b.2 (incomingPos x) := by
  obtain ⟨hcone, hc⟩ := hx
  have key := excess_sum (F := F) (m := parabolaField b.2) hc
  rw [hl] at key
  have hn : parabolaField b.2 (incomingNeg x) ≤ F (incomingNeg x) := hwin x hcone (incomingNeg x) (Or.inl rfl)
  have hp : parabolaField b.2 (incomingPos x) ≤ F (incomingPos x) := hwin x hcone (incomingPos x) (Or.inr rfl)
  constructor <;> omega

/-- An even contact of the fan is white. -/
theorem contact_even_white_R {R : Site → Prop} {F : Field} {b : Site} {K : ℕ}
    (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hwin : WindowOn (fun x => R x ∧ ConeRoot b K x) F (fun i => parabolaField b.2 i))
    {x : Site} (hx : x ∈ fanSet R F b K) (he : EvenSite x) : laplacian F x = 0 := by
  obtain ⟨hcone, hc⟩ := hx
  exact even_contact_white (hbin x) hc he (hwin x hcone (incomingNeg x) (Or.inl rfl))
    (hwin x hcone (incomingPos x) (Or.inr rfl))

/-- An odd white contact has a contact vertical input. -/
theorem contact_odd_input_R {R : Site → Prop} {F : Field} {b : Site} {K : ℕ}
    (hwin : WindowOn (fun x => R x ∧ ConeRoot b K x) F (fun i => parabolaField b.2 i))
    {x : Site} (hx : x ∈ fanSet R F b K) (ho : ¬ EvenSite x) (hw : laplacian F x = 0) :
    ∃ y, (y = incomingNeg x ∨ y = incomingPos x) ∧ F y = parabolaField b.2 y := by
  obtain ⟨hcone, hc⟩ := hx
  have key := excess_sum (F := F) (m := parabolaField b.2) hc
  rw [parabola_lap_odd b.2 x ho, hw] at key
  have hn : parabolaField b.2 (incomingNeg x) ≤ F (incomingNeg x) := hwin x hcone (incomingNeg x) (Or.inl rfl)
  have hp : parabolaField b.2 (incomingPos x) ≤ F (incomingPos x) := hwin x hcone (incomingPos x) (Or.inr rfl)
  by_cases hn0 : F (incomingNeg x) = parabolaField b.2 (incomingNeg x)
  · exact ⟨incomingNeg x, Or.inl rfl, hn0⟩
  · by_cases hp0 : F (incomingPos x) = parabolaField b.2 (incomingPos x)
    · exact ⟨incomingPos x, Or.inr rfl, hp0⟩
    · exfalso
      omega

/-- **The fan start is forced to its east input (abstract region form).** If the contact fan is closed under its contact inputs in the
region `R` (`hclose`), and the start is a fan site with even parity whose forced edge leaves the region, then the forced edge is its
east edge. The argument is `RegionalCompat.regional_forced` on the fan, with the rank `fanRank`. -/
theorem fan_start_forced_R {R : Site → Prop} {F : Field}
    (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0) {b start : Site} {K : ℕ}
    (hwin : WindowOn (fun x => R x ∧ ConeRoot b K x) F (fun i => parabolaField b.2 i))
    (hclose : ∀ x ∈ fanSet R F b K, ∀ u : Site, (u = incomingNeg x ∨ u = incomingPos x) →
      (EvenSite x → u = incomingPos x) → R u → F u = parabolaField b.2 u → u ∈ fanSet R F b K)
    (hstart : start ∈ fanSet R F b K) (heven : EvenSite start) {o : Site}
    (ho : FLatticePaper.W1.ForcedEdgeIn F R (fun _ _ => False) start o) :
    o = incomingPos start := by
  have hreg := FLatticePaper.RegionalCompat.regional_forced (F := F) (R := R)
    (S := fun x => x ∈ fanSet R F b K)
    (C := fun x u => (EvenSite x ∧ u = incomingPos x ∧ F u = parabolaField b.2 u) ∨
      (¬ EvenSite x ∧ (u = incomingNeg x ∨ u = incomingPos x) ∧ F u = parabolaField b.2 u))
    (r := fanRank)
    (by
      intro x u hCu
      rcases hCu with ⟨he, hu, -⟩ | ⟨hne, hu, -⟩
      · rw [hu]
        exact fanRank_east_of_even x he
      · exact fanRank_vertical_of_odd x hne u hu)
    (by
      intro x u hx hCu hR
      rcases hCu with ⟨he, hu, hcu⟩ | ⟨hne, hu, hcu⟩
      · exact hclose x hx u (Or.inr hu) (fun _ => hu) hR hcu
      · exact hclose x hx u hu (fun h => absurd h hne) hR hcu)
    (by
      intro x hx hl u hu
      have hodd : ¬ EvenSite x := by
        intro he
        have h0 := contact_even_white_R hbin hwin hx he
        rw [hl] at h0
        norm_num at h0
      have hsum := fan_both_inputs_R hwin hx (by rw [hl, parabola_lap_odd b.2 x hodd])
      rcases hu with rfl | rfl
      · exact Or.inr ⟨hodd, Or.inl rfl, hsum.1⟩
      · exact Or.inr ⟨hodd, Or.inr rfl, hsum.2⟩)
    (by
      intro x hx hl
      by_cases he : EvenSite x
      · have hsum := fan_both_inputs_R hwin hx (by rw [hl, parabola_lap_even b.2 x he])
        exact ⟨incomingPos x, Or.inl ⟨he, rfl, hsum.2⟩, Or.inr rfl⟩
      · obtain ⟨y, hy, hyc⟩ := contact_odd_input_R hwin hx he hl
        exact ⟨y, Or.inr ⟨he, hy, hyc⟩, hy⟩)
    ho hstart
  rcases hreg with ⟨-, h, -⟩ | ⟨hne, -⟩
  · exact h
  · exact absurd heven hne

end FLatticePaper.FanRegion
