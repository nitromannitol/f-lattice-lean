import FLatticePaper.Plane.Induction.InternalReturns
import FLatticePaper.Plane.Induction.CanonicalSigned

/-! # Prescribed arrows of the route fields (`h3`, `h1` at the west neighbour, `v3` at the even source)

A free root `c` with zero Laplacian keeps its prescribed input: `PrescribedAt` gives `P c j ↔ j = c + prescribedH η c` on the free H
cut and `P c j ↔ j = c + prescribedV η c` on the free V cut. The sign-free prescriptions are `(1, 0)` at even H sites and `(0, 1)` at
odd H sites other than `hFirst`; the even V prescription is `(η, 0)` except at `vFirst`, where it is `(1, 0)`. -/

namespace FLatticePaper.RoutePresc

open FLatticePaper FLatticePaper.Induction

/-- The odd H prescription `(0, 1)`, off `hFirst` (for `hLast` it is `(0, 1)` as well). -/
theorem prescribedH_odd_ne_first (frame : ChildFrame) (η : ℤ) {z : Site} (hz : ¬ EvenSite z)
    (h1 : z ≠ FLatticePaper.Induction.hFirst) : frame.prescribedH η z = (0, 1) := by
  unfold ChildFrame.prescribedH
  by_cases h2 : z = frame.hLast
  · rw [if_neg h1, if_pos h2]
  · rw [if_neg h1, if_neg h2, if_neg hz]

/-- The even V prescription `(η, 0)`, at an even site off `vFirst` (and at `vFirst` when `η = 1`). -/
theorem prescribedV_even_eta (frame : ChildFrame) (η : ℤ) {q : Site} (hq : EvenSite q)
    (h : q ≠ FLatticePaper.Induction.vFirst ∨ η = 1) : frame.prescribedV η q = (η, 0) := by
  unfold ChildFrame.prescribedV
  by_cases h1 : q = FLatticePaper.Induction.vFirst
  · have hη : η = 1 := h.resolve_left (fun h' => h' h1)
    rw [if_pos h1, hη]
  · by_cases h2 : q = frame.vLast
    · rw [if_neg h1, if_pos h2]
    · rw [if_neg h1, if_neg h2, if_pos hq]

/-- **The middle arrow `z+W → z+S... ` of an even free H root (the `h3` first arrow).** The west neighbour `q = (z.1 - 1, z.2)` is an
odd free H root with zero Laplacian, or black; its prescription `(0, 1)` gives the arrow to `(z.1 - 1, z.2 + 1)`. -/
theorem h3_arrow_a {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0) {z : Site}
    (hq : (z.1 - 1, z.2) ∈ frame.freeH) (hodd : ¬ EvenSite (z.1 - 1, z.2))
    (hne : (z.1 - 1, z.2) ≠ FLatticePaper.Induction.hFirst) :
    laplacian G (z.1 - 1, z.2) = -1 ∨ C.policy (z.1 - 1, z.2) (z.1 - 1, z.2 + 1) := by
  by_cases hb : laplacian G (z.1 - 1, z.2) = -1
  · exact Or.inl hb
  · right
    have hw : laplacian G (z.1 - 1, z.2) = 0 := (hbin _).resolve_left hb
    refine (C.prescribed.1 (z.1 - 1, z.2) hq hw _).mpr ?_
    rw [prescribedH_odd_ne_first frame η hodd hne]
    ext <;> simp

/-- **The arrow `z+W → z` of an even free H root's west neighbour (the `h1` third arrow).** The west neighbour `q = (z.1 - 1, z.2)` is
an even free H root with zero Laplacian, its prescription `(1, 0)` keeps `z`. -/
theorem h1_arrow_c {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0) {z : Site}
    (hq : (z.1 - 1, z.2) ∈ frame.freeH) (hev : EvenSite (z.1 - 1, z.2)) :
    laplacian G (z.1 - 1, z.2) = -1 ∨ C.policy (z.1 - 1, z.2) z := by
  by_cases hb : laplacian G (z.1 - 1, z.2) = -1
  · exact Or.inl hb
  · right
    have hw : laplacian G (z.1 - 1, z.2) = 0 := (hbin _).resolve_left hb
    refine (C.prescribed.1 (z.1 - 1, z.2) hq hw _).mpr ?_
    rw [FLatticePaper.InternalReturns.prescribedH_even frame η hev]
    ext <;> simp

/-- **The first arrow of the `v3` row at a free odd V root `z`**: the even neighbour `q = (z.1, z.2 - -η)` is a free V root, its
prescription `(η, 0)` (off `vFirst`) keeps `(z.1 - -η, z.2 - -η)`. -/
theorem v3_arrow_a0 {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0) (hη : η = 1 ∨ η = -1) {z : Site}
    (hodd : ¬ EvenSite z) (hne : ¬ (η = -1 ∧ z = (0, 1)))
    (hq : (z.1, z.2 - -η) ∈ frame.freeV) :
    laplacian G (z.1, z.2 - -η) = -1 ∨ C.policy (z.1, z.2 - -η) (z.1 - -η, z.2 - -η) := by
  have hev : EvenSite (z.1, z.2 - -η) := by
    unfold EvenSite at hodd ⊢
    rcases hη with rfl | rfl <;> omega
  by_cases hb : laplacian G (z.1, z.2 - -η) = -1
  · exact Or.inl hb
  · right
    have hw : laplacian G (z.1, z.2 - -η) = 0 := (hbin _).resolve_left hb
    have hcond : (z.1, z.2 - -η) ≠ FLatticePaper.Induction.vFirst ∨ η = 1 := by
      by_cases hη1 : η = 1
      · exact Or.inr hη1
      · left
        intro h
        apply hne
        have hm1 : η = -1 := by omega
        refine ⟨hm1, ?_⟩
        have h1 : z.1 = 0 := by
          have := congrArg Prod.fst h
          simpa [FLatticePaper.Induction.vFirst, hm1] using this
        have h2 : z.2 = 1 := by
          have := congrArg Prod.snd h
          simp [FLatticePaper.Induction.vFirst, hm1] at this
          omega
        exact Prod.ext h1 h2
    refine (C.prescribed.2 (z.1, z.2 - -η) hq hw _).mpr ?_
    rw [prescribedV_even_eta frame η hev hcond]
    ext <;> simp

end FLatticePaper.RoutePresc
