import FLatticePaper.Plane.RestrictedBellmanRank

/-! Task 72 (TIP_THEOREM, the two-edge cut-tip escape), in the restricted escape game of `RestrictedBellmanRank`.

A root `r` escapes at depth two through a white route `r → u → y` when `u` is an input of `r`, `y` is an input of `u`, the two
sites are white (charge `0`), both edges are permitted, and the escape port `y` has grade below the level. This module proves that
abstract statement (`two_edge_escape`), and instantiates it at the two cut-tip routes of TIP_THEOREM:

* W0: the odd root `v + (1,0)` takes its north input `v + (1,1)` (even), then its west input `v + (0,1)`;
* W1: the even root `v` takes its west input `v + (−1,0)` (odd), then its north input `v + (−1,1)`.

The field values (whiteness, permits, the grade decrease `J: 0 → −1` at the port) are hypotheses: TIP_THEOREM derives them from the
two-sheet fields, which are not modelled here. -/

namespace FLatticePaper

open Farey

/-- A white site whose permitted input `y` has grade below the level escapes at depth one. -/
theorem escape_one_of_white {field grade : Field} {permits : Site → Site → Prop} {level : ℤ} {u y : Site}
    (hu : laplacian field u = 0) (hy : y = incomingNeg u ∨ y = incomingPos u) (hpu : permits u y)
    (hgy : grade y < level) : RestrictedEscapesWithin field grade permits level 1 u := by
  refine Or.inr (Or.inr ⟨hu, ?_⟩)
  rcases hy with rfl | rfl
  · exact Or.inl ⟨hpu, hgy⟩
  · exact Or.inr ⟨hpu, hgy⟩

/-- **The two-edge escape.** A white root `r` with a white permitted input `u` whose permitted input `y` has grade below the level
escapes at depth two. -/
theorem two_edge_escape {field grade : Field} {permits : Site → Site → Prop} {level : ℤ} {r u y : Site}
    (hr : laplacian field r = 0) (hu_in : u = incomingNeg r ∨ u = incomingPos r) (hru : permits r u)
    (hu : laplacian field u = 0) (hy_in : y = incomingNeg u ∨ y = incomingPos u) (hpu : permits u y)
    (hy : grade y < level) : RestrictedEscapesWithin field grade permits level 2 r := by
  have h1 := escape_one_of_white hu hy_in hpu hy
  rcases hu_in with rfl | rfl
  · exact Or.inr (Or.inr ⟨hr, Or.inl ⟨hru, h1⟩⟩)
  · exact Or.inr (Or.inr ⟨hr, Or.inr ⟨hru, h1⟩⟩)

/-- **W0 two-edge tip escape.** The odd root `v + (1,0)` (with `v` even) escapes at depth two through `v + (1,1)` and `v + (0,1)`. -/
theorem tip_W0_escape {field grade : Field} {permits : Site → Site → Prop} {level : ℤ} {v : Site} (hv : EvenSite v)
    (hr : laplacian field (v + (1, 0)) = 0) (hu : laplacian field (v + (1, 1)) = 0)
    (hru : permits (v + (1, 0)) (v + (1, 1))) (hpu : permits (v + (1, 1)) (v + (0, 1)))
    (hy : grade (v + (0, 1)) < level) : RestrictedEscapesWithin field grade permits level 2 (v + (1, 0)) := by
  have hodd : ¬ EvenSite (v + (1, 0)) := by
    unfold EvenSite at hv ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have heven : EvenSite (v + (1, 1)) := by
    unfold EvenSite at hv ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  refine two_edge_escape hr (Or.inr ?_) hru hu (Or.inl ?_) hpu hy
  · unfold incomingPos
    rw [if_neg hodd]
    ext <;> (simp; try omega)
  · unfold incomingNeg
    rw [if_pos heven]
    ext <;> (simp; try omega)

/-- **W1 two-edge tip escape.** The even root `v` escapes at depth two through `v + (−1,0)` and `v + (−1,1)`. -/
theorem tip_W1_escape {field grade : Field} {permits : Site → Site → Prop} {level : ℤ} {v : Site} (hv : EvenSite v)
    (hr : laplacian field v = 0) (hu : laplacian field (v + (-1, 0)) = 0)
    (hru : permits v (v + (-1, 0))) (hpu : permits (v + (-1, 0)) (v + (-1, 1)))
    (hy : grade (v + (-1, 1)) < level) : RestrictedEscapesWithin field grade permits level 2 v := by
  have hodd : ¬ EvenSite (v + (-1, 0)) := by
    unfold EvenSite at hv ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  refine two_edge_escape hr (Or.inl ?_) hru hu (Or.inr ?_) hpu hy
  · unfold incomingNeg
    rw [if_pos hv]
    ext <;> (simp; try omega)
  · unfold incomingPos
    rw [if_neg hodd]
    ext <;> (simp; try omega)

end FLatticePaper
