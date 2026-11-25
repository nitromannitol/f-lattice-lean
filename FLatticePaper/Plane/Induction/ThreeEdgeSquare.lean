import FLatticePaper.Plane.Induction.W1NonfreeOut
import FLatticePaper.Plane.Induction.FanCompat
import FLatticePaper.Plane.Induction.CanonicalSigned

/-! # The three-edge return of an odd root is `ParentSquareOut` (Q32, structural form)

For an odd root `z` (white in `G`), the unit square `{z, z+S, z+SW, z+W}` carries the return `q0 = z+S → q1 = z+SW → q2 = z+W → z`: the
rejected input `q0` of `z` is not retained by `z`, and the root retains only its outside input `o = z+N`. Each corner is black (keeps both
inputs) or white with its unique retained input. This is exactly `ParentSquareOut`. The module proves that structure from the three arrows,
the root's prescription (`z` retains `z+N` only, `hz_unique`), and white uniqueness (`hwu`); the arrows are the named inputs. -/

namespace FLatticePaper.ThreeEdgeSquare

open FLatticePaper FLatticePaper.W1NonfreeOut FLatticePaper.FanCompat FLatticePaper.Induction

theorem parentSquareOut_of_three_edges {G : Field} {R : Site → Site → Prop} {z : Site}
    (hz_odd : ¬ EvenSite z)
    (hz_n : R z (z.1, z.2 + 1)) (hz_unique : ∀ j, R z j → j = (z.1, z.2 + 1))
    (hwu : ∀ c j j', laplacian G c = 0 → R c j → R c j' → j = j')
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    (he1 : R (z.1, z.2 - 1) (z.1 - 1, z.2 - 1))
    (he2 : R (z.1 - 1, z.2 - 1) (z.1 - 1, z.2))
    (he3 : R (z.1 - 1, z.2) z) :
    ParentSquareOut G R z := by
  have hodd : (z.1 + z.2) % 2 = 1 := by
    unfold EvenSite at hz_odd
    omega
  have hev0 : EvenSite (z.1, z.2 - 1) := by
    unfold EvenSite
    simp only
    omega
  have hodd1 : ¬ EvenSite (z.1 - 1, z.2 - 1) := by
    unfold EvenSite
    simp only
    omega
  have hev2 : EvenSite (z.1 - 1, z.2) := by
    unfold EvenSite
    simp only
    omega
  have E1 : Edge (z.1 - 1, z.2 - 1) (z.1, z.2 - 1) := by
    unfold Edge incomingNeg
    rw [if_pos hev0]
    exact Or.inl rfl
  have E2 : Edge (z.1 - 1, z.2) (z.1 - 1, z.2 - 1) := by
    unfold Edge incomingPos
    rw [if_neg hodd1]
    exact Or.inr (Prod.ext rfl (by simp))
  have E3 : Edge z (z.1 - 1, z.2) := by
    unfold Edge incomingPos
    rw [if_pos hev2]
    exact Or.inr (Prod.ext (by simp) rfl)
  have hneg : incomingNeg z = (z.1, z.2 - 1) := by
    unfold incomingNeg
    rw [if_neg hz_odd]
  have hpos : incomingPos z = (z.1, z.2 + 1) := by
    unfold incomingPos
    rw [if_neg hz_odd]
  refine ⟨(z.1, z.2 - 1), (z.1 - 1, z.2 - 1), (z.1 - 1, z.2), (z.1, z.2 + 1), z.1 - 1, z.2 - 1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_squareCorners_iff]
    omega
  · rw [mem_squareCorners_iff]
    omega
  · rw [mem_squareCorners_iff]
    omega
  · rw [mem_squareCorners_iff]
    omega
  · intro c' hc' hne
    rw [mem_squareCorners_iff] at hc'
    obtain ⟨x, y⟩ := c'
    have hne' : ¬ (x = z.1 ∧ y = z.2) := fun h => hne (Prod.ext h.1 h.2)
    dsimp only at hc' ⊢
    simp only [Prod.mk.injEq]
    omega
  · simp only [ne_eq, Prod.mk.injEq]
    omega
  · simp only [ne_eq, Prod.mk.injEq]
    omega
  · simp only [ne_eq, Prod.mk.injEq]
    omega
  · exact Or.inl hneg.symm
  · intro h
    have := hz_unique _ h
    simp only [Prod.mk.injEq] at this
    omega
  · exact E1
  · exact E2
  · exact E3
  · exact he1
  · exact he2
  · exact he3
  · exact Or.inr hpos.symm
  · intro h
    rw [mem_squareCorners_iff] at h
    dsimp only at h
    omega
  · exact hz_n
  · exact hz_unique
  · rcases hbin (z.1, z.2 - 1) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, fun j hj => hwu _ j _ h hj he1⟩
  · rcases hbin (z.1 - 1, z.2 - 1) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, fun j hj => hwu _ j _ h hj he2⟩
  · rcases hbin (z.1 - 1, z.2) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, fun j hj => hwu _ j _ h hj he3⟩

/-- The prescribed H direction at an odd site away from `hFirst` and `hLast` is `N`. -/
theorem prescribedH_odd {frame : ChildFrame} (η : ℤ) {x : Site} (ho : ¬ EvenSite x)
    (h1 : x ≠ hFirst) (h2 : x ≠ frame.hLast) : frame.prescribedH η x = (0, 1) := by
  unfold ChildFrame.prescribedH
  rw [if_neg h1, if_neg h2, if_neg ho]

/-- **The three-edge square at a free H root.** An odd root `z` in the free H trace, white in `G`, with the prescribed `N` (`PrescribedAt`)
and the three arrows `z+S → z+SW → z+W → z`, has `ParentSquareOut`. The white uniqueness `hwu` is the canonical policy's
`white_policy` (the white keeps its selected input). -/
theorem parentSquareOut_of_freeH_root {frame : ChildFrame} {G : Field} {R : Site → Site → Prop} {η : ℤ}
    (hpres : PrescribedAt frame G η R) {z : Site} (hzH : z ∈ frame.freeH) (hzw : laplacian G z = 0)
    (hz_odd : ¬ EvenSite z) (hz_first : z ≠ hFirst) (hz_last : z ≠ frame.hLast)
    (hwu : ∀ c j j', laplacian G c = 0 → R c j → R c j' → j = j')
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    (he1 : R (z.1, z.2 - 1) (z.1 - 1, z.2 - 1))
    (he2 : R (z.1 - 1, z.2 - 1) (z.1 - 1, z.2))
    (he3 : R (z.1 - 1, z.2) z) :
    ParentSquareOut G R z := by
  have hP := prescribedH_odd (frame := frame) η hz_odd hz_first hz_last
  have hzN : z + frame.prescribedH η z = (z.1, z.2 + 1) := by
    rw [hP]
    exact Prod.ext (by simp) (by simp)
  have hn : R z (z.1, z.2 + 1) := by
    have := (hpres.1 z hzH hzw (z + frame.prescribedH η z)).mpr rfl
    rw [hzN] at this
    exact this
  have hu : ∀ j, R z j → j = (z.1, z.2 + 1) := by
    intro j hj
    have := (hpres.1 z hzH hzw j).mp hj
    rw [hzN] at this
    exact this
  exact parentSquareOut_of_three_edges hz_odd hn hu hwu hbin he1 he2 he3

end FLatticePaper.ThreeEdgeSquare
