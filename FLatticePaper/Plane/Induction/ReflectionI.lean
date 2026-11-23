import FLatticePaper.Plane.Induction.OldPolicy
import FLatticePaper.Plane.Induction.SquareClauses

/-! Task 72 (b): the reflection about `I = (1, −1)` of the clause system.

For `F` with `F (I − z) = F z`:
* the incoming neighbours are exchanged: `incomingNeg (I − x) = I − incomingPos x`, `incomingPos (I − x) = I − incomingNeg x`, so an
  edge `i → c` maps to an edge `I − i → I − c` (`edge_reflectI`);
* the Laplacian is `I`-invariant (`laplacian_reflectI`);
* the unit square with corners `squareCorners a b` maps to `squareCorners (−a) (−2 − b)` (`mem_corners_reflectI`);
* unseeded forced edges are carried to forced edges (`forced_reflectI`), by induction on `ForcedEdge`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper FLatticePaper.SquareClauses FLatticePaper.AndOrRank

theorem evenSite_reflectI (x : Site) : EvenSite (reflectionI - x) ↔ EvenSite x := by
  unfold EvenSite reflectionI
  simp only [Prod.fst_sub, Prod.snd_sub]
  omega

theorem incomingNeg_reflectI (x : Site) :
    incomingNeg (reflectionI - x) = reflectionI - incomingPos x := by
  unfold incomingNeg incomingPos
  by_cases h : EvenSite x
  · have h' : EvenSite (reflectionI - x) := (evenSite_reflectI x).mpr h
    rw [if_pos h, if_pos h']
    unfold reflectionI
    ext <;> simp <;> ring
  · have h' : ¬ EvenSite (reflectionI - x) := fun hh => h ((evenSite_reflectI x).mp hh)
    rw [if_neg h, if_neg h']
    unfold reflectionI
    ext <;> simp <;> ring

theorem incomingPos_reflectI (x : Site) :
    incomingPos (reflectionI - x) = reflectionI - incomingNeg x := by
  unfold incomingNeg incomingPos
  by_cases h : EvenSite x
  · have h' : EvenSite (reflectionI - x) := (evenSite_reflectI x).mpr h
    rw [if_pos h, if_pos h']
    unfold reflectionI
    ext <;> simp <;> ring
  · have h' : ¬ EvenSite (reflectionI - x) := fun hh => h ((evenSite_reflectI x).mp hh)
    rw [if_neg h, if_neg h']
    unfold reflectionI
    ext <;> simp <;> ring

/-- An edge `i → c` is carried to the edge `I − i → I − c`. -/
theorem edge_reflectI {i c : Site} (h : Edge i c) : Edge (reflectionI - i) (reflectionI - c) := by
  unfold Edge at h ⊢
  rcases h with h | h
  · right
    rw [h, incomingPos_reflectI]
  · left
    rw [h, incomingNeg_reflectI]

/-- The Laplacian is `I`-invariant when `F (I − z) = F z`. -/
theorem laplacian_reflectI {F : Field} (hF : ∀ z, F (reflectionI - z) = F z) (c : Site) :
    laplacian F (reflectionI - c) = laplacian F c := by
  unfold laplacian
  simp only [incomingNeg_reflectI, incomingPos_reflectI, hF]
  ring

/-- The unit square `squareCorners a b` is carried to `squareCorners (−a) (−2 − b)` by `I`. -/
theorem mem_corners_reflectI (a b : ℤ) (x : Site) :
    x ∈ squareCorners a b ↔ reflectionI - x ∈ squareCorners (-a) (-2 - b) := by
  obtain ⟨x1, x2⟩ := x
  unfold reflectionI
  show (x1, x2) ∈ squareCorners a b ↔ (1 - x1, -1 - x2) ∈ squareCorners (-a) (-2 - b)
  simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor <;> intro h <;> omega

/-- Unseeded forced edges are carried to unseeded forced edges by `I`, when `F` is `I`-symmetric. -/
theorem forced_reflectI {F : Field} (hF : ∀ z, F (reflectionI - z) = F z) {c i : Site}
    (h : ForcedEdge F (fun _ _ => False) c i) :
    ForcedEdge F (fun _ _ => False) (reflectionI - c) (reflectionI - i) := by
  induction h with
  | seed hs => exact False.elim hs
  | @unit a b c' o inside hc hw ho hout hin hforced ih =>
    refine ForcedEdge.unit (a := -a) (b := -2 - b) (fun z => reflectionI - inside (reflectionI - z)) ?_ ?_ ?_ ?_ ?_ ?_
    · exact (mem_corners_reflectI a b c').mp hc
    · rw [laplacian_reflectI hF]
      exact hw
    · rcases ho with rfl | rfl
      · exact Or.inr (by rw [incomingPos_reflectI])
      · exact Or.inl (by rw [incomingNeg_reflectI])
    · intro hmem
      exact hout ((mem_corners_reflectI a b o).mpr hmem)
    · intro c'' hc'' hne
      have hx : reflectionI - c'' ∈ squareCorners a b :=
        (mem_corners_reflectI a b (reflectionI - c'')).mpr (by rwa [sub_sub_cancel])
      have hne' : reflectionI - c'' ≠ c' := fun e => hne (by rw [← e, sub_sub_cancel])
      have hlap := laplacian_reflectI hF (reflectionI - c'')
      rw [sub_sub_cancel] at hlap
      rcases hin (reflectionI - c'') hx hne' with hb | ⟨hw', hy, hyin⟩
      · left
        rw [hlap]
        exact hb
      · right
        refine ⟨by rw [hlap]; exact hw', ?_, ?_⟩
        · exact (mem_corners_reflectI a b _).mp hy
        · rcases hyin with e | e
          · right
            show reflectionI - inside (reflectionI - c'') = incomingPos c''
            rw [e, ← sub_sub_cancel reflectionI c'', incomingPos_reflectI, sub_sub_cancel]
          · left
            show reflectionI - inside (reflectionI - c'') = incomingNeg c''
            rw [e, ← sub_sub_cancel reflectionI c'', incomingNeg_reflectI, sub_sub_cancel]
    · intro c'' hc'' hne hw''
      have hx : reflectionI - c'' ∈ squareCorners a b :=
        (mem_corners_reflectI a b (reflectionI - c'')).mpr (by rwa [sub_sub_cancel])
      have hne' : reflectionI - c'' ≠ c' := fun e => hne (by rw [← e, sub_sub_cancel])
      have hwx : laplacian F (reflectionI - c'') = 0 := by
        rw [laplacian_reflectI hF]
        exact hw''
      have h' := ih (reflectionI - c'') hx hne' hwx
      rw [sub_sub_cancel] at h'
      exact h'

end FLatticePaper.Induction
