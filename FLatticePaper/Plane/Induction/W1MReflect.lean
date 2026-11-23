import FLatticePaper.Plane.Induction.W1MDescent

/-! # Task 85 (reflection): the centre reflection `z ↦ K₀ − z` with an even centre

For an even centre `K₀` the reflection `R z = K₀ − z` preserves parity, swaps the two inputs of a site (`R (incomingNeg x) = incomingPos (R x)`),
maps unit squares to unit squares, and therefore carries the unseeded forced edges of a field `F` to forced edges, when the laplacian of `F`
is `R`-invariant (`forcedEdge_reflect`). -/

namespace FLatticePaper.W1MReflect

open FLatticePaper FLatticePaper.SquareClauses FLatticePaper.AndOrRank

/-- The reflection swaps the inputs of a site (for an even centre). -/
theorem neighbours_reflect (K0 x : Site) (hK0 : (K0.1 + K0.2) % 2 = 0) :
    K0 - incomingNeg x = incomingPos (K0 - x) ∧ K0 - incomingPos x = incomingNeg (K0 - x) := by
  obtain ⟨k1, k2⟩ := K0
  obtain ⟨x1, x2⟩ := x
  unfold incomingNeg incomingPos EvenSite
  simp only at hK0
  constructor
  · split_ifs <;> simp only [Prod.mk.injEq, Prod.mk_sub_mk, and_true, true_and] at * <;> (repeat' apply And.intro) <;> omega
  · split_ifs <;> simp only [Prod.mk.injEq, Prod.mk_sub_mk, and_true, true_and] at * <;> (repeat' apply And.intro) <;> omega

/-- The reflection of a unit square is a unit square. -/
theorem square_reflect (K0 : Site) (a b : ℤ) (x : Site) :
    x ∈ squareCorners (K0.1 - a - 1) (K0.2 - b - 1) ↔ K0 - x ∈ squareCorners a b := by
  obtain ⟨k1, k2⟩ := K0
  obtain ⟨x1, x2⟩ := x
  simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_sub_mk]
  constructor <;> intro h <;> omega

/-- **Reflection covariance of the unseeded forced edges** (task 85): for an `R`-invariant laplacian, `R` carries forced edges to forced
edges. -/
theorem forcedEdge_reflect (F : Field) (K0 : Site) (hK0 : (K0.1 + K0.2) % 2 = 0)
    (hlap : ∀ x, laplacian F (K0 - x) = laplacian F x) {c o : Site}
    (h : ForcedEdge F (fun _ _ => False) c o) : ForcedEdge F (fun _ _ => False) (K0 - c) (K0 - o) := by
  induction h with
  | seed hs => exact False.elim hs
  | @unit a b c o inside hc hw ho hout hin hforced ih =>
    have hc' : K0 - c ∈ squareCorners (K0.1 - a - 1) (K0.2 - b - 1) := by
      rw [square_reflect, sub_sub_cancel]
      exact hc
    have hl : ∀ x, laplacian F x = laplacian F (K0 - x) := by
      intro x
      have := hlap (K0 - x)
      rw [sub_sub_cancel] at this
      exact this
    refine ForcedEdge.unit (fun c' => K0 - inside (K0 - c')) hc' ?_ ?_ ?_ ?_ ?_
    · rw [hlap]
      exact hw
    · rcases ho with ho | ho
      · rw [ho]
        exact Or.inr (neighbours_reflect K0 c hK0).1
      · rw [ho]
        exact Or.inl (neighbours_reflect K0 c hK0).2
    · intro hmem
      rw [square_reflect, sub_sub_cancel] at hmem
      exact hout hmem
    · intro c' hc'' hne
      have hcq : K0 - c' ∈ squareCorners a b := (square_reflect K0 a b c').1 hc''
      have hne' : K0 - c' ≠ c := by
        intro e
        apply hne
        rw [← sub_sub_cancel K0 c', e]
      have hl' : laplacian F c' = laplacian F (K0 - c') := hl c'
      rcases hin (K0 - c') hcq hne' with hb | ⟨hw2, hin2, hin2'⟩
      · left
        rw [hl']
        exact hb
      · right
        refine ⟨by rw [hl']; exact hw2, ?_, ?_⟩
        · show K0 - inside (K0 - c') ∈ squareCorners (K0.1 - a - 1) (K0.2 - b - 1)
          rw [square_reflect, sub_sub_cancel]
          exact hin2
        · show K0 - inside (K0 - c') = incomingNeg c' ∨ K0 - inside (K0 - c') = incomingPos c'
          rcases hin2' with h2 | h2
          · rw [h2, (neighbours_reflect K0 (K0 - c') hK0).1, sub_sub_cancel]
            exact Or.inr rfl
          · rw [h2, (neighbours_reflect K0 (K0 - c') hK0).2, sub_sub_cancel]
            exact Or.inl rfl
    · intro c' hc'' hne hw''
      have hcq : K0 - c' ∈ squareCorners a b := (square_reflect K0 a b c').1 hc''
      have hne' : K0 - c' ≠ c := by
        intro e
        apply hne
        rw [← sub_sub_cancel K0 c', e]
      have hw2 : laplacian F (K0 - c') = 0 := by
        rw [← hl c']
        exact hw''
      have hI := ih (K0 - c') hcq hne' hw2
      rw [sub_sub_cancel] at hI
      show ForcedEdge F (fun _ _ => False) c' (K0 - inside (K0 - c'))
      exact hI

end FLatticePaper.W1MReflect
