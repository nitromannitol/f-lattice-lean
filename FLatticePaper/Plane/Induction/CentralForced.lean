import FLatticePaper.Plane.Induction.ReflectedFan

/-! # Forced edges are carried by a central reflection with an even centre

For an even site `A`, the map `cref A y = A − y` swaps the two inputs of every site and maps unit squares to unit squares. If the
laplacian is equivariant (`laplacian G (cref A y) = laplacian G y`), then `ForcedEdge G ∅ c i` gives `ForcedEdge G ∅ (cref A c) (cref A i)`.
This is the general form of `ReflectedFan.forcedEdge_reflH` (which is `cref` with the centre `U + I`). -/

namespace FLatticePaper.CentralForced

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.FanCompat

/-- The central reflection `y ↦ A − y`. -/
def cref (A y : Site) : Site := (A.1 - y.1, A.2 - y.2)

theorem cref_cref (A y : Site) : cref A (cref A y) = y := by
  unfold cref
  ext <;> simp

theorem evenSite_cref {A : Site} (hA : EvenSite A) (y : Site) : EvenSite (cref A y) ↔ EvenSite y := by
  unfold EvenSite at hA ⊢
  unfold cref
  dsimp only
  omega

theorem incomingNeg_cref {A : Site} (hA : EvenSite A) (z : Site) :
    incomingNeg (cref A z) = cref A (incomingPos z) := by
  unfold incomingNeg incomingPos
  by_cases hz : EvenSite z
  · rw [if_pos ((evenSite_cref hA z).mpr hz), if_pos hz]
    unfold cref
    refine Prod.ext ?_ ?_
    · try dsimp only
      try omega
    · try dsimp only
      try omega
  · rw [if_neg (fun h => hz ((evenSite_cref hA z).mp h)), if_neg hz]
    unfold cref
    refine Prod.ext ?_ ?_
    · try dsimp only
      try omega
    · try dsimp only
      try omega

theorem incomingPos_cref {A : Site} (hA : EvenSite A) (z : Site) :
    incomingPos (cref A z) = cref A (incomingNeg z) := by
  unfold incomingNeg incomingPos
  by_cases hz : EvenSite z
  · rw [if_pos ((evenSite_cref hA z).mpr hz), if_pos hz]
    unfold cref
    refine Prod.ext ?_ ?_
    · try dsimp only
      try omega
    · try dsimp only
      try omega
  · rw [if_neg (fun h => hz ((evenSite_cref hA z).mp h)), if_neg hz]
    unfold cref
    refine Prod.ext ?_ ?_
    · try dsimp only
      try omega
    · try dsimp only
      try omega

theorem mem_square_cref (A : Site) (a b : ℤ) (c : Site) :
    cref A c ∈ squareCorners (A.1 - a - 1) (A.2 - b - 1) ↔ c ∈ squareCorners a b := by
  rw [mem_squareCorners_iff, mem_squareCorners_iff]
  unfold cref
  dsimp only
  omega

/-- **Forced edges are carried by the central reflection.** -/
theorem forcedEdge_cref {G : Field} {A : Site} (hA : EvenSite A)
    (hlap : ∀ y, laplacian G (cref A y) = laplacian G y)
    {c i : Site} (h : ForcedEdge G (fun _ _ => False) c i) :
    ForcedEdge G (fun _ _ => False) (cref A c) (cref A i) := by
  induction h with
  | seed hs => exact (hs : False).elim
  | @unit a b c' o inside hc hw ho hout hin hforced ih =>
    refine ForcedEdge.unit (a := A.1 - a - 1) (b := A.2 - b - 1)
      (inside := fun x => cref A (inside (cref A x))) ((mem_square_cref A a b c').mpr hc) ?_ ?_ ?_ ?_ ?_
    · rw [hlap]
      exact hw
    · rcases ho with h1 | h1
      · right
        rw [h1, incomingPos_cref hA]
      · left
        rw [h1, incomingNeg_cref hA]
    · intro hmem
      exact hout ((mem_square_cref A a b o).mp hmem)
    · intro c'' hc'' hne
      obtain ⟨x, rfl⟩ : ∃ x, c'' = cref A x := ⟨cref A c'', (cref_cref A c'').symm⟩
      have hx : x ∈ squareCorners a b := (mem_square_cref A a b x).mp hc''
      have hxne : x ≠ c' := by
        intro h'
        apply hne
        rw [h']
      simp only [cref_cref]
      rcases hin x hx hxne with hb' | ⟨h0, hinSq, hinIn⟩
      · left
        rw [hlap]
        exact hb'
      · right
        refine ⟨by rw [hlap]; exact h0, (mem_square_cref A a b _).mpr hinSq, ?_⟩
        rcases hinIn with h2 | h2
        · right
          rw [h2, incomingPos_cref hA]
        · left
          rw [h2, incomingNeg_cref hA]
    · intro c'' hc'' hne hl
      obtain ⟨x, rfl⟩ : ∃ x, c'' = cref A x := ⟨cref A c'', (cref_cref A c'').symm⟩
      have hx : x ∈ squareCorners a b := (mem_square_cref A a b x).mp hc''
      have hxne : x ≠ c' := by
        intro h'
        apply hne
        rw [h']
      have hl' : laplacian G x = 0 := by
        rw [← hlap]
        simpa [cref_cref] using hl
      have hf := ih x hx hxne hl'
      simp only [cref_cref]
      exact hf

end FLatticePaper.CentralForced
