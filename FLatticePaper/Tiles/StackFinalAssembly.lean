import FLatticePaper.Tiles.StackFinalTruth
import FLatticePaper.Tiles.StackDecomp
import FLatticePaper.Tiles.StackedStringConnected

/-! The simple connectivity of the stacked strings of almost palindromes of length at least three, from the truth of
the final union and the decomposition. -/

namespace FLatticePaper.Tiles

/-- The final union, in the shape of the decomposition (anchor `posO (q + 1)`). -/
def finSetDef (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) : Finset Site :=
  lamO o ℓ (q + 1) ∪ pieceAt (ℓ (q + 1)) false (posO o ℓ (q + 1)) ∪
    pieceAt (ℓ 0) (decide (o = Orientation.horizontal) && decide (ℓ 1 = Letter.q) && decide (ℓ 0 = Letter.q))
      (posO o ℓ (q + 1) + (plusStepO o (ℓ 0) + ccO o (ℓ 0) - plusStepO o (ℓ (q + 1)) + familyShift o))

theorem mem_pieceAt_shift (l : Letter) (e : Bool) (A d x : Site) :
    x ∈ pieceAt l e (A + d) ↔ (x - A) - d ∈ tileSitesOf l e := by
  rw [piece_mem_iff, show x - (A + d) = x - A - d from by abel]

theorem finSetDef_mem_h (q : ℕ) (ℓ : ℕ → Letter) (hl0 : ℓ 0 = Letter.q) (hl : ℓ (q + 1) = Letter.p) (x : Site) :
    x ∈ finSetDef .horizontal ℓ q ↔
      x ∈ lamO .horizontal ℓ (q + 1) ∨ x - posO .horizontal ℓ (q + 1) ∈ finRel .horizontal (stateOf .horizontal ℓ (q + 1)).secondL := by
  have hc : plusStepO .horizontal (ℓ 0) + ccO .horizontal (ℓ 0) - plusStepO .horizontal (ℓ (q + 1)) +
      familyShift .horizontal = ((1 : ℤ), (-1 : ℤ)) := by
    rw [hl0, hl]
    decide
  unfold finSetDef
  rw [hc]
  simp only [Finset.mem_union, hl0, hl, decide_true, Bool.true_and, Bool.and_true, decide_eq_true_eq]
  rw [or_assoc]
  apply or_congr Iff.rfl
  show _ ↔ x - posO .horizontal ℓ (q + 1) ∈ tileSitesOf .p false ++
    (tileSitesOf .q (decide (ℓ 1 = Letter.q))).map (fun c => c + ((1 : ℤ), (-1 : ℤ)))
  rw [List.mem_append, List.mem_map]
  constructor
  · rintro (h | h)
    · exact Or.inl ((piece_mem_iff _ _ _ _).1 h)
    · rw [mem_pieceAt_shift] at h
      exact Or.inr ⟨_, h, by abel⟩
  · rintro (h | ⟨c, hc, hcx⟩)
    · exact Or.inl ((piece_mem_iff _ _ _ _).2 h)
    · right
      rw [mem_pieceAt_shift]
      have e : x - posO .horizontal ℓ (q + 1) - ((1 : ℤ), (-1 : ℤ)) = c := by
        rw [← hcx]
        abel
      rw [e]
      exact hc


theorem finSetDef_mem_v (q : ℕ) (ℓ : ℕ → Letter) (hl0 : ℓ 0 = Letter.p) (hl : ℓ (q + 1) = Letter.q) (x : Site) :
    x ∈ finSetDef .vertical ℓ q ↔
      x ∈ lamO .vertical ℓ (q + 1) ∨ x - posO .vertical ℓ (q + 1) ∈ finRel .vertical (stateOf .vertical ℓ (q + 1)).secondL := by
  have hc : plusStepO .vertical (ℓ 0) + ccO .vertical (ℓ 0) - plusStepO .vertical (ℓ (q + 1)) +
      familyShift .vertical = ((1 : ℤ), (0 : ℤ)) := by
    rw [hl0, hl]
    decide
  have hf : decide (Orientation.vertical = Orientation.horizontal) = false := by decide
  unfold finSetDef
  rw [hc, hf, Bool.false_and]
  simp only [Finset.mem_union, hl0, hl]
  rw [or_assoc]
  apply or_congr Iff.rfl
  show _ ↔ x - posO .vertical ℓ (q + 1) ∈ tileSitesOf .q false ++
    (tileSitesOf .p false).map (fun c => c + ((1 : ℤ), (0 : ℤ)))
  rw [List.mem_append, List.mem_map]
  constructor
  · rintro (h | h)
    · exact Or.inl ((piece_mem_iff _ _ _ _).1 h)
    · rw [mem_pieceAt_shift] at h
      exact Or.inr ⟨_, h, by abel⟩
  · rintro (h | ⟨c, hc, hcx⟩)
    · exact Or.inl ((piece_mem_iff _ _ _ _).2 h)
    · right
      rw [mem_pieceAt_shift]
      have e : x - posO .vertical ℓ (q + 1) - ((1 : ℤ), (0 : ℤ)) = c := by
        rw [← hcx]
        abel
      rw [e]
      exact hc

end FLatticePaper.Tiles
