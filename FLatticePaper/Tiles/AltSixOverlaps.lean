import FLatticePaper.Tiles.AltPiecesAgree
import FLatticePaper.Tiles.AltItem5

/-! # The overlaps of the six standard copies of an alternate child

`AltPiecesAgree.SixOverlaps` for both alternate children at every non-base word, from the two facts on the copies: two copies of
the same register that are not a doubled pair never meet (the hypothesis `hsame`, in the form of the same-register disjointness of
the alternate copies), and two copies of different registers meet only inside the marks of both (`AltItem5.item5_marks_even`,
`item5_marks_odd`). -/

namespace FLatticePaper.Tiles.AltSixOverlaps

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.ClosedPathAlt FLatticePaper.Tiles.ChildGlue
open FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.SurgicalWeak (regsAt)
open FLatticePaper.Tiles.Standard (IsBase oddTile evenTile)

theorem getD_mem (l : List (ℤ × ℤ)) (i : ℕ) (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

/-- `SixOverlaps` for the even alternate child. -/
theorem sixOverlaps_even (w u1 u2 : Word) (hw : ¬ IsBase w) (hr : regsAt w = (some u1, some u2))
    (hsame : ∀ i j, i < 6 → j < 6 → i ≠ j → (i < 4 ↔ j < 4) →
      ¬(i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0 ∨ i = 2 ∧ j = 3 ∨ i = 3 ∧ j = 2) →
      ∀ z, z ∈ dAE w u1 u2 i → z ∈ dAE w u1 u2 j → False) :
    AltPiecesAgree.SixOverlaps (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) dblEven := by
  obtain ⟨h1, -, h2, -⟩ := WeakStepPaper.regsAt_tiles w
  have hT1 := h1 u1 (by rw [hr])
  have hT2 := h2 u2 (by rw [hr])
  have hm := AltItem5.item5_marks_even hw u1 u2 hT1 hT2
  have hlen : (altEvenD w).length = 4 := by simp [altEvenD]
  have hlenR : (altEvenR w).length = 2 := by simp [altEvenR]
  intro i j hi hj hij z hzi hzj
  by_cases hf : pieceFlag (altEvenD w) i = pieceFlag (altEvenD w) j
  · left
    refine ⟨hf, ?_⟩
    simp only [pieceFlag, hlen, decide_eq_decide] at hf
    by_contra hd
    exact hsame i j hi hj (by omega) (by omega) (by simp only [dblEven] at hd; omega) z hzi hzj
  · right
    refine ⟨hf, ?_⟩
    simp only [pieceFlag, hlen, decide_eq_decide] at hf
    have hi4 : i < 4 := by omega
    have hj4 : 4 ≤ j := by omega
    simp only [pieceSet, hlen, if_pos hi4, if_neg (show ¬ j < 4 by omega)] at hzi hzj ⊢
    have mR : (altEvenR w).getD (j - 4) 0 ∈ altEvenR w := getD_mem _ _ (by omega)
    have mD : (altEvenD w).getD i 0 ∈ altEvenD w := getD_mem _ _ (by omega)
    have key := hm ((altEvenR w).getD (j - 4) 0) mR ((altEvenD w).getD i 0) mD z (by rw [← coe_shift, hT1] at *; exact hzj) (by rw [← coe_shift, hT2] at *; exact hzi)
    exact ⟨key.2, key.1⟩

/-- `SixOverlaps` for the odd alternate child. -/
theorem sixOverlaps_odd (w u1 u2 : Word) (hw : ¬ IsBase w) (hr : regsAt w = (some u1, some u2))
    (hsame : ∀ i j, i < 6 → j < 6 → i ≠ j → (i < 4 ↔ j < 4) →
      ¬(i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0 ∨ i = 2 ∧ j = 3 ∨ i = 3 ∧ j = 2) →
      ∀ z, z ∈ dAO w u1 u2 i → z ∈ dAO w u1 u2 j → False) :
    AltPiecesAgree.SixOverlaps (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) dblEven := by
  obtain ⟨h1, -, h2, -⟩ := WeakStepPaper.regsAt_tiles w
  have hT1 := h1 u1 (by rw [hr])
  have hT2 := h2 u2 (by rw [hr])
  have hm := AltItem5.item5_marks_odd hw u1 u2 hT1 hT2
  have hlen : (altOddD w).length = 4 := by simp [altOddD]
  have hlenR : (altOddR w).length = 2 := by simp [altOddR]
  intro i j hi hj hij z hzi hzj
  by_cases hf : pieceFlag (altOddD w) i = pieceFlag (altOddD w) j
  · left
    refine ⟨hf, ?_⟩
    simp only [pieceFlag, hlen, decide_eq_decide] at hf
    by_contra hd
    exact hsame i j hi hj (by omega) (by omega) (by simp only [dblEven] at hd; omega) z hzi hzj
  · right
    refine ⟨hf, ?_⟩
    simp only [pieceFlag, hlen, decide_eq_decide] at hf
    have hi4 : i < 4 := by omega
    have hj4 : 4 ≤ j := by omega
    simp only [pieceSet, hlen, if_pos hi4, if_neg (show ¬ j < 4 by omega)] at hzi hzj ⊢
    have mR : (altOddR w).getD (j - 4) 0 ∈ altOddR w := getD_mem _ _ (by omega)
    have mD : (altOddD w).getD i 0 ∈ altOddD w := getD_mem _ _ (by omega)
    have key := hm ((altOddD w).getD i 0) mD ((altOddR w).getD (j - 4) 0) mR z (by rw [← coe_shift, hT1] at *; exact hzi) (by rw [← coe_shift, hT2] at *; exact hzj)
    exact ⟨key.1, key.2⟩

end FLatticePaper.Tiles.AltSixOverlaps
