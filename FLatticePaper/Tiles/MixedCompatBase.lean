import FLatticePaper.Tiles.ClosedPathAssembly

/-! Mixed interfaces at the first non-base word. Both registers come from the empty word.
The two base formulas determine the difference on the whole intersection of the placed
domains, including the displaced copy in each doubling. -/

namespace FLatticePaper.Tiles.MixedCompatBase

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard FLatticePaper.Tiles.SurgicalWeak
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.ClosedPathAssembly
open FLatticePaper.Tiles.ClosedPathCycle FLatticePaper.Tiles.ClosedPathSum

private def row (a b s t : Site) (k : ℤ) : Prop :=
  ∀ x ∈ nstairN 3, x + a - b ∈ stairF 3 →
    paperNearStairValue 3 (x + (0, 1)) + dot2 s (x + a) -
      (paperStairValue 3 (x + a - b) + dot2 t (x + a)) = k

private instance (a b s t : Site) (k : ℤ) : Decidable (row a b s t k) := by
  unfold row
  infer_instance

private def oddHeight (i : ℕ) : ℤ := [0, -7, 0, 0, -2, -2].getD i 0
private def evenHeight (i : ℕ) : ℤ := [0, -2, -7, -18, 0, -11].getD i 0

private abbrev oneWord : Word := [.one]

private theorem odd_rows (i : Fin 2) (j : Fin 4) :
    row ((oddP oneWord).getD i 0) ((oddQ oneWord).getD j 0)
      (affOdd (parentsAt oneWord).odd (parentsAt oneWord).even i)
      (affOdd (parentsAt oneWord).odd (parentsAt oneWord).even (j + 2 : ℕ))
      (oddHeight i - oddHeight (j + 2 : ℕ)) := by
  fin_cases i <;> fin_cases j <;> decide

private theorem even_rows (i : Fin 4) (j : Fin 2) :
    row ((evenP oneWord).getD i 0) ((evenQ oneWord).getD j 0)
      (affEven (parentsAt oneWord).odd (parentsAt oneWord).even i)
      (affEven (parentsAt oneWord).odd (parentsAt oneWord).even (j + 4 : ℕ))
      (evenHeight i - evenHeight (j + 4 : ℕ)) := by
  fin_cases i <;> fin_cases j <;> decide

private theorem placed_row (P Q : PartialOdometer) (h : PaperBaseCond [] P Q)
    (a b s t z : Site) (k cp cq : ℤ) (hr : row a b s t k)
    (hp : z - a ∈ oddTile []) (hq : z - b ∈ evenTile []) :
    P.val (z - a) + dot2 s z + cp - (Q.val (z - b) + dot2 t z + cq) = k + cp - cq := by
  obtain ⟨hP, vP, hQ, vQ⟩ := h.1 rfl
  change z - a ∈ nstairN 3 at hp
  change z - b ∈ stairF 3 at hq
  have hrow := hr (z - a) hp (by simpa only [sub_add_cancel] using hq)
  rw [sub_add_cancel] at hrow
  rw [vP _ (hP ▸ hp), vQ _ (hQ ▸ hq)]
  omega

/-- Local compatibility of the mixed copies of the odd child of the word `[1]`,
for the paper's base parents and any constants on the six copies. -/
theorem mixedCompatOdd_one (P Q : PartialOdometer) (h : PaperBaseCond [] P Q) (c : ℕ → ℤ) :
    MixedCompatOdd [.one] [] [] (placedOdd [.one] P.val Q.val c) := by
  intro i j hi hj hj'
  refine ⟨oddHeight i - oddHeight j + c i - c j, fun z hpi hqj => ?_⟩
  have hp := mOdd_sub oneWord [] [] i hpi
  have hq := mOdd_sub oneWord [] [] j hqj
  simp only [dOdd, pieceSet, oddP_length, if_pos hi, if_neg (by omega : ¬ j < 2)] at hp hq
  have hr := odd_rows ⟨i, hi⟩ ⟨j - 2, by omega⟩
  simp only [Nat.sub_add_cancel hj] at hr
  simp only [placedOdd, if_pos hi, if_neg (by omega : ¬ j < 2)]
  exact placed_row P Q h _ _ _ _ z _ _ _ hr (sub_mem_of_shift _ _ _ hp) (sub_mem_of_shift _ _ _ hq)

/-- Local compatibility of the mixed copies of the even child of the word `[1]`,
including the two vertical translates of the odd register. -/
theorem mixedCompatEven_one (P Q : PartialOdometer) (h : PaperBaseCond [] P Q) (c : ℕ → ℤ) :
    MixedCompatEven [.one] [] [] (placedEven [.one] P.val Q.val c) := by
  intro i j hi hj hj'
  refine ⟨evenHeight i - evenHeight j + c i - c j, fun z hpi hqj => ?_⟩
  have hp := mEven_sub oneWord [] [] i hpi
  have hq := mEven_sub oneWord [] [] j hqj
  simp only [dEven, pieceSet, evenP_length, if_pos hi, if_neg (by omega : ¬ j < 4)] at hp hq
  have hr := even_rows ⟨i, hi⟩ ⟨j - 4, by omega⟩
  simp only [Nat.sub_add_cancel hj] at hr
  simp only [placedEven, if_pos hi, if_neg (by omega : ¬ j < 4)]
  exact placed_row P Q h _ _ _ _ z _ _ _ hr (sub_mem_of_shift _ _ _ hp) (sub_mem_of_shift _ _ _ hq)

end FLatticePaper.Tiles.MixedCompatBase
