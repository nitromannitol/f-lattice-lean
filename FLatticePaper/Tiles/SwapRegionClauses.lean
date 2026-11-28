import FLatticePaper.Tiles.SwapNonvac
import FLatticePaper.Tiles.SwapRegions

/-! # The region clauses of `SwapBaseInput`, as pair compatibilities

The region identities of `SwapRegions` give the compatibility of the pair when the overlap grows with the word; the block template
`pairCompat_of_block` takes them as its difference hypothesis. -/

namespace FLatticePaper.Tiles.SwapRegionClauses

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SurgicalWeak FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.WeakStepPaper FLatticePaper.Tiles.JointFamily FLatticePaper.Tiles.TileCompatInputs
open FLatticePaper.Tiles.Standard FLatticePaper.Construction
open FLatticePaper.Tiles.SwapNonvac

/-- Clause N6: the even pair (1,2) of the word `3^k 1` (`k ≥ 1`) on the odd tile of `3^k` (the ladder region). -/
theorem clause_N6 (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (w : Word) (k : ℕ) (hk : 1 ≤ k)
    (hw : w = List.replicate k Digit.three ++ [Digit.one])
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f w.length) :
    PairCompat (FLatticePaper.Tiles.GlueFull.evenFull f w) 1 2 := by
  subst hw
  have hreg := regsAt_three_one k
  have hnb := not_isBase_three_one k
  have hc : ¬ CorrectedAfterTwo (List.replicate k Digit.three ++ [Digit.one]) := by
    rintro ⟨-, h⟩
    simp at h
  have hl1 : (List.replicate k Digit.three).length < (List.replicate k Digit.three ++ [Digit.one]).length := by simp
  have hI3 : IsBase (List.replicate k Digit.three) :=
    Or.inr (Or.inl fun d hd => List.eq_of_mem_replicate hd)
  have hb := FLatticePaper.Tiles.SwapBaseTiles.base_tiles_paper D hS f _ hG _ hl1 hI3
  obtain ⟨hOd, hOv, -, -⟩ := hb.2.1 k hk rfl
  have hp1 : (parentsAt (List.replicate k Digit.three ++ [Digit.one])).odd = ⟨1, 2 * (k : ℤ) + 2⟩ := by
    rw [(FLatticePaper.Tiles.WeakStepAssembly.regsAt_parents _).1 _ (by rw [hreg])]
    exact FLatticePaper.Tiles.BaseTileProps.cur_odd_three k
  have hq1 : (parentsAt (List.replicate k Digit.three ++ [Digit.one])).even = ⟨1, 2 * (k : ℤ) + 3⟩ := by
    rw [(FLatticePaper.Tiles.WeakStepAssembly.regsAt_parents _).2 _ (by rw [hreg])]
    exact FLatticePaper.Tiles.BaseTileProps.cur_even_three k
  have hf := phase_three_one k
  have h1 := FLatticePaper.Tiles.GlueFull.evenFull_get f (List.replicate k Digit.three ++ [Digit.one])
    (List.replicate k Digit.three) (List.replicate k Digit.three) hnb hreg hc hl1 hl1 1 (by norm_num)
  have h2 := FLatticePaper.Tiles.GlueFull.evenFull_get f (List.replicate k Digit.three ++ [Digit.one])
    (List.replicate k Digit.three) (List.replicate k Digit.three) hnb hreg hc hl1 hl1 2 (by norm_num)
  have e1 : FLatticePaper.Tiles.GlueFull.offE (List.replicate k Digit.three ++ [Digit.one]) 1 =
      (-2 * (k : ℤ) - 1, 2 * (k : ℤ) + 3) := by
    rw [FLatticePaper.Tiles.SwapOffsets.offE_1, if_pos hf, hp1]
    show ((1 - (2 * (k : ℤ) + 2), 1 + (2 * (k : ℤ) + 2)) : ℤ × ℤ) = _
    rw [Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  have e2 : FLatticePaper.Tiles.GlueFull.offE (List.replicate k Digit.three ++ [Digit.one]) 2 = (1, 2 * (k : ℤ) + 5) := by
    rw [FLatticePaper.Tiles.SwapOffsets.offE_2, if_pos hf, hq1]
    show ((2 * (k : ℤ) + 3, 1) + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) : ℤ × ℤ) = _
    rw [Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  have a1 : FLatticePaper.Tiles.ClosedPathAssembly.affEven (parentsAt (List.replicate k Digit.three ++ [Digit.one])).odd
      (parentsAt (List.replicate k Digit.three ++ [Digit.one])).even 1 = (1, -(2 * (k : ℤ) + 2)) := by
    rw [hp1]
    rfl
  have a2 : FLatticePaper.Tiles.ClosedPathAssembly.affEven (parentsAt (List.replicate k Digit.three ++ [Digit.one])).odd
      (parentsAt (List.replicate k Digit.three ++ [Digit.one])).even 2 = (1, -(2 * (k : ℤ) + 3)) := by
    rw [hq1]
    rfl
  have hp : (FLatticePaper.Tiles.GlueFull.evenFull f (List.replicate k Digit.three ++ [Digit.one]))[1]? =
      some (stdPiece (f (List.replicate k Digit.three)).tOdd (-2 * (k : ℤ) - 1, 2 * (k : ℤ) + 3) (1, -(2 * (k : ℤ) + 2))) := by
    rw [h1, e1, a1]
    simp
  have hq : (FLatticePaper.Tiles.GlueFull.evenFull f (List.replicate k Digit.three ++ [Digit.one]))[2]? =
      some (stdPiece (f (List.replicate k Digit.three)).tOdd (1, 2 * (k : ℤ) + 5) (1, -(2 * (k : ℤ) + 3))) := by
    rw [h2, e2, a2]
    simp
  have hdom : ∀ z, z ∈ (f (List.replicate k Digit.three)).tOdd.dom ↔ z ∈ paperLadderTile (2 * (k : ℤ) + 2) := by
    intro z
    rw [hOd]
    exact FLatticePaper.Tiles.Standard.mem_ladderF_iff_paper (by omega) z
  exact FLatticePaper.Tiles.SwapBaseBlock.pairCompat_of_block _ 1 2 _ _ _ _ _ _ _ (2 * (k : ℤ) + 5)
    hdom hOv hp hq (fun x h0 h1 => FLatticePaper.Tiles.SwapRegions.ladder_region (k : ℤ) (by omega) x h0 h1)

/-- Clause N5: the odd pair (2,5) of the word `2^k 1` (`k ≥ 1`) on the even tile of `2^k` (the near-ladder region). -/
theorem clause_N5 (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (w : Word) (k : ℕ) (hk : 1 ≤ k)
    (hw : w = List.replicate k Digit.two ++ [Digit.one])
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f w.length) :
    PairCompat (FLatticePaper.Tiles.GlueFull.oddFull f w) 2 5 := by
  subst hw
  have hreg := regsAt_two_one k
  have hnb := not_isBase_two_one k
  have hc : ¬ CorrectedAfterThree (List.replicate k Digit.two ++ [Digit.one]) := by
    rintro ⟨-, h⟩
    simp at h
  have hl1 : (List.replicate k Digit.two).length < (List.replicate k Digit.two ++ [Digit.one]).length := by simp
  have hI2 : IsBase (List.replicate k Digit.two) :=
    Or.inr (Or.inr fun d hd => List.eq_of_mem_replicate hd)
  have hb := FLatticePaper.Tiles.SwapBaseTiles.base_tiles_paper D hS f _ hG _ hl1 hI2
  obtain ⟨-, -, hEd, hEv⟩ := hb.2.2 k hk rfl
  have hp1 : (parentsAt (List.replicate k Digit.two ++ [Digit.one])).odd = ⟨(k : ℤ) + 1, (k : ℤ) + 2⟩ := by
    rw [(FLatticePaper.Tiles.WeakStepAssembly.regsAt_parents _).1 _ (by rw [hreg])]
    exact FLatticePaper.Tiles.BaseTileProps.cur_odd_two k
  have hq1 : (parentsAt (List.replicate k Digit.two ++ [Digit.one])).even = ⟨2 * (k : ℤ) + 1, 2 * (k : ℤ) + 3⟩ := by
    rw [(FLatticePaper.Tiles.WeakStepAssembly.regsAt_parents _).2 _ (by rw [hreg])]
    exact FLatticePaper.Tiles.BaseTileProps.cur_even_two k
  have hf := phase_two_one k
  have h2 := FLatticePaper.Tiles.GlueFull.oddFull_get f (List.replicate k Digit.two ++ [Digit.one])
    (List.replicate k Digit.two) (List.replicate k Digit.two) hnb hreg hc hl1 hl1 2 (by norm_num)
  have h5 := FLatticePaper.Tiles.GlueFull.oddFull_get f (List.replicate k Digit.two ++ [Digit.one])
    (List.replicate k Digit.two) (List.replicate k Digit.two) hnb hreg hc hl1 hl1 5 (by norm_num)
  have e2 : FLatticePaper.Tiles.GlueFull.offO (List.replicate k Digit.two ++ [Digit.one]) 2 =
      (2 * (k : ℤ) + 4, 2 * (k : ℤ) + 2) := by
    rw [FLatticePaper.Tiles.SwapOffsets.offO_2, if_pos hf, hp1]
    show ((2 * ((k : ℤ) + 2), 2 * ((k : ℤ) + 1)) : ℤ × ℤ) = _
    rw [Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  have e5 : FLatticePaper.Tiles.GlueFull.offO (List.replicate k Digit.two ++ [Digit.one]) 5 =
      (2 * (k : ℤ) + 2, 4 * (k : ℤ) + 4) := by
    rw [FLatticePaper.Tiles.SwapOffsets.offO_5, if_pos hf, hp1, hq1]
    show ((((k : ℤ) + 1) - ((k : ℤ) + 2), ((k : ℤ) + 1) + ((k : ℤ) + 2)) + (2 * (k : ℤ) + 3, 2 * (k : ℤ) + 1) :
      ℤ × ℤ) = _
    rw [Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  have a2 : FLatticePaper.Tiles.ClosedPathAssembly.affOdd (parentsAt (List.replicate k Digit.two ++ [Digit.one])).odd
      (parentsAt (List.replicate k Digit.two ++ [Digit.one])).even 2 = (0, 0) := by
    simp [FLatticePaper.Tiles.ClosedPathAssembly.affOdd]
    rfl
  have a5 : FLatticePaper.Tiles.ClosedPathAssembly.affOdd (parentsAt (List.replicate k Digit.two ++ [Digit.one])).odd
      (parentsAt (List.replicate k Digit.two ++ [Digit.one])).even 5 = ((k : ℤ) + 1, -((k : ℤ) + 2)) := by
    rw [hp1]
    rfl
  have hp : (FLatticePaper.Tiles.GlueFull.oddFull f (List.replicate k Digit.two ++ [Digit.one]))[2]? =
      some (stdPiece (f (List.replicate k Digit.two)).tEven (2 * (k : ℤ) + 4, 2 * (k : ℤ) + 2) (0, 0)) := by
    rw [h2, e2, a2]
    simp
  have hq : (FLatticePaper.Tiles.GlueFull.oddFull f (List.replicate k Digit.two ++ [Digit.one]))[5]? =
      some (stdPiece (f (List.replicate k Digit.two)).tEven (2 * (k : ℤ) + 2, 4 * (k : ℤ) + 4)
        ((k : ℤ) + 1, -((k : ℤ) + 2))) := by
    rw [h5, e5, a5]
    simp
  have hval : ∀ z ∈ (f (List.replicate k Digit.two)).tEven.dom,
      (f (List.replicate k Digit.two)).tEven.val z = paperNearLadderValue (2 * (k : ℤ) + 2) (z.1, z.2 + 1) :=
    fun z hz => by
      rw [hEv z hz, site_add_zero_one z]
  have hdom : ∀ z, z ∈ (f (List.replicate k Digit.two)).tEven.dom ↔
      z ∈ {z : Site | (z.1, z.2 + 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 2)} := by
    intro z
    rw [hEd]
    exact FLatticePaper.Tiles.Standard.mem_nladderN_iff_paper (by omega) z
  exact FLatticePaper.Tiles.SwapBaseBlock.pairCompat_of_block _ 2 5 _ _ _ _ _ _ _ (((k : ℤ) + 1) * ((k : ℤ) + 2)) hdom hval hp hq
    (fun x h0 h1 => FLatticePaper.Tiles.SwapRegions.nladder_region (k : ℤ) (by omega) x.1 x.2 h0 h1)

end FLatticePaper.Tiles.SwapRegionClauses
