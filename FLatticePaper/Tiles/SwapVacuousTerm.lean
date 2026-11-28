import FLatticePaper.Tiles.SwapVacuousSpec
import FLatticePaper.Tiles.SwapVacuity
import FLatticePaper.Tiles.SwapNonvac
import FLatticePaper.Tiles.SwapBaseTiles
import FLatticePaper.Tiles.SwapBaseClauses

/-! # The fields V1, V3, V4, V5, V6 of `SwapVacuous`

Each field is a clause on the pieces `oddFull f w` and `evenFull f w`. The pieces of a register are read by `oddFull_get` and
`evenFull_get` (the helpers `vt_odd*`, `vt_even*` pick the odometer of the piece: the odd or the even base odometer of the
register). The odometers of a base register are `base_tiles_paper`. The disjointness is the vacuity lemma of `SwapVacuity`,
and `pairCompat_of_disjoint` closes the pair. The fields `V2` and `V7` are proved elsewhere and enter the structure there. -/

namespace FLatticePaper.Tiles.SwapVacuousTerm

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SurgicalWeak FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.WeakStepPaper FLatticePaper.Tiles.JointFamily FLatticePaper.Tiles.TileCompatInputs
open FLatticePaper.Tiles.Standard FLatticePaper.Construction
open FLatticePaper.Tiles.GlueFull FLatticePaper.Tiles.JointInduction FLatticePaper.Tiles.SwapVacuousSpec
open FLatticePaper.Tiles.SwapBaseClauses (pairCompat_of_disjoint)

/-! ### Non-base words and corrected words -/

theorem vt_nb_one (w : Word) (hw : Digit.one ∈ w) : ¬ FLatticePaper.Tiles.Standard.IsBase w := by
  rintro (h | h | h)
  · subst h; simp at hw
  · exact absurd (h Digit.one hw) (by decide)
  · exact absurd (h Digit.one hw) (by decide)

theorem vt_nb_mix (w : Word) (h2 : Digit.two ∈ w) (h3 : Digit.three ∈ w) :
    ¬ FLatticePaper.Tiles.Standard.IsBase w := by
  rintro (h | h | h)
  · subst h; simp at h2
  · exact absurd (h Digit.two h2) (by decide)
  · exact absurd (h Digit.three h3) (by decide)

/-! ### The registers of the words of the vacuous families -/

theorem vt_regs_three_one (k : ℕ) (hk : 1 ≤ k) :
    regsAt (List.replicate k Digit.three ++ [Digit.one]) =
      (some (List.replicate k Digit.three), some (List.replicate k Digit.three)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [WeakStepPaper.regsAt_snoc, FLatticePaper.Tiles.SwapNonvac.regsAt_three_succ n]
  simp [regStep]

theorem vt_regs_two_one (k : ℕ) (hk : 1 ≤ k) :
    regsAt (List.replicate k Digit.two ++ [Digit.one]) =
      (some (List.replicate k Digit.two), some (List.replicate k Digit.two)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [WeakStepPaper.regsAt_snoc, FLatticePaper.Tiles.SwapNonvac.regsAt_two_succ n]
  simp [regStep]

theorem vt_regs_two_three (m : ℕ) :
    regsAt (List.replicate (m + 1) Digit.two ++ [Digit.three]) =
      (some (List.replicate m Digit.two), some (List.replicate (m + 1) Digit.two)) := by
  rw [WeakStepPaper.regsAt_snoc, FLatticePaper.Tiles.SwapNonvac.regsAt_two_succ m]
  simp [regStep]

theorem vt_regs_one :
    regsAt [Digit.one] = (some [], some []) := by
  simp [regsAt, regRun, regStep]

/-! ### The pieces of the odd and even sides, by the odometer that each piece uses -/

theorem vt_oddTOdd (f : Word → JSlice) (w u1 u2 : Word) (hw : ¬ FLatticePaper.Tiles.Standard.IsBase w)
    (hreg : regsAt w = (some u1, some u2)) (hc : ¬ CorrectedAfterThree w) (hl1 : u1.length < w.length)
    (hl2 : u2.length < w.length) (k : ℕ) (hk : k < 2) :
    (oddFull f w)[k]? = some (stdPiece (f u1).tOdd (offO w k)
      (FLatticePaper.Tiles.ClosedPathAssembly.affOdd (parentsAt w).odd (parentsAt w).even k)) := by
  rw [oddFull_get f w u1 u2 hw hreg hc hl1 hl2 k (by omega), if_pos hk]

theorem vt_oddTEven (f : Word → JSlice) (w u1 u2 : Word) (hw : ¬ FLatticePaper.Tiles.Standard.IsBase w)
    (hreg : regsAt w = (some u1, some u2)) (hc : ¬ CorrectedAfterThree w) (hl1 : u1.length < w.length)
    (hl2 : u2.length < w.length) (k : ℕ) (hk2 : 2 ≤ k) (hk6 : k < 6) :
    (oddFull f w)[k]? = some (stdPiece (f u2).tEven (offO w k)
      (FLatticePaper.Tiles.ClosedPathAssembly.affOdd (parentsAt w).odd (parentsAt w).even k)) := by
  rw [oddFull_get f w u1 u2 hw hreg hc hl1 hl2 k hk6, if_neg (show ¬ k < 2 by omega)]

theorem vt_evenTOdd (f : Word → JSlice) (w u1 u2 : Word) (hw : ¬ FLatticePaper.Tiles.Standard.IsBase w)
    (hreg : regsAt w = (some u1, some u2)) (hc : ¬ CorrectedAfterTwo w) (hl1 : u1.length < w.length)
    (hl2 : u2.length < w.length) (k : ℕ) (hk : k < 4) :
    (evenFull f w)[k]? = some (stdPiece (f u1).tOdd (offE w k)
      (FLatticePaper.Tiles.ClosedPathAssembly.affEven (parentsAt w).odd (parentsAt w).even k)) := by
  rw [evenFull_get f w u1 u2 hw hreg hc hl1 hl2 k (by omega), if_pos hk]

theorem vt_evenTEven (f : Word → JSlice) (w u1 u2 : Word) (hw : ¬ FLatticePaper.Tiles.Standard.IsBase w)
    (hreg : regsAt w = (some u1, some u2)) (hc : ¬ CorrectedAfterTwo w) (hl1 : u1.length < w.length)
    (hl2 : u2.length < w.length) (k : ℕ) (hk4 : 4 ≤ k) (hk6 : k < 6) :
    (evenFull f w)[k]? = some (stdPiece (f u2).tEven (offE w k)
      (FLatticePaper.Tiles.ClosedPathAssembly.affEven (parentsAt w).odd (parentsAt w).even k)) := by
  rw [evenFull_get f w u1 u2 hw hreg hc hl1 hl2 k hk6, if_neg (show ¬ k < 4 by omega)]

/-! ### The fields -/

/-- Field `V5`: `w = [1]`. -/
theorem field_V5 : ∀ (D : JointData) (f : Word → JSlice) (w : Word), D.S = paperS → w = [Digit.one] →
    GoodBelow D f w.length →
      PairCompat (oddFull f w) 0 1 ∧ PairCompat (oddFull f w) 3 4 ∧
        PairCompat (evenFull f w) 0 3 ∧ PairCompat (evenFull f w) 4 5 := by
  intro D f w hS hw hG
  subst hw
  have hl : ([] : Word).length < [Digit.one].length := by simp
  have hb := FLatticePaper.Tiles.SwapBaseTiles.base_tiles_paper D hS f _ hG [] hl (Or.inl rfl)
  obtain ⟨c1, c2, c3, c4⟩ := FLatticePaper.Tiles.SwapVacuity.vac_V5 _ _ hb
  have hnb := vt_nb_one [Digit.one] (by simp)
  have hc1 : ¬ CorrectedAfterThree [Digit.one] := by rintro ⟨-, h⟩; simp at h
  have hc2 : ¬ CorrectedAfterTwo [Digit.one] := by rintro ⟨-, h⟩; simp at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact pairCompat_of_disjoint _ 0 1 _ _ _ _ _
      (vt_oddTOdd f [Digit.one] [] [] hnb vt_regs_one hc1 hl hl 0 (by norm_num))
      (vt_oddTOdd f [Digit.one] [] [] hnb vt_regs_one hc1 hl hl 1 (by norm_num)) c1
  · exact pairCompat_of_disjoint _ 3 4 _ _ _ _ _
      (vt_oddTEven f [Digit.one] [] [] hnb vt_regs_one hc1 hl hl 3 (by norm_num) (by norm_num))
      (vt_oddTEven f [Digit.one] [] [] hnb vt_regs_one hc1 hl hl 4 (by norm_num) (by norm_num)) c2
  · exact pairCompat_of_disjoint _ 0 3 _ _ _ _ _
      (vt_evenTOdd f [Digit.one] [] [] hnb vt_regs_one hc2 hl hl 0 (by norm_num))
      (vt_evenTOdd f [Digit.one] [] [] hnb vt_regs_one hc2 hl hl 3 (by norm_num)) c3
  · exact pairCompat_of_disjoint _ 4 5 _ _ _ _ _
      (vt_evenTEven f [Digit.one] [] [] hnb vt_regs_one hc2 hl hl 4 (by norm_num) (by norm_num))
      (vt_evenTEven f [Digit.one] [] [] hnb vt_regs_one hc2 hl hl 5 (by norm_num) (by norm_num)) c4

/-- Field `V3`: `w = 3^k 1`, `k ≥ 1`. -/
theorem field_V3 : ∀ (D : JointData) (f : Word → JSlice) (k : ℕ) (w : Word), D.S = paperS → 1 ≤ k →
    w = List.replicate k Digit.three ++ [Digit.one] → GoodBelow D f w.length →
      PairCompat (oddFull f w) 0 1 ∧ PairCompat (oddFull f w) 3 4 ∧
        PairCompat (evenFull f w) 0 3 ∧ PairCompat (evenFull f w) 4 5 := by
  intro D f k w hS hk hw hG
  subst hw
  have hl : (List.replicate k Digit.three).length < (List.replicate k Digit.three ++ [Digit.one]).length := by simp
  have hb := FLatticePaper.Tiles.SwapBaseTiles.base_tiles_paper D hS f _ hG (List.replicate k Digit.three) hl
    (Or.inr (Or.inl fun d hd => List.eq_of_mem_replicate hd))
  obtain ⟨c1, c2, c3, c4⟩ := FLatticePaper.Tiles.SwapVacuity.vac_V3 k hk _ _ hb
  have hreg := vt_regs_three_one k hk
  have hnb := vt_nb_one (List.replicate k Digit.three ++ [Digit.one]) (by simp)
  have hc1 : ¬ CorrectedAfterThree (List.replicate k Digit.three ++ [Digit.one]) := by rintro ⟨-, h⟩; simp at h
  have hc2 : ¬ CorrectedAfterTwo (List.replicate k Digit.three ++ [Digit.one]) := by rintro ⟨-, h⟩; simp at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact pairCompat_of_disjoint _ 0 1 _ _ _ _ _
      (vt_oddTOdd f _ _ _ hnb hreg hc1 hl hl 0 (by norm_num))
      (vt_oddTOdd f _ _ _ hnb hreg hc1 hl hl 1 (by norm_num)) c1
  · exact pairCompat_of_disjoint _ 3 4 _ _ _ _ _
      (vt_oddTEven f _ _ _ hnb hreg hc1 hl hl 3 (by norm_num) (by norm_num))
      (vt_oddTEven f _ _ _ hnb hreg hc1 hl hl 4 (by norm_num) (by norm_num)) c2
  · exact pairCompat_of_disjoint _ 0 3 _ _ _ _ _
      (vt_evenTOdd f _ _ _ hnb hreg hc2 hl hl 0 (by norm_num))
      (vt_evenTOdd f _ _ _ hnb hreg hc2 hl hl 3 (by norm_num)) c3
  · exact pairCompat_of_disjoint _ 4 5 _ _ _ _ _
      (vt_evenTEven f _ _ _ hnb hreg hc2 hl hl 4 (by norm_num) (by norm_num))
      (vt_evenTEven f _ _ _ hnb hreg hc2 hl hl 5 (by norm_num) (by norm_num)) c4

/-- Field `V4`: `w = 2^k 1`, `k ≥ 1`. -/
theorem field_V4 : ∀ (D : JointData) (f : Word → JSlice) (k : ℕ) (w : Word), D.S = paperS → 1 ≤ k →
    w = List.replicate k Digit.two ++ [Digit.one] → GoodBelow D f w.length →
      PairCompat (oddFull f w) 0 1 ∧ PairCompat (oddFull f w) 3 4 ∧
        PairCompat (evenFull f w) 0 3 ∧ PairCompat (evenFull f w) 4 5 := by
  intro D f k w hS hk hw hG
  subst hw
  have hl : (List.replicate k Digit.two).length < (List.replicate k Digit.two ++ [Digit.one]).length := by simp
  have hb := FLatticePaper.Tiles.SwapBaseTiles.base_tiles_paper D hS f _ hG (List.replicate k Digit.two) hl
    (Or.inr (Or.inr fun d hd => List.eq_of_mem_replicate hd))
  obtain ⟨c1, c2, c3, c4⟩ := FLatticePaper.Tiles.SwapVacuity.vac_V4 k hk _ _ hb
  have hreg := vt_regs_two_one k hk
  have hnb := vt_nb_one (List.replicate k Digit.two ++ [Digit.one]) (by simp)
  have hc1 : ¬ CorrectedAfterThree (List.replicate k Digit.two ++ [Digit.one]) := by rintro ⟨-, h⟩; simp at h
  have hc2 : ¬ CorrectedAfterTwo (List.replicate k Digit.two ++ [Digit.one]) := by rintro ⟨-, h⟩; simp at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact pairCompat_of_disjoint _ 0 1 _ _ _ _ _
      (vt_oddTOdd f _ _ _ hnb hreg hc1 hl hl 0 (by norm_num))
      (vt_oddTOdd f _ _ _ hnb hreg hc1 hl hl 1 (by norm_num)) c1
  · exact pairCompat_of_disjoint _ 3 4 _ _ _ _ _
      (vt_oddTEven f _ _ _ hnb hreg hc1 hl hl 3 (by norm_num) (by norm_num))
      (vt_oddTEven f _ _ _ hnb hreg hc1 hl hl 4 (by norm_num) (by norm_num)) c2
  · exact pairCompat_of_disjoint _ 0 3 _ _ _ _ _
      (vt_evenTOdd f _ _ _ hnb hreg hc2 hl hl 0 (by norm_num))
      (vt_evenTOdd f _ _ _ hnb hreg hc2 hl hl 3 (by norm_num)) c3
  · exact pairCompat_of_disjoint _ 4 5 _ _ _ _ _
      (vt_evenTEven f _ _ _ hnb hreg hc2 hl hl 4 (by norm_num) (by norm_num))
      (vt_evenTEven f _ _ _ hnb hreg hc2 hl hl 5 (by norm_num) (by norm_num)) c4

/-- Field `V1`: `w = 3^(m+1) 2`. -/
theorem field_V1 : ∀ (D : JointData) (f : Word → JSlice) (m : ℕ) (w : Word), D.S = paperS →
    w = List.replicate (m + 1) Digit.three ++ [Digit.two] → GoodBelow D f w.length →
      PairCompat (oddFull f w) 3 4 ∧ PairCompat (oddFull f w) 2 5 := by
  intro D f m w hS hw hG
  subst hw
  have hl1 : (List.replicate (m + 1) Digit.three).length <
      (List.replicate (m + 1) Digit.three ++ [Digit.two]).length := by simp
  have hl2 : (List.replicate m Digit.three).length <
      (List.replicate (m + 1) Digit.three ++ [Digit.two]).length := by simp
  have hb := FLatticePaper.Tiles.SwapBaseTiles.base_tiles_paper D hS f _ hG (List.replicate m Digit.three) hl2
    (Or.inr (Or.inl fun d hd => List.eq_of_mem_replicate hd))
  have hb' : PaperBaseCond (List.replicate (m + 1 - 1) Digit.three)
      (f (List.replicate m Digit.three)).tOdd (f (List.replicate m Digit.three)).tEven := by
    rw [Nat.add_sub_cancel]; exact hb
  obtain ⟨c1, c2⟩ := FLatticePaper.Tiles.SwapVacuity.vac_V1 (m + 1) (by omega) _ _ hb'
  have hnb := FLatticePaper.Tiles.SwapNonvac.not_isBase_three_two m
  have hreg := FLatticePaper.Tiles.SwapNonvac.regsAt_three_two m
  have hc : ¬ CorrectedAfterThree (List.replicate (m + 1) Digit.three ++ [Digit.two]) := by
    rintro ⟨-, h⟩; simp at h
  refine ⟨?_, ?_⟩
  · exact pairCompat_of_disjoint _ 3 4 _ _ _ _ _
      (vt_oddTEven f _ _ _ hnb hreg hc hl1 hl2 3 (by norm_num) (by norm_num))
      (vt_oddTEven f _ _ _ hnb hreg hc hl1 hl2 4 (by norm_num) (by norm_num)) c1
  · exact pairCompat_of_disjoint _ 2 5 _ _ _ _ _
      (vt_oddTEven f _ _ _ hnb hreg hc hl1 hl2 2 (by norm_num) (by norm_num))
      (vt_oddTEven f _ _ _ hnb hreg hc hl1 hl2 5 (by norm_num) (by norm_num)) c2

/-- Field `V6`: `w = 2^(m+1) 3`. -/
theorem field_V6 : ∀ (D : JointData) (f : Word → JSlice) (m : ℕ) (w : Word), D.S = paperS →
    w = List.replicate (m + 1) Digit.two ++ [Digit.three] → GoodBelow D f w.length →
      PairCompat (evenFull f w) 0 3 ∧ PairCompat (evenFull f w) 1 2 := by
  intro D f m w hS hw hG
  subst hw
  have hl1 : (List.replicate m Digit.two).length < (List.replicate (m + 1) Digit.two ++ [Digit.three]).length := by
    simp
  have hl2 : (List.replicate (m + 1) Digit.two).length <
      (List.replicate (m + 1) Digit.two ++ [Digit.three]).length := by simp
  have hb := FLatticePaper.Tiles.SwapBaseTiles.base_tiles_paper D hS f _ hG (List.replicate m Digit.two) hl1
    (Or.inr (Or.inr fun d hd => List.eq_of_mem_replicate hd))
  obtain ⟨c1, c2⟩ := FLatticePaper.Tiles.SwapVacuity.vac_V6 m _ _ hb
  have hreg := vt_regs_two_three m
  have hnb := vt_nb_mix (List.replicate (m + 1) Digit.two ++ [Digit.three]) (by simp) (by simp)
  have hc : ¬ CorrectedAfterTwo (List.replicate (m + 1) Digit.two ++ [Digit.three]) := by
    rintro ⟨-, h⟩; simp at h
  refine ⟨?_, ?_⟩
  · exact pairCompat_of_disjoint _ 0 3 _ _ _ _ _
      (vt_evenTOdd f _ _ _ hnb hreg hc hl1 hl2 0 (by norm_num))
      (vt_evenTOdd f _ _ _ hnb hreg hc hl1 hl2 3 (by norm_num)) c1
  · exact pairCompat_of_disjoint _ 1 2 _ _ _ _ _
      (vt_evenTOdd f _ _ _ hnb hreg hc hl1 hl2 1 (by norm_num))
      (vt_evenTOdd f _ _ _ hnb hreg hc hl1 hl2 2 (by norm_num)) c2

end FLatticePaper.Tiles.SwapVacuousTerm
