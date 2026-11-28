import FLatticePaper.Tiles.SwapOffsets
import FLatticePaper.Tiles.SwapBaseBlock
import FLatticePaper.Tiles.SwapBaseTiles
import FLatticePaper.Tiles.SwapBaseClauses
import FLatticePaper.Tiles.SwapRegsShape
import FLatticePaper.Tiles.WeakStepAssembly
import FLatticePaper.Tiles.BaseTileProps

/-! # The nonvacuous clauses of `SwapBaseInput`, family by family

Each clause is proved from the block lemma of `SwapBaseBlock` at the closed offsets of `SwapOffsets`, the closed parents of the
base words, and the base tile odometers `base_tiles_paper`. This module starts with the register and phase facts of the
families `3^(m+1) 2` (odd pair (0,1)). -/

namespace FLatticePaper.Tiles.SwapNonvac

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SurgicalWeak FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.WeakStepPaper FLatticePaper.Tiles.JointFamily FLatticePaper.Tiles.TileCompatInputs
open FLatticePaper.Tiles.Standard FLatticePaper.Construction

theorem regsAt_three_succ (n : ℕ) : regsAt (List.replicate (n + 1) Digit.three) = (none, some (List.replicate n Digit.three)) := by
  induction n with
  | zero => simp [regsAt, regRun, regStep]
  | succ n ih =>
    rw [List.replicate_succ' (n := n + 1), regsAt_snoc, ih]
    simp [regStep, List.replicate_succ']

theorem regsAt_two_succ (n : ℕ) : regsAt (List.replicate (n + 1) Digit.two) = (some (List.replicate n Digit.two), none) := by
  induction n with
  | zero => simp [regsAt, regRun, regStep]
  | succ n ih =>
    rw [List.replicate_succ' (n := n + 1), regsAt_snoc, ih]
    simp [regStep, List.replicate_succ']

/-- The registers of `3^(m+1) 2`: the first is `3^(m+1)`, the second `3^m`. -/
theorem regsAt_three_two (m : ℕ) :
    regsAt (List.replicate (m + 1) Digit.three ++ [Digit.two]) =
      (some (List.replicate (m + 1) Digit.three), some (List.replicate m Digit.three)) := by
  rw [regsAt_snoc, regsAt_three_succ]
  simp [regStep]

/-- The phase of `3^n 2` is even (no letter `one`). -/
theorem phase_three_two (n : ℕ) : W1Odd (List.replicate n Digit.three ++ [Digit.two]) = false := by
  simp [W1Odd, phase, List.count_append, List.count_replicate]

/-- The word `3^(m+1) 2` is not a base word. -/
theorem not_isBase_three_two (m : ℕ) : ¬ IsBase (List.replicate (m + 1) Digit.three ++ [Digit.two]) := by
  rintro (h | h | h)
  · simp at h
  · have := h Digit.two (by simp)
    exact absurd this (by decide)
  · have := h Digit.three (by simp)
    exact absurd this (by decide)

/-- Clause N1: the odd pair (0,1) of the word `3^(m+1) 2` (the ladder block with `k = m+1`). The odd child pieces `0,1` sit on
the ladder tile of `3^(m+1)`, and the even parent is `fracEven (3^m) = ⟨1, 2m+3⟩`. -/
theorem clause_N1 (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (w : Word) (m : ℕ)
    (hw : w = List.replicate (m + 1) Digit.three ++ [Digit.two]) (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f w.length) :
    PairCompat (FLatticePaper.Tiles.GlueFull.oddFull f w) 0 1 := by
  subst hw
  have hreg := regsAt_three_two m
  have hnb := not_isBase_three_two m
  have hc : ¬ CorrectedAfterThree (List.replicate (m + 1) Digit.three ++ [Digit.two]) := by
    rintro ⟨-, h⟩
    simp at h
  have hl1 : (List.replicate (m + 1) Digit.three).length <
      (List.replicate (m + 1) Digit.three ++ [Digit.two]).length := by simp
  have hl2 : (List.replicate m Digit.three).length <
      (List.replicate (m + 1) Digit.three ++ [Digit.two]).length := by simp
  have hI3 : IsBase (List.replicate (m + 1) Digit.three) :=
    Or.inr (Or.inl fun d hd => List.eq_of_mem_replicate hd)
  have hb := FLatticePaper.Tiles.SwapBaseTiles.base_tiles_paper D hS f _ hG _ hl1 hI3
  obtain ⟨hOd, hOv, -, -⟩ := hb.2.1 (m + 1) (by omega) rfl
  have hfam : (regsAt (List.replicate (m + 1) Digit.three ++ [Digit.two])).1 =
      some (List.replicate (m + 1) Digit.three) := by rw [hreg]
  have hfam2 : (regsAt (List.replicate (m + 1) Digit.three ++ [Digit.two])).2 =
      some (List.replicate m Digit.three) := by rw [hreg]
  have hp1 : (parentsAt (List.replicate (m + 1) Digit.three ++ [Digit.two])).odd =
      ⟨1, 2 * ((m + 1 : ℕ) : ℤ) + 2⟩ := by
    rw [(FLatticePaper.Tiles.WeakStepAssembly.regsAt_parents _).1 _ hfam]
    exact FLatticePaper.Tiles.BaseTileProps.cur_odd_three (m + 1)
  have hq1 : (parentsAt (List.replicate (m + 1) Digit.three ++ [Digit.two])).even = ⟨1, 2 * (m : ℤ) + 3⟩ := by
    rw [(FLatticePaper.Tiles.WeakStepAssembly.regsAt_parents _).2 _ hfam2]
    exact FLatticePaper.Tiles.BaseTileProps.cur_even_three m
  have hnf : ¬ W1Odd (List.replicate (m + 1) Digit.three ++ [Digit.two]) := by
    rw [phase_three_two]; simp
  have h0 := FLatticePaper.Tiles.GlueFull.oddFull_get f (List.replicate (m + 1) Digit.three ++ [Digit.two])
    (List.replicate (m + 1) Digit.three) (List.replicate m Digit.three) hnb hreg hc hl1 hl2 0 (by norm_num)
  have h1 := FLatticePaper.Tiles.GlueFull.oddFull_get f (List.replicate (m + 1) Digit.three ++ [Digit.two])
    (List.replicate (m + 1) Digit.three) (List.replicate m Digit.three) hnb hreg hc hl1 hl2 1 (by norm_num)
  have e0 : FLatticePaper.Tiles.GlueFull.offO (List.replicate (m + 1) Digit.three ++ [Digit.two]) 0 =
      (4 * ((m + 1 : ℕ) : ℤ) + 2, 2) := by
    rw [FLatticePaper.Tiles.SwapOffsets.offO_0, if_neg hnf, hq1]
    show ((2 * (m : ℤ) + 3, 1) + (2 * (m : ℤ) + 3, 1) : ℤ × ℤ) = _
    rw [Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨by push_cast; ring, by norm_num⟩
  have e1 : FLatticePaper.Tiles.GlueFull.offO (List.replicate (m + 1) Digit.three ++ [Digit.two]) 1 =
      (-2 * ((m + 1 : ℕ) : ℤ), 2 * ((m + 1 : ℕ) : ℤ) + 2) := by
    rw [FLatticePaper.Tiles.SwapOffsets.offO_1, if_neg hnf, hq1]
    show ((1 - (2 * (m : ℤ) + 3), 1 + (2 * (m : ℤ) + 3)) : ℤ × ℤ) = _
    rw [Prod.mk.injEq]
    exact ⟨by push_cast; ring, by push_cast; ring⟩
  have a0 : FLatticePaper.Tiles.ClosedPathAssembly.affOdd (parentsAt (List.replicate (m + 1) Digit.three ++ [Digit.two])).odd
      (parentsAt (List.replicate (m + 1) Digit.three ++ [Digit.two])).even 0 = (0, 0) := by
    simp [FLatticePaper.Tiles.ClosedPathAssembly.affOdd]
    rfl
  have a1 : FLatticePaper.Tiles.ClosedPathAssembly.affOdd (parentsAt (List.replicate (m + 1) Digit.three ++ [Digit.two])).odd
      (parentsAt (List.replicate (m + 1) Digit.three ++ [Digit.two])).even 1 = (1, -(2 * ((m + 1 : ℕ) : ℤ) + 1)) := by
    rw [hq1]
    show ((1 : ℤ), -(2 * (m : ℤ) + 3)) = _
    rw [Prod.mk.injEq]
    exact ⟨rfl, by push_cast; ring⟩
  have hp : (FLatticePaper.Tiles.GlueFull.oddFull f (List.replicate (m + 1) Digit.three ++ [Digit.two]))[0]? =
      some (stdPiece (f (List.replicate (m + 1) Digit.three)).tOdd (4 * ((m + 1 : ℕ) : ℤ) + 2, 2) (0, 0)) := by
    rw [h0, e0, a0]
    simp
  have hq : (FLatticePaper.Tiles.GlueFull.oddFull f (List.replicate (m + 1) Digit.three ++ [Digit.two]))[1]? =
      some (stdPiece (f (List.replicate (m + 1) Digit.three)).tOdd (-2 * ((m + 1 : ℕ) : ℤ), 2 * ((m + 1 : ℕ) : ℤ) + 2)
        (1, -(2 * ((m + 1 : ℕ) : ℤ) + 1))) := by
    rw [h1, e1, a1]
    simp
  exact FLatticePaper.Tiles.SwapBaseBlock.ladder_pairCompat ((m + 1 : ℕ) : ℤ) (by omega) _ 0 1
    (f (List.replicate (m + 1) Digit.three)).tOdd hOd hOv hp hq

theorem site_add_zero_one (z : Site) : z + (0, 1) = (z.1, z.2 + 1) := Prod.ext (add_zero z.1) rfl

/-- The odd tile of `2^k` (`k ≥ 0`) with the near-stair values, read at `x + (0,1)` (`k = 0` is the empty word). -/
theorem two_odd_tile (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (n : ℕ)
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f n) (k : ℕ) (hl : (List.replicate k Digit.two).length < n) :
    (f (List.replicate k Digit.two)).tOdd.dom = nstairN (2 * (k : ℤ) + 3) ∧
      ∀ x ∈ (f (List.replicate k Digit.two)).tOdd.dom,
        (f (List.replicate k Digit.two)).tOdd.val x = paperNearStairValue (2 * (k : ℤ) + 3) (x + (0, 1)) := by
  have hb := FLatticePaper.Tiles.SwapBaseTiles.base_tiles_paper D hS f n hG _ hl
    (Or.inr (Or.inr fun d hd => List.eq_of_mem_replicate hd))
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨hd, hv, -, -⟩ := hb.1 rfl
    have e : (2 * ((0 : ℕ) : ℤ) + 3) = 3 := by norm_num
    rw [e]
    exact ⟨hd, hv⟩
  · obtain ⟨hd, hv, -, -⟩ := hb.2.2 k hk rfl
    exact ⟨hd, hv⟩

theorem not_isBase_three_one (k : ℕ) : ¬ IsBase (List.replicate k Digit.three ++ [Digit.one]) := by
  rintro (h | h | h)
  · simp at h
  · exact absurd (h Digit.one (by simp)) (by decide)
  · exact absurd (h Digit.one (by simp)) (by decide)

theorem not_isBase_two_one (k : ℕ) : ¬ IsBase (List.replicate k Digit.two ++ [Digit.one]) := by
  rintro (h | h | h)
  · simp at h
  · exact absurd (h Digit.one (by simp)) (by decide)
  · exact absurd (h Digit.one (by simp)) (by decide)

theorem not_isBase_two_three (m : ℕ) : ¬ IsBase (List.replicate (m + 1) Digit.two ++ [Digit.three]) := by
  rintro (h | h | h)
  · simp at h
  · exact absurd (h Digit.two (by simp)) (by decide)
  · exact absurd (h Digit.three (by simp)) (by decide)

theorem regsAt_three_one (k : ℕ) :
    regsAt (List.replicate k Digit.three ++ [Digit.one]) =
      (some (List.replicate k Digit.three), some (List.replicate k Digit.three)) := by
  rw [regsAt_snoc]
  simp [regStep]

theorem regsAt_two_one (k : ℕ) :
    regsAt (List.replicate k Digit.two ++ [Digit.one]) =
      (some (List.replicate k Digit.two), some (List.replicate k Digit.two)) := by
  rw [regsAt_snoc]
  simp [regStep]

theorem regsAt_two_three (m : ℕ) :
    regsAt (List.replicate (m + 1) Digit.two ++ [Digit.three]) =
      (some (List.replicate m Digit.two), some (List.replicate (m + 1) Digit.two)) := by
  rw [regsAt_snoc, regsAt_two_succ]
  simp [regStep]

theorem phase_three_one (k : ℕ) : W1Odd (List.replicate k Digit.three ++ [Digit.one]) = true := by
  simp [W1Odd, phase, List.count_append, List.count_replicate]

theorem phase_two_one (k : ℕ) : W1Odd (List.replicate k Digit.two ++ [Digit.one]) = true := by
  simp [W1Odd, phase, List.count_append, List.count_replicate]

theorem phase_two_three (m : ℕ) : W1Odd (List.replicate (m + 1) Digit.two ++ [Digit.three]) = false := by
  simp [W1Odd, phase, List.count_append, List.count_replicate]

theorem three_even_tile (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (n : ℕ)
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f n) (k : ℕ) (hl : (List.replicate k Digit.three).length < n) :
    (f (List.replicate k Digit.three)).tEven.dom = stairF (2 * (k : ℤ) + 3) ∧
      ∀ x ∈ (f (List.replicate k Digit.three)).tEven.dom,
        (f (List.replicate k Digit.three)).tEven.val x = paperStairValue (2 * (k : ℤ) + 3) x := by
  have hb := FLatticePaper.Tiles.SwapBaseTiles.base_tiles_paper D hS f n hG _ hl
    (Or.inr (Or.inl fun d hd => List.eq_of_mem_replicate hd))
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨-, -, hd, hv⟩ := hb.1 rfl
    have e : (2 * ((0 : ℕ) : ℤ) + 3) = 3 := by norm_num
    rw [e]
    exact ⟨hd, hv⟩
  · obtain ⟨-, -, hd, hv⟩ := hb.2.1 k hk rfl
    exact ⟨hd, hv⟩

/-- Clause N2: the odd pair (2,5) of the word `3^k 1` for every `k ≥ 0` (the stair block on the even tile of `3^k`; `k = 0` is
the word `1`). -/
theorem clause_N2 (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (w : Word) (k : ℕ)
    (hw : w = List.replicate k Digit.three ++ [Digit.one])
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f w.length) :
    PairCompat (FLatticePaper.Tiles.GlueFull.oddFull f w) 2 5 := by
  subst hw
  have hreg := regsAt_three_one k
  have hnb := not_isBase_three_one k
  have hc : ¬ CorrectedAfterThree (List.replicate k Digit.three ++ [Digit.one]) := by
    rintro ⟨-, h⟩
    simp at h
  have hl1 : (List.replicate k Digit.three).length < (List.replicate k Digit.three ++ [Digit.one]).length := by simp
  obtain ⟨hEd, hEv⟩ := three_even_tile D hS f _ hG k hl1
  have hp1 : (parentsAt (List.replicate k Digit.three ++ [Digit.one])).odd = ⟨1, 2 * (k : ℤ) + 2⟩ := by
    rw [(FLatticePaper.Tiles.WeakStepAssembly.regsAt_parents _).1 _ (by rw [hreg])]
    exact FLatticePaper.Tiles.BaseTileProps.cur_odd_three k
  have hq1 : (parentsAt (List.replicate k Digit.three ++ [Digit.one])).even = ⟨1, 2 * (k : ℤ) + 3⟩ := by
    rw [(FLatticePaper.Tiles.WeakStepAssembly.regsAt_parents _).2 _ (by rw [hreg])]
    exact FLatticePaper.Tiles.BaseTileProps.cur_even_three k
  have hf := phase_three_one k
  have h2 := FLatticePaper.Tiles.GlueFull.oddFull_get f (List.replicate k Digit.three ++ [Digit.one])
    (List.replicate k Digit.three) (List.replicate k Digit.three) hnb hreg hc hl1 hl1 2 (by norm_num)
  have h5 := FLatticePaper.Tiles.GlueFull.oddFull_get f (List.replicate k Digit.three ++ [Digit.one])
    (List.replicate k Digit.three) (List.replicate k Digit.three) hnb hreg hc hl1 hl1 5 (by norm_num)
  have e2 : FLatticePaper.Tiles.GlueFull.offO (List.replicate k Digit.three ++ [Digit.one]) 2 =
      (4 * (k : ℤ) + 4, 2) := by
    rw [FLatticePaper.Tiles.SwapOffsets.offO_2, if_pos hf, hp1]
    show ((2 * (2 * (k : ℤ) + 2), 2 * 1) : ℤ × ℤ) = _
    rw [Prod.mk.injEq]
    exact ⟨by ring, by norm_num⟩
  have e5 : FLatticePaper.Tiles.GlueFull.offO (List.replicate k Digit.three ++ [Digit.one]) 5 =
      (2, 2 * (k : ℤ) + 4) := by
    rw [FLatticePaper.Tiles.SwapOffsets.offO_5, if_pos hf, hp1, hq1]
    show ((1 - (2 * (k : ℤ) + 2), 1 + (2 * (k : ℤ) + 2)) + (2 * (k : ℤ) + 3, 1) : ℤ × ℤ) = _
    rw [Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  have a2 : FLatticePaper.Tiles.ClosedPathAssembly.affOdd (parentsAt (List.replicate k Digit.three ++ [Digit.one])).odd
      (parentsAt (List.replicate k Digit.three ++ [Digit.one])).even 2 = (0, 0) := by
    simp [FLatticePaper.Tiles.ClosedPathAssembly.affOdd]
    rfl
  have a5 : FLatticePaper.Tiles.ClosedPathAssembly.affOdd (parentsAt (List.replicate k Digit.three ++ [Digit.one])).odd
      (parentsAt (List.replicate k Digit.three ++ [Digit.one])).even 5 = (1, -(2 * (k : ℤ) + 2)) := by
    rw [hp1]
    rfl
  have hp : (FLatticePaper.Tiles.GlueFull.oddFull f (List.replicate k Digit.three ++ [Digit.one]))[2]? =
      some (stdPiece (f (List.replicate k Digit.three)).tEven (4 * (k : ℤ) + 4, 2) (0, 0)) := by
    rw [h2, e2, a2]
    simp
  have hq : (FLatticePaper.Tiles.GlueFull.oddFull f (List.replicate k Digit.three ++ [Digit.one]))[5]? =
      some (stdPiece (f (List.replicate k Digit.three)).tEven (2, 2 * (k : ℤ) + 4) (1, -(2 * (k : ℤ) + 2))) := by
    rw [h5, e5, a5]
    simp
  exact FLatticePaper.Tiles.SwapBaseBlock.stair_pairCompat (k : ℤ) (by positivity) _ 2 5
    (f (List.replicate k Digit.three)).tEven hEd hEv hp hq

/-- Clause N3: the even pair (4,5) of the word `2^(m+1) 3` (the near-ladder block at `k = m+1` on the even tile of `2^(m+1)`,
with the odd parent `fracOdd (2^m) = ⟨m+1, m+2⟩`). -/
theorem clause_N3 (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (w : Word) (m : ℕ)
    (hw : w = List.replicate (m + 1) Digit.two ++ [Digit.three])
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f w.length) :
    PairCompat (FLatticePaper.Tiles.GlueFull.evenFull f w) 4 5 := by
  subst hw
  have hreg := regsAt_two_three m
  have hnb := not_isBase_two_three m
  have hc : ¬ CorrectedAfterTwo (List.replicate (m + 1) Digit.two ++ [Digit.three]) := by
    rintro ⟨-, h⟩
    simp at h
  have hl1 : (List.replicate m Digit.two).length < (List.replicate (m + 1) Digit.two ++ [Digit.three]).length := by simp
  have hl2 : (List.replicate (m + 1) Digit.two).length < (List.replicate (m + 1) Digit.two ++ [Digit.three]).length := by simp
  have hI2 : IsBase (List.replicate (m + 1) Digit.two) :=
    Or.inr (Or.inr fun d hd => List.eq_of_mem_replicate hd)
  have hb := FLatticePaper.Tiles.SwapBaseTiles.base_tiles_paper D hS f _ hG _ hl2 hI2
  obtain ⟨-, -, hEd, hEv⟩ := hb.2.2 (m + 1) (by omega) rfl
  have hp1 : (parentsAt (List.replicate (m + 1) Digit.two ++ [Digit.three])).odd =
      ⟨(m : ℤ) + 1, (m : ℤ) + 2⟩ := by
    rw [(FLatticePaper.Tiles.WeakStepAssembly.regsAt_parents _).1 _ (by rw [hreg])]
    exact FLatticePaper.Tiles.BaseTileProps.cur_odd_two m
  have hf := phase_two_three m
  have h4 := FLatticePaper.Tiles.GlueFull.evenFull_get f (List.replicate (m + 1) Digit.two ++ [Digit.three])
    (List.replicate m Digit.two) (List.replicate (m + 1) Digit.two) hnb hreg hc hl1 hl2 4 (by norm_num)
  have h5 := FLatticePaper.Tiles.GlueFull.evenFull_get f (List.replicate (m + 1) Digit.two ++ [Digit.three])
    (List.replicate m Digit.two) (List.replicate (m + 1) Digit.two) hnb hreg hc hl1 hl2 5 (by norm_num)
  have e4 : FLatticePaper.Tiles.GlueFull.offE (List.replicate (m + 1) Digit.two ++ [Digit.three]) 4 = 0 := by
    rw [FLatticePaper.Tiles.SwapOffsets.offE_4, if_neg (by rw [hf]; decide)]
  have e5 : FLatticePaper.Tiles.GlueFull.offE (List.replicate (m + 1) Digit.two ++ [Digit.three]) 5 =
      (2 * ((m + 1 : ℕ) : ℤ), 6 * ((m + 1 : ℕ) : ℤ) + 2) := by
    rw [FLatticePaper.Tiles.SwapOffsets.offE_5, if_neg (by rw [hf]; decide), hp1]
    simp only [texV1Odd, texV2, Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨by push_cast; ring, by push_cast; ring⟩
  have a4 : FLatticePaper.Tiles.ClosedPathAssembly.affEven (parentsAt (List.replicate (m + 1) Digit.two ++ [Digit.three])).odd
      (parentsAt (List.replicate (m + 1) Digit.two ++ [Digit.three])).even 4 = (0, 0) := by
    simp [FLatticePaper.Tiles.ClosedPathAssembly.affEven]
    rfl
  have a5 : FLatticePaper.Tiles.ClosedPathAssembly.affEven (parentsAt (List.replicate (m + 1) Digit.two ++ [Digit.three])).odd
      (parentsAt (List.replicate (m + 1) Digit.two ++ [Digit.three])).even 5 =
      (2 * ((m + 1 : ℕ) : ℤ), -(2 * ((m + 1 : ℕ) : ℤ) + 2)) := by
    rw [hp1]
    show (((m : ℤ) + 1, -((m : ℤ) + 2)) + ((m : ℤ) + 1, -((m : ℤ) + 2)) : ℤ × ℤ) = _
    rw [Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨by push_cast; ring, by push_cast; ring⟩
  have hp : (FLatticePaper.Tiles.GlueFull.evenFull f (List.replicate (m + 1) Digit.two ++ [Digit.three]))[4]? =
      some (stdPiece (f (List.replicate (m + 1) Digit.two)).tEven 0 (0, 0)) := by
    rw [h4, e4, a4]
    simp
  have hq : (FLatticePaper.Tiles.GlueFull.evenFull f (List.replicate (m + 1) Digit.two ++ [Digit.three]))[5]? =
      some (stdPiece (f (List.replicate (m + 1) Digit.two)).tEven (2 * ((m + 1 : ℕ) : ℤ), 6 * ((m + 1 : ℕ) : ℤ) + 2)
        (2 * ((m + 1 : ℕ) : ℤ), -(2 * ((m + 1 : ℕ) : ℤ) + 2))) := by
    rw [h5, e5, a5]
    simp
  have hv : ∀ z ∈ (f (List.replicate (m + 1) Digit.two)).tEven.dom,
      (f (List.replicate (m + 1) Digit.two)).tEven.val z =
        paperNearLadderValue (2 * ((m + 1 : ℕ) : ℤ) + 2) (z.1, z.2 + 1) := fun z hz => by
    rw [hEv z hz, site_add_zero_one z]
  exact FLatticePaper.Tiles.SwapBaseBlock.nladder_pairCompat ((m + 1 : ℕ) : ℤ) (by omega) _ 4 5
    (f (List.replicate (m + 1) Digit.two)).tEven hEd hv hp hq

/-- Clause N4: the even pair (1,2) of the word `2^k 1` for every `k ≥ 0` (the near-stair block at `k` on the odd tile of
`2^k`; `k = 0` is the word `1` with the empty register). -/
theorem clause_N4 (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (w : Word) (k : ℕ)
    (hw : w = List.replicate k Digit.two ++ [Digit.one])
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f w.length) :
    PairCompat (FLatticePaper.Tiles.GlueFull.evenFull f w) 1 2 := by
  subst hw
  have hreg := regsAt_two_one k
  have hnb := not_isBase_two_one k
  have hc : ¬ CorrectedAfterTwo (List.replicate k Digit.two ++ [Digit.one]) := by
    rintro ⟨-, h⟩
    simp at h
  have hl1 : (List.replicate k Digit.two).length < (List.replicate k Digit.two ++ [Digit.one]).length := by simp
  have hl2 : (List.replicate k Digit.two).length < (List.replicate k Digit.two ++ [Digit.one]).length := by simp
  obtain ⟨hOd, hOv⟩ := two_odd_tile D hS f _ hG k hl1
  have hp1 : (parentsAt (List.replicate k Digit.two ++ [Digit.one])).odd = ⟨(k : ℤ) + 1, (k : ℤ) + 2⟩ := by
    rw [(FLatticePaper.Tiles.WeakStepAssembly.regsAt_parents _).1 _ (by rw [hreg])]
    exact FLatticePaper.Tiles.BaseTileProps.cur_odd_two k
  have hq1 : (parentsAt (List.replicate k Digit.two ++ [Digit.one])).even = ⟨2 * (k : ℤ) + 1, 2 * (k : ℤ) + 3⟩ := by
    rw [(FLatticePaper.Tiles.WeakStepAssembly.regsAt_parents _).2 _ (by rw [hreg])]
    exact FLatticePaper.Tiles.BaseTileProps.cur_even_two k
  have hf := phase_two_one k
  have h1 := FLatticePaper.Tiles.GlueFull.evenFull_get f (List.replicate k Digit.two ++ [Digit.one])
    (List.replicate k Digit.two) (List.replicate k Digit.two) hnb hreg hc hl1 hl2 1 (by norm_num)
  have h2 := FLatticePaper.Tiles.GlueFull.evenFull_get f (List.replicate k Digit.two ++ [Digit.one])
    (List.replicate k Digit.two) (List.replicate k Digit.two) hnb hreg hc hl1 hl2 2 (by norm_num)
  have e1 : FLatticePaper.Tiles.GlueFull.offE (List.replicate k Digit.two ++ [Digit.one]) 1 = (-1, 2 * (k : ℤ) + 3) := by
    rw [FLatticePaper.Tiles.SwapOffsets.offE_1, if_pos hf, hp1]
    show ((((k : ℤ) + 1 - ((k : ℤ) + 2)), ((k : ℤ) + 1 + ((k : ℤ) + 2))) : ℤ × ℤ) = _
    rw [Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  have e2 : FLatticePaper.Tiles.GlueFull.offE (List.replicate k Digit.two ++ [Digit.one]) 2 =
      (2 * (k : ℤ) + 1, 6 * (k : ℤ) + 5) := by
    rw [FLatticePaper.Tiles.SwapOffsets.offE_2, if_pos hf, hq1]
    show ((((2 * (k : ℤ) + 3), (2 * (k : ℤ) + 1)) + ((2 * (k : ℤ) + 1 - (2 * (k : ℤ) + 3)),
      (2 * (k : ℤ) + 1 + (2 * (k : ℤ) + 3)))) : ℤ × ℤ) = _
    rw [Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  have a1 : FLatticePaper.Tiles.ClosedPathAssembly.affEven (parentsAt (List.replicate k Digit.two ++ [Digit.one])).odd
      (parentsAt (List.replicate k Digit.two ++ [Digit.one])).even 1 = ((k : ℤ) + 1, -((k : ℤ) + 2)) := by
    rw [hp1]
    rfl
  have a2 : FLatticePaper.Tiles.ClosedPathAssembly.affEven (parentsAt (List.replicate k Digit.two ++ [Digit.one])).odd
      (parentsAt (List.replicate k Digit.two ++ [Digit.one])).even 2 = (2 * (k : ℤ) + 1, -(2 * (k : ℤ) + 3)) := by
    rw [hq1]
    rfl
  have hp : (FLatticePaper.Tiles.GlueFull.evenFull f (List.replicate k Digit.two ++ [Digit.one]))[1]? =
      some (stdPiece (f (List.replicate k Digit.two)).tOdd (-1, 2 * (k : ℤ) + 3) ((k : ℤ) + 1, -((k : ℤ) + 2))) := by
    rw [h1, e1, a1]
    simp
  have hq : (FLatticePaper.Tiles.GlueFull.evenFull f (List.replicate k Digit.two ++ [Digit.one]))[2]? =
      some (stdPiece (f (List.replicate k Digit.two)).tOdd (2 * (k : ℤ) + 1, 6 * (k : ℤ) + 5)
        (2 * (k : ℤ) + 1, -(2 * (k : ℤ) + 3))) := by
    rw [h2, e2, a2]
    simp
  have hv : ∀ z ∈ (f (List.replicate k Digit.two)).tOdd.dom,
      (f (List.replicate k Digit.two)).tOdd.val z = paperNearStairValue (2 * (k : ℤ) + 3) (z.1, z.2 + 1) := fun z hz => by
    rw [hOv z hz, site_add_zero_one z]
  exact FLatticePaper.Tiles.SwapBaseBlock.nstair_pairCompat (k : ℤ) (by positivity) _ 1 2
    (f (List.replicate k Digit.two)).tOdd hOd hv hp hq

end FLatticePaper.Tiles.SwapNonvac
