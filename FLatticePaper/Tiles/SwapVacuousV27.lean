import FLatticePaper.Tiles.SwapVacuousSpec
import FLatticePaper.Tiles.SwapBaseClauses
import FLatticePaper.Tiles.SwapOffsets
import FLatticePaper.Tiles.SwapNonvac
import FLatticePaper.Tiles.SwapRegions
import FLatticePaper.Tiles.SwapBaseTiles
import FLatticePaper.Tiles.BaseTileProps
import FLatticePaper.Tiles.StandardBaseBridge
import FLatticePaper.Tiles.SwapBaseInputAssembly

/-! # The vacuous families V2 and V7 of `SwapBaseInput`

Helpers: the disjointness of two translates of a box (`disjoint_of_box`), the boxes of the base even tiles `stairF` and
`nladderN`, and the closed parents of `u d 2^m` and `u d 3^m` (iterated `Parents.step`). -/

namespace FLatticePaper.Tiles.SwapVacuousV27

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.JointFamily FLatticePaper.Tiles.SurgicalWeak
open FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.Standard FLatticePaper.Construction
open FLatticePaper.Tiles.WeakStepPaper
open FLatticePaper.Tiles.TileCompatInputs

/-- Two translates of a finite set inside a box are disjoint when the difference of the two shifts is outside the difference
of the box. -/
theorem disjoint_of_box (T : Finset Site) (lx hx ly hy : ℤ)
    (hT : ∀ z ∈ T, lx ≤ z.1 ∧ z.1 ≤ hx ∧ ly ≤ z.2 ∧ z.2 ≤ hy) (o1 o2 : Site)
    (hsep : o2.1 - o1.1 < lx - hx ∨ hx - lx < o2.1 - o1.1 ∨ o2.2 - o1.2 < ly - hy ∨ hy - ly < o2.2 - o1.2) :
    ∀ x ∈ T, ∀ y ∈ T, x + o1 ≠ y + o2 := by
  intro x hxT y hyT h
  have h1 := hT x hxT
  have h2 := hT y hyT
  have e1 : x.1 + o1.1 = y.1 + o2.1 := by
    have := congrArg Prod.fst h
    simpa using this
  have e2 : x.2 + o1.2 = y.2 + o2.2 := by
    have := congrArg Prod.snd h
    simpa using this
  rcases hsep with h3 | h3 | h3 | h3 <;> omega

/-- The even tile `stairF d` (`d ≥ 2`) lies in the box `[2-d, d] × [0, d+1]`. -/
theorem stairF_box (d : ℤ) (hd : 2 ≤ d) : ∀ z ∈ stairF d, 2 - d ≤ z.1 ∧ z.1 ≤ d ∧ 0 ≤ z.2 ∧ z.2 ≤ d + 1 := by
  intro z hz
  rw [mem_stairF_iff_paper hd] at hz
  simp only [paperStairTile, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.ext_iff] at hz
  rcases hz with h | h | h
  · omega
  · omega
  · omega

/-- The even tile `nladderN d` (`d ≥ 2`) lies in the box `[-1, d+1] × [0, 3d-2]`. -/
theorem nladderN_box (d : ℤ) (hd : 2 ≤ d) : ∀ z ∈ nladderN d, -1 ≤ z.1 ∧ z.1 ≤ d + 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 3 * d - 2 := by
  intro z hz
  rw [mem_nladderN_iff_paper hd] at hz
  rw [SwapRegions.nl_tile_mem] at hz
  omega

/-- The parents of a word of the form `v ++ 2^m`: iterate the odd step `odd + even` (`Parents.step` at `two`). -/
theorem walk_two_iter (P : Parents) (m : ℕ) :
    P.walk (List.replicate m Digit.two) =
      ⟨⟨P.odd.num + (m : ℤ) * P.even.num, P.odd.den + (m : ℤ) * P.even.den⟩, P.even⟩ := by
  induction m with
  | zero => cases P; simp [Parents.walk]
  | succ m ih =>
    rw [List.replicate_succ', Parents.walk_append, ih]
    simp only [Parents.walk, List.foldl, Parents.step, Parents.current, Parents.combine]
    simp only [Nat.cast_succ]
    congr 2 <;> ring

/-- The parents of `v ++ 2^m`. -/
theorem parentsAt_append_rep_two (X : Word) (m : ℕ) :
    parentsAt (X ++ List.replicate m Digit.two) = (parentsAt X).walk (List.replicate m Digit.two) := by
  unfold parentsAt
  rw [Parents.walk_append]

/-- The registers of `x 2^(j+1)`: the first is the prefix `x 2^j`. -/
theorem regsAt_rep_two_fst (x : Word) (j : ℕ) :
    (regsAt (x ++ List.replicate (j + 1) Digit.two)).1 = some (x ++ List.replicate j Digit.two) := by
  rw [List.replicate_succ', ← List.append_assoc, WeakStepPaper.regsAt_snoc]
  simp [regStep]

/-- The second register is unchanged by the letters `two`. -/
theorem regsAt_rep_two_snd (x : Word) (j : ℕ) :
    (regsAt (x ++ List.replicate j Digit.two)).2 = (regsAt x).2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ', ← List.append_assoc, WeakStepPaper.regsAt_snoc, ← ih]
    simp [regStep]

/-- The second register of `u d` (`d ∈ {one, three}`) is `u`. -/
theorem regsAt_snd_of_one_three (u : Word) (d : Digit) (hd : d = Digit.one ∨ d = Digit.three) :
    (regsAt (u ++ [d])).2 = some u := by
  rw [WeakStepPaper.regsAt_snoc]
  rcases hd with rfl | rfl
  · simp [regStep]
  · simp [regStep]

/-- The last letter of `u d 2^(m+1)` is `two`. -/
theorem getLast_v2 (u : Word) (d : Digit) (m : ℕ) :
    (u ++ [d] ++ List.replicate (m + 1) Digit.two).getLast? = some Digit.two := by
  rw [List.replicate_succ', ← List.append_assoc, List.getLast?_append]
  simp

/-- `u d 2^(m+1)` with `d ∈ {one, three}` is not a base word. -/
theorem not_isBase_v2 (u : Word) (d : Digit) (m : ℕ) (hd : d = Digit.one ∨ d = Digit.three) :
    ¬ IsBase (u ++ [d] ++ List.replicate (m + 1) Digit.two) := by
  rintro (h | h | h)
  · simp at h
  · have := h Digit.two (by simp)
    exact absurd this (by decide)
  · have := h d (by simp)
    rcases hd with rfl | rfl <;> exact absurd this (by decide)

/-- The parents of `3^a 1 2^m` (`parents_three` then one step of `one`, then `m` steps of `two`). -/
theorem parents_three_one (a m : ℕ) :
    parentsAt (List.replicate a Digit.three ++ [Digit.one] ++ List.replicate m Digit.two) =
      ⟨⟨1 + (m : ℤ), 2 * (a : ℤ) + 2 + (m : ℤ) * (2 * (a : ℤ) + 3)⟩, ⟨1, 2 * (a : ℤ) + 3⟩⟩ := by
  have hX : parentsAt (List.replicate a Digit.three ++ [Digit.one]) = ⟨⟨1, 2 * (a : ℤ) + 2⟩, ⟨1, 2 * (a : ℤ) + 3⟩⟩ := by
    rw [parentsAt_append_singleton, FLatticePaper.Tiles.BaseTileProps.parents_three]
    simp only [Parents.step, Parents.current, Parents.combine]
    congr 2 <;> ring
  rw [parentsAt_append_rep_two, hX, walk_two_iter]
  congr 2
  ring

/-- The parents of `3^a 3 2^m`. -/
theorem parents_three_three (a m : ℕ) :
    parentsAt (List.replicate a Digit.three ++ [Digit.three] ++ List.replicate m Digit.two) =
      ⟨⟨(m : ℤ), 1 + (m : ℤ) * (2 * (a : ℤ) + 3)⟩, ⟨1, 2 * (a : ℤ) + 3⟩⟩ := by
  have hX : parentsAt (List.replicate a Digit.three ++ [Digit.three]) = ⟨⟨0, 1⟩, ⟨1, 2 * (a : ℤ) + 3⟩⟩ := by
    rw [parentsAt_append_singleton, FLatticePaper.Tiles.BaseTileProps.parents_three]
    simp only [Parents.step, Parents.current, Parents.combine]
    congr 2
    ring
  rw [parentsAt_append_rep_two, hX, walk_two_iter]
  congr 2
  ring

/-- The parents of `2^b d 2^m` (`parents_two`, then `d`, then `m` steps of `two`), for `d = one`. -/
theorem parents_two_one (b m : ℕ) :
    parentsAt (List.replicate b Digit.two ++ [Digit.one] ++ List.replicate m Digit.two) =
      ⟨⟨(b : ℤ) + 1 + (m : ℤ) * (2 * (b : ℤ) + 1), (b : ℤ) + 2 + (m : ℤ) * (2 * (b : ℤ) + 3)⟩,
        ⟨2 * (b : ℤ) + 1, 2 * (b : ℤ) + 3⟩⟩ := by
  have hX : parentsAt (List.replicate b Digit.two ++ [Digit.one]) =
      ⟨⟨(b : ℤ) + 1, (b : ℤ) + 2⟩, ⟨2 * (b : ℤ) + 1, 2 * (b : ℤ) + 3⟩⟩ := by
    rw [parentsAt_append_singleton, FLatticePaper.Tiles.BaseTileProps.parents_two]
    simp only [Parents.step, Parents.current, Parents.combine]
    congr 2 <;> ring
  rw [parentsAt_append_rep_two, hX, walk_two_iter]

/-- The parents of `2^b 3 2^m`, for `d = three`. -/
theorem parents_two_three (b m : ℕ) :
    parentsAt (List.replicate b Digit.two ++ [Digit.three] ++ List.replicate m Digit.two) =
      ⟨⟨(b : ℤ) + (m : ℤ) * (2 * (b : ℤ) + 1), (b : ℤ) + 1 + (m : ℤ) * (2 * (b : ℤ) + 3)⟩,
        ⟨2 * (b : ℤ) + 1, 2 * (b : ℤ) + 3⟩⟩ := by
  have hX : parentsAt (List.replicate b Digit.two ++ [Digit.three]) =
      ⟨⟨(b : ℤ), (b : ℤ) + 1⟩, ⟨2 * (b : ℤ) + 1, 2 * (b : ℤ) + 3⟩⟩ := by
    rw [parentsAt_append_singleton, FLatticePaper.Tiles.BaseTileProps.parents_two]
    simp only [Parents.step, Parents.current, Parents.combine]
    congr 2
  rw [parentsAt_append_rep_two, hX, walk_two_iter]

theorem phase_three_one_v (a m : ℕ) :
    W1Odd (List.replicate a Digit.three ++ [Digit.one] ++ List.replicate m Digit.two) = true := by
  simp [W1Odd, phase, List.count_append, List.count_replicate]

theorem phase_three_three_v (a m : ℕ) :
    W1Odd (List.replicate a Digit.three ++ [Digit.three] ++ List.replicate m Digit.two) = false := by
  simp [W1Odd, phase, List.count_append, List.count_replicate]

theorem phase_two_one_v (b m : ℕ) :
    W1Odd (List.replicate b Digit.two ++ [Digit.one] ++ List.replicate m Digit.two) = true := by
  simp [W1Odd, phase, List.count_append, List.count_replicate]

theorem phase_two_three_v (b m : ℕ) :
    W1Odd (List.replicate b Digit.two ++ [Digit.three] ++ List.replicate m Digit.two) = false := by
  simp [W1Odd, phase, List.count_append, List.count_replicate]

/-- The glue of V2: the pieces 3,4 and 2,5 of the odd child of `w = u d 2^(m+1)` are the odometer `(f u).tEven` at the
offsets `offO w i`; they are compatible as soon as the offsets are separated with respect to the even tile of `u` (a box). -/
theorem v2_glue (D : JointData) (_hS : D.S = paperS) (f : Word → JSlice) (u : Word) (d : Digit) (m : ℕ)
    (w : Word) (hd : d = Digit.one ∨ d = Digit.three) (hw : w = u ++ [d] ++ List.replicate (m + 1) Digit.two)
    (_hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f w.length)
    (lx hx ly hy : ℤ)
    (hbox : ∀ z ∈ (f u).tEven.dom, lx ≤ z.1 ∧ z.1 ≤ hx ∧ ly ≤ z.2 ∧ z.2 ≤ hy)
    (h34 : (FLatticePaper.Tiles.GlueFull.offO w 4).1 - (FLatticePaper.Tiles.GlueFull.offO w 3).1 < lx - hx ∨
      hx - lx < (FLatticePaper.Tiles.GlueFull.offO w 4).1 - (FLatticePaper.Tiles.GlueFull.offO w 3).1 ∨
      (FLatticePaper.Tiles.GlueFull.offO w 4).2 - (FLatticePaper.Tiles.GlueFull.offO w 3).2 < ly - hy ∨
      hy - ly < (FLatticePaper.Tiles.GlueFull.offO w 4).2 - (FLatticePaper.Tiles.GlueFull.offO w 3).2)
    (h25 : (FLatticePaper.Tiles.GlueFull.offO w 5).1 - (FLatticePaper.Tiles.GlueFull.offO w 2).1 < lx - hx ∨
      hx - lx < (FLatticePaper.Tiles.GlueFull.offO w 5).1 - (FLatticePaper.Tiles.GlueFull.offO w 2).1 ∨
      (FLatticePaper.Tiles.GlueFull.offO w 5).2 - (FLatticePaper.Tiles.GlueFull.offO w 2).2 < ly - hy ∨
      hy - ly < (FLatticePaper.Tiles.GlueFull.offO w 5).2 - (FLatticePaper.Tiles.GlueFull.offO w 2).2) :
    PairCompat (FLatticePaper.Tiles.GlueFull.oddFull f w) 3 4 ∧
      PairCompat (FLatticePaper.Tiles.GlueFull.oddFull f w) 2 5 := by
  have hreg : regsAt w = (some (u ++ [d] ++ List.replicate m Digit.two), some u) := by
    apply Prod.ext
    · show (regsAt w).1 = _
      rw [hw]
      exact regsAt_rep_two_fst (u ++ [d]) m
    · show (regsAt w).2 = _
      rw [hw, regsAt_rep_two_snd (u ++ [d]) (m + 1)]
      exact regsAt_snd_of_one_three u d hd
  have hnb : ¬ IsBase w := by
    rw [hw]
    exact not_isBase_v2 u d m hd
  have hc : ¬ CorrectedAfterThree w := by
    rintro ⟨-, h⟩
    rw [hw, getLast_v2] at h
    cases h
  have hl1 : (u ++ [d] ++ List.replicate m Digit.two).length < w.length := by
    rw [hw]; simp
  have hl2 : u.length < w.length := by
    rw [hw]; simp
  have h3 := FLatticePaper.Tiles.GlueFull.oddFull_get f w (u ++ [d] ++ List.replicate m Digit.two) u hnb hreg hc hl1 hl2 3
    (by norm_num)
  have h4 := FLatticePaper.Tiles.GlueFull.oddFull_get f w (u ++ [d] ++ List.replicate m Digit.two) u hnb hreg hc hl1 hl2 4
    (by norm_num)
  have h2 := FLatticePaper.Tiles.GlueFull.oddFull_get f w (u ++ [d] ++ List.replicate m Digit.two) u hnb hreg hc hl1 hl2 2
    (by norm_num)
  have h5 := FLatticePaper.Tiles.GlueFull.oddFull_get f w (u ++ [d] ++ List.replicate m Digit.two) u hnb hreg hc hl1 hl2 5
    (by norm_num)
  have hp3 : (FLatticePaper.Tiles.GlueFull.oddFull f w)[3]? = some (stdPiece (f u).tEven
      (FLatticePaper.Tiles.GlueFull.offO w 3) (FLatticePaper.Tiles.ClosedPathAssembly.affOdd (parentsAt w).odd (parentsAt w).even 3)) := by
    rw [h3, if_neg (show ¬ (3 : ℕ) < 2 by norm_num)]
  have hp4 : (FLatticePaper.Tiles.GlueFull.oddFull f w)[4]? = some (stdPiece (f u).tEven
      (FLatticePaper.Tiles.GlueFull.offO w 4) (FLatticePaper.Tiles.ClosedPathAssembly.affOdd (parentsAt w).odd (parentsAt w).even 4)) := by
    rw [h4, if_neg (show ¬ (4 : ℕ) < 2 by norm_num)]
  have hp2 : (FLatticePaper.Tiles.GlueFull.oddFull f w)[2]? = some (stdPiece (f u).tEven
      (FLatticePaper.Tiles.GlueFull.offO w 2) (FLatticePaper.Tiles.ClosedPathAssembly.affOdd (parentsAt w).odd (parentsAt w).even 2)) := by
    rw [h2, if_neg (show ¬ (2 : ℕ) < 2 by norm_num)]
  have hp5 : (FLatticePaper.Tiles.GlueFull.oddFull f w)[5]? = some (stdPiece (f u).tEven
      (FLatticePaper.Tiles.GlueFull.offO w 5) (FLatticePaper.Tiles.ClosedPathAssembly.affOdd (parentsAt w).odd (parentsAt w).even 5)) := by
    rw [h5, if_neg (show ¬ (5 : ℕ) < 2 by norm_num)]
  exact ⟨FLatticePaper.Tiles.SwapBaseClauses.pairCompat_of_disjoint _ 3 4 _ _ _ _ _ hp3 hp4
      (disjoint_of_box _ lx hx ly hy hbox _ _ h34),
    FLatticePaper.Tiles.SwapBaseClauses.pairCompat_of_disjoint _ 2 5 _ _ _ _ _ hp2 hp5
      (disjoint_of_box _ lx hx ly hy hbox _ _ h25)⟩


/-- The even tile of `2^(b)` (`b ≥ 1`) is `nladderN (2b+2)`. -/
theorem two_even_dom (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (n : ℕ)
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f n) (b : ℕ) (hb : 1 ≤ b)
    (hl : (List.replicate b Digit.two).length < n) :
    (f (List.replicate b Digit.two)).tEven.dom = nladderN (2 * (b : ℤ) + 2) := by
  have hb' := FLatticePaper.Tiles.SwapBaseTiles.base_tiles_paper D hS f n hG _ hl
    (Or.inr (Or.inr fun d hd => List.eq_of_mem_replicate hd))
  obtain ⟨-, -, hd, -⟩ := hb'.2.2 b hb rfl
  exact hd

/-- V2 for the odd base `3^a`, `d = one`: the pairs are separated along the first coordinate. -/
theorem v2_three_one (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (a m : ℕ)
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f
      (List.replicate a Digit.three ++ [Digit.one] ++ List.replicate (m + 1) Digit.two).length) :
    PairCompat (FLatticePaper.Tiles.GlueFull.oddFull f (List.replicate a Digit.three ++ [Digit.one] ++
        List.replicate (m + 1) Digit.two)) 3 4 ∧
      PairCompat (FLatticePaper.Tiles.GlueFull.oddFull f (List.replicate a Digit.three ++ [Digit.one] ++
        List.replicate (m + 1) Digit.two)) 2 5 := by
  have hl : (List.replicate a Digit.three).length <
      (List.replicate a Digit.three ++ [Digit.one] ++ List.replicate (m + 1) Digit.two).length := by simp
  have hd := FLatticePaper.Tiles.SwapNonvac.three_even_tile D hS f _ hG a hl
  have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
  have ha : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
  refine v2_glue D hS f (List.replicate a Digit.three) Digit.one m _ (Or.inl rfl) rfl hG
    (2 - (2 * (a : ℤ) + 3)) (2 * (a : ℤ) + 3) 0 (2 * (a : ℤ) + 3 + 1) ?_ ?_ ?_
  · intro z hz
    rw [hd.1] at hz
    exact stairF_box _ (by omega) z hz
  · left
    simp only [FLatticePaper.Tiles.SwapOffsets.offO_4, FLatticePaper.Tiles.SwapOffsets.offO_3,
      phase_three_one_v, parents_three_one, if_true]
    simp [texV1Odd, texV1Even, texV2]
    nlinarith [mul_nonneg hm ha, mul_nonneg hm (show (0 : ℤ) ≤ 6 * (a : ℤ) + 8 by positivity)]
  · left
    simp only [FLatticePaper.Tiles.SwapOffsets.offO_5, FLatticePaper.Tiles.SwapOffsets.offO_2,
      phase_three_one_v, parents_three_one, if_true]
    simp [texV1Odd, texV1Even, texV2]
    nlinarith [mul_nonneg hm ha, mul_nonneg hm (show (0 : ℤ) ≤ 6 * (a : ℤ) + 8 by positivity)]

/-- V2 for the odd base `3^a`, `d = three`: the pairs are separated along the second coordinate. -/
theorem v2_three_three (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (a m : ℕ)
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f
      (List.replicate a Digit.three ++ [Digit.three] ++ List.replicate (m + 1) Digit.two).length) :
    PairCompat (FLatticePaper.Tiles.GlueFull.oddFull f (List.replicate a Digit.three ++ [Digit.three] ++
        List.replicate (m + 1) Digit.two)) 3 4 ∧
      PairCompat (FLatticePaper.Tiles.GlueFull.oddFull f (List.replicate a Digit.three ++ [Digit.three] ++
        List.replicate (m + 1) Digit.two)) 2 5 := by
  have hl : (List.replicate a Digit.three).length <
      (List.replicate a Digit.three ++ [Digit.three] ++ List.replicate (m + 1) Digit.two).length := by simp
  have hd := FLatticePaper.Tiles.SwapNonvac.three_even_tile D hS f _ hG a hl
  have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
  have ha : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
  refine v2_glue D hS f (List.replicate a Digit.three) Digit.three m _ (Or.inr rfl) rfl hG
    (2 - (2 * (a : ℤ) + 3)) (2 * (a : ℤ) + 3) 0 (2 * (a : ℤ) + 3 + 1) ?_ ?_ ?_
  · intro z hz
    rw [hd.1] at hz
    exact stairF_box _ (by omega) z hz
  · right; right; right
    simp only [FLatticePaper.Tiles.SwapOffsets.offO_4, FLatticePaper.Tiles.SwapOffsets.offO_3,
      phase_three_three_v, parents_three_three, if_false, Bool.false_eq_true]
    simp [texV1Odd, texV1Even, texV2]
    nlinarith [mul_nonneg hm ha]
  · right; right; right
    simp only [FLatticePaper.Tiles.SwapOffsets.offO_5, FLatticePaper.Tiles.SwapOffsets.offO_2,
      phase_three_three_v, parents_three_three, if_false, Bool.false_eq_true]
    simp [texV1Odd, texV1Even, texV2]
    nlinarith [mul_nonneg hm ha]

/-- V2 for the even base `2^b` (`b ≥ 1`), `d = one`: separated along the first coordinate. -/
theorem v2_two_one (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (b m : ℕ) (hb : 1 ≤ b)
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f
      (List.replicate b Digit.two ++ [Digit.one] ++ List.replicate (m + 1) Digit.two).length) :
    PairCompat (FLatticePaper.Tiles.GlueFull.oddFull f (List.replicate b Digit.two ++ [Digit.one] ++
        List.replicate (m + 1) Digit.two)) 3 4 ∧
      PairCompat (FLatticePaper.Tiles.GlueFull.oddFull f (List.replicate b Digit.two ++ [Digit.one] ++
        List.replicate (m + 1) Digit.two)) 2 5 := by
  have hl : (List.replicate b Digit.two).length <
      (List.replicate b Digit.two ++ [Digit.one] ++ List.replicate (m + 1) Digit.two).length := by simp
  have hd := two_even_dom D hS f _ hG b hb hl
  have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
  have hb' : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
  refine v2_glue D hS f (List.replicate b Digit.two) Digit.one m _ (Or.inl rfl) rfl hG
    (-1) (2 * (b : ℤ) + 3) 0 (6 * (b : ℤ) + 4) ?_ ?_ ?_
  · intro z hz
    rw [hd] at hz
    have := nladderN_box (2 * (b : ℤ) + 2) (by omega) z hz
    omega
  · left
    simp only [FLatticePaper.Tiles.SwapOffsets.offO_4, FLatticePaper.Tiles.SwapOffsets.offO_3,
      phase_two_one_v, parents_two_one, if_true]
    simp [texV1Odd, texV1Even, texV2]
    nlinarith [mul_nonneg hm hb', mul_nonneg hm (show (0 : ℤ) ≤ 4 * (b : ℤ) + 8 by positivity)]
  · left
    simp only [FLatticePaper.Tiles.SwapOffsets.offO_5, FLatticePaper.Tiles.SwapOffsets.offO_2,
      phase_two_one_v, parents_two_one, if_true]
    simp [texV1Odd, texV1Even, texV2]
    nlinarith [mul_nonneg hm hb', mul_nonneg hm (show (0 : ℤ) ≤ 4 * (b : ℤ) + 8 by positivity)]

/-- V2 for the even base `2^b` (`b ≥ 1`), `d = three`: separated along the second coordinate. -/
theorem v2_two_three (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (b m : ℕ) (hb : 1 ≤ b)
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f
      (List.replicate b Digit.two ++ [Digit.three] ++ List.replicate (m + 1) Digit.two).length) :
    PairCompat (FLatticePaper.Tiles.GlueFull.oddFull f (List.replicate b Digit.two ++ [Digit.three] ++
        List.replicate (m + 1) Digit.two)) 3 4 ∧
      PairCompat (FLatticePaper.Tiles.GlueFull.oddFull f (List.replicate b Digit.two ++ [Digit.three] ++
        List.replicate (m + 1) Digit.two)) 2 5 := by
  have hl : (List.replicate b Digit.two).length <
      (List.replicate b Digit.two ++ [Digit.three] ++ List.replicate (m + 1) Digit.two).length := by simp
  have hd := two_even_dom D hS f _ hG b hb hl
  have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
  have hb' : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
  refine v2_glue D hS f (List.replicate b Digit.two) Digit.three m _ (Or.inr rfl) rfl hG
    (-1) (2 * (b : ℤ) + 3) 0 (6 * (b : ℤ) + 4) ?_ ?_ ?_
  · intro z hz
    rw [hd] at hz
    have := nladderN_box (2 * (b : ℤ) + 2) (by omega) z hz
    omega
  · right; right; right
    simp only [FLatticePaper.Tiles.SwapOffsets.offO_4, FLatticePaper.Tiles.SwapOffsets.offO_3,
      phase_two_three_v, parents_two_three, if_false, Bool.false_eq_true]
    simp [texV1Odd, texV1Even, texV2]
    nlinarith [mul_nonneg hm hb']
  · right; right; right
    simp only [FLatticePaper.Tiles.SwapOffsets.offO_5, FLatticePaper.Tiles.SwapOffsets.offO_2,
      phase_two_three_v, parents_two_three, if_false, Bool.false_eq_true]
    simp [texV1Odd, texV1Even, texV2]
    nlinarith [mul_nonneg hm hb']

/-- **V2**, the vacuous family `u d 2^m` (`u` a base word, `d ∈ {1,3}`, `m ≥ 1`). -/
theorem vac_V2 (D : JointData) (f : Word → JSlice) (u : Word) (d : Digit) (m : ℕ) (w : Word)
    (hS : D.S = paperS) (hu : FLatticePaper.Tiles.Standard.IsBase u) (hd : d = Digit.one ∨ d = Digit.three)
    (hm : 1 ≤ m) (_hex : ¬ (d = Digit.three ∧ m = 1 ∧ ∀ x ∈ u, x = Digit.three))
    (hw : w = u ++ [d] ++ List.replicate m Digit.two)
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f w.length) :
    PairCompat (FLatticePaper.Tiles.GlueFull.oddFull f w) 3 4 ∧
      PairCompat (FLatticePaper.Tiles.GlueFull.oddFull f w) 2 5 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  subst hw
  rcases FLatticePaper.Tiles.SwapBaseInputAssembly.base_cases hu with h | ⟨a, -, h⟩ | ⟨b, hb, h⟩
  · subst h
    rcases hd with rfl | rfl
    · exact v2_three_one D hS f 0 m' hG
    · exact v2_three_three D hS f 0 m' hG
  · subst h
    rcases hd with rfl | rfl
    · exact v2_three_one D hS f a m' hG
    · exact v2_three_three D hS f a m' hG
  · subst h
    rcases hd with rfl | rfl
    · exact v2_two_one D hS f b m' hb hG
    · exact v2_two_three D hS f b m' hb hG

/-! ### V7: the vacuous family `u d 3^m` (`u` base, `d ∈ {one, two}`, `m ≥ 1`), the even pairs (0,3), (1,2) on the odd tile of `u` -/

/-- The first register is unchanged by the letters `three`. -/
theorem regs_three_fst (x : Word) (j : ℕ) : (regsAt (x ++ List.replicate j Digit.three)).1 = (regsAt x).1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ', ← List.append_assoc, WeakStepPaper.regsAt_snoc, ← ih]
    simp [regStep]

/-- The second register after `x 3^(j+1)` is the prefix `x 3^j`. -/
theorem regs_three_snd_succ (x : Word) (j : ℕ) :
    (regsAt (x ++ List.replicate (j + 1) Digit.three)).2 = some (x ++ List.replicate j Digit.three) := by
  rw [List.replicate_succ', ← List.append_assoc, WeakStepPaper.regsAt_snoc]
  simp [regStep]

/-- The first register of `u d` (`d ∈ {one, two}`) is `u`. -/
theorem regs_fst_one_two (u : Word) (d : Digit) (hd : d = Digit.one ∨ d = Digit.two) :
    (regsAt (u ++ [d])).1 = some u := by
  rw [WeakStepPaper.regsAt_snoc]
  rcases hd with rfl | rfl
  · simp [regStep]
  · simp [regStep]

theorem walk_three_iter (P : Parents) (m : ℕ) :
    P.walk (List.replicate m Digit.three) =
      ⟨P.odd, ⟨P.even.num + 2 * (m : ℤ) * P.odd.num, P.even.den + 2 * (m : ℤ) * P.odd.den⟩⟩ := by
  induction m with
  | zero => cases P; simp [Parents.walk]
  | succ m ih =>
    rw [List.replicate_succ', Parents.walk_append, ih]
    simp only [Parents.walk, List.foldl, Parents.step, Parents.current, Parents.combine]
    simp only [Nat.cast_succ]
    congr 2 <;> ring

theorem parentsAt_append_rep_three (X : Word) (m : ℕ) :
    parentsAt (X ++ List.replicate m Digit.three) = (parentsAt X).walk (List.replicate m Digit.three) := by
  unfold parentsAt
  rw [Parents.walk_append]

theorem getLast_v7 (u : Word) (d : Digit) (m : ℕ) :
    (u ++ [d] ++ List.replicate (m + 1) Digit.three).getLast? = some Digit.three := by
  rw [List.replicate_succ', ← List.append_assoc, List.getLast?_append]
  simp

theorem not_isBase_v7 (u : Word) (d : Digit) (m : ℕ) (hd : d = Digit.one ∨ d = Digit.two) :
    ¬ IsBase (u ++ [d] ++ List.replicate (m + 1) Digit.three) := by
  rintro (h | h | h)
  · simp at h
  · have := h d (by simp)
    rcases hd with rfl | rfl <;> exact absurd this (by decide)
  · have := h Digit.three (by simp)
    exact absurd this (by decide)

theorem parents_three_one7 (a m : ℕ) :
    parentsAt (List.replicate a Digit.three ++ [Digit.one] ++ List.replicate m Digit.three) =
      ⟨⟨1, 2 * (a : ℤ) + 2⟩, ⟨1 + 2 * (m : ℤ), 2 * (a : ℤ) + 3 + 2 * (m : ℤ) * (2 * (a : ℤ) + 2)⟩⟩ := by
  have hX : parentsAt (List.replicate a Digit.three ++ [Digit.one]) = ⟨⟨1, 2 * (a : ℤ) + 2⟩, ⟨1, 2 * (a : ℤ) + 3⟩⟩ := by
    rw [parentsAt_append_singleton, FLatticePaper.Tiles.BaseTileProps.parents_three]
    simp only [Parents.step, Parents.current, Parents.combine]
    congr 2 <;> ring
  rw [parentsAt_append_rep_three, hX, walk_three_iter]
  congr 2; ring

theorem parents_three_two7 (a m : ℕ) :
    parentsAt (List.replicate a Digit.three ++ [Digit.two] ++ List.replicate m Digit.three) =
      ⟨⟨1, 2 * (a : ℤ) + 2⟩, ⟨1 + 2 * (m : ℤ), 2 * (a : ℤ) + 1 + 2 * (m : ℤ) * (2 * (a : ℤ) + 2)⟩⟩ := by
  have hX : parentsAt (List.replicate a Digit.three ++ [Digit.two]) = ⟨⟨1, 2 * (a : ℤ) + 2⟩, ⟨1, 2 * (a : ℤ) + 1⟩⟩ := by
    rw [parentsAt_append_singleton, FLatticePaper.Tiles.BaseTileProps.parents_three]
    simp only [Parents.step, Parents.current, Parents.combine]
    congr 2; ring
  rw [parentsAt_append_rep_three, hX, walk_three_iter]
  congr 2; ring

theorem parents_two_one7 (b m : ℕ) :
    parentsAt (List.replicate b Digit.two ++ [Digit.one] ++ List.replicate m Digit.three) =
      ⟨⟨(b : ℤ) + 1, (b : ℤ) + 2⟩, ⟨2 * (b : ℤ) + 1 + 2 * (m : ℤ) * ((b : ℤ) + 1), 2 * (b : ℤ) + 3 + 2 * (m : ℤ) * ((b : ℤ) + 2)⟩⟩ := by
  have hX : parentsAt (List.replicate b Digit.two ++ [Digit.one]) =
      ⟨⟨(b : ℤ) + 1, (b : ℤ) + 2⟩, ⟨2 * (b : ℤ) + 1, 2 * (b : ℤ) + 3⟩⟩ := by
    rw [parentsAt_append_singleton, FLatticePaper.Tiles.BaseTileProps.parents_two]
    simp only [Parents.step, Parents.current, Parents.combine]
    congr 2 <;> ring
  rw [parentsAt_append_rep_three, hX, walk_three_iter]

theorem parents_two_two7 (b m : ℕ) :
    parentsAt (List.replicate b Digit.two ++ [Digit.two] ++ List.replicate m Digit.three) =
      ⟨⟨(b : ℤ) + 1, (b : ℤ) + 2⟩, ⟨1 + 2 * (m : ℤ) * ((b : ℤ) + 1), 1 + 2 * (m : ℤ) * ((b : ℤ) + 2)⟩⟩ := by
  have hX : parentsAt (List.replicate b Digit.two ++ [Digit.two]) = ⟨⟨(b : ℤ) + 1, (b : ℤ) + 2⟩, ⟨1, 1⟩⟩ := by
    rw [parentsAt_append_singleton, FLatticePaper.Tiles.BaseTileProps.parents_two]
    simp only [Parents.step, Parents.current, Parents.combine]
    congr 2 <;> ring
  rw [parentsAt_append_rep_three, hX, walk_three_iter]

theorem phase_three_one7 (a m : ℕ) :
    W1Odd (List.replicate a Digit.three ++ [Digit.one] ++ List.replicate m Digit.three) = true := by
  simp [W1Odd, phase, List.count_append, List.count_replicate]

theorem phase_three_two7 (a m : ℕ) :
    W1Odd (List.replicate a Digit.three ++ [Digit.two] ++ List.replicate m Digit.three) = false := by
  simp [W1Odd, phase, List.count_append, List.count_replicate]

theorem phase_two_one7 (b m : ℕ) :
    W1Odd (List.replicate b Digit.two ++ [Digit.one] ++ List.replicate m Digit.three) = true := by
  simp [W1Odd, phase, List.count_append, List.count_replicate]

theorem phase_two_two7 (b m : ℕ) :
    W1Odd (List.replicate b Digit.two ++ [Digit.two] ++ List.replicate m Digit.three) = false := by
  simp [W1Odd, phase, List.count_append, List.count_replicate]

/-- The odd tile `ladderF d` (`d ≥ 2`) lies in the box `[-d+2, 2d] × [0, d+2]`. -/
theorem ladderF_box (d : ℤ) (hd : 2 ≤ d) :
    ∀ z ∈ ladderF d, -d + 2 ≤ z.1 ∧ z.1 ≤ 2 * d ∧ 0 ≤ z.2 ∧ z.2 ≤ d + 2 := by
  intro z hz
  obtain ⟨z1, z2⟩ := z
  rw [mem_ladderF_iff_paper hd, SwapRegions.ladder_tile_mem] at hz
  omega

/-- The odd tile `nstairN d` (`d ≥ 2`) lies in the box `[0, d+1] × [0, 2d-2]`. -/
theorem nstairN_box (d : ℤ) (hd : 2 ≤ d) :
    ∀ z ∈ nstairN d, 0 ≤ z.1 ∧ z.1 ≤ d + 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 2 * d - 2 := by
  intro z hz
  obtain ⟨z1, z2⟩ := z
  rw [mem_nstairN_iff_paper hd] at hz
  simp only [paperNearStairTile, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.ext_iff] at hz
  omega

/-- The glue of V7: the pieces 0,3 and 1,2 of the even child of `w = u d 3^(m+1)` are the odometer `(f u).tOdd` at the offsets
`offE w i`; they are compatible when the offsets are separated with respect to the odd tile of `u`. -/
theorem v7_glue (D : JointData) (_hS : D.S = paperS) (f : Word → JSlice) (u : Word) (d : Digit) (m : ℕ)
    (w : Word) (hd : d = Digit.one ∨ d = Digit.two) (hw : w = u ++ [d] ++ List.replicate (m + 1) Digit.three)
    (_hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f w.length)
    (lx hx ly hy : ℤ)
    (hbox : ∀ z ∈ (f u).tOdd.dom, lx ≤ z.1 ∧ z.1 ≤ hx ∧ ly ≤ z.2 ∧ z.2 ≤ hy)
    (h03 : (FLatticePaper.Tiles.GlueFull.offE w 3).1 - (FLatticePaper.Tiles.GlueFull.offE w 0).1 < lx - hx ∨
      hx - lx < (FLatticePaper.Tiles.GlueFull.offE w 3).1 - (FLatticePaper.Tiles.GlueFull.offE w 0).1 ∨
      (FLatticePaper.Tiles.GlueFull.offE w 3).2 - (FLatticePaper.Tiles.GlueFull.offE w 0).2 < ly - hy ∨
      hy - ly < (FLatticePaper.Tiles.GlueFull.offE w 3).2 - (FLatticePaper.Tiles.GlueFull.offE w 0).2)
    (h12 : (FLatticePaper.Tiles.GlueFull.offE w 2).1 - (FLatticePaper.Tiles.GlueFull.offE w 1).1 < lx - hx ∨
      hx - lx < (FLatticePaper.Tiles.GlueFull.offE w 2).1 - (FLatticePaper.Tiles.GlueFull.offE w 1).1 ∨
      (FLatticePaper.Tiles.GlueFull.offE w 2).2 - (FLatticePaper.Tiles.GlueFull.offE w 1).2 < ly - hy ∨
      hy - ly < (FLatticePaper.Tiles.GlueFull.offE w 2).2 - (FLatticePaper.Tiles.GlueFull.offE w 1).2) :
    PairCompat (FLatticePaper.Tiles.GlueFull.evenFull f w) 0 3 ∧
      PairCompat (FLatticePaper.Tiles.GlueFull.evenFull f w) 1 2 := by
  have hreg : regsAt w = (some u, some (u ++ [d] ++ List.replicate m Digit.three)) := by
    apply Prod.ext
    · show (regsAt w).1 = some u
      rw [hw, regs_three_fst]
      exact regs_fst_one_two u d hd
    · show (regsAt w).2 = some (u ++ [d] ++ List.replicate m Digit.three)
      rw [hw]
      exact regs_three_snd_succ (u ++ [d]) m
  have hnb : ¬ IsBase w := by
    rw [hw]
    exact not_isBase_v7 u d m hd
  have hc : ¬ CorrectedAfterTwo w := by
    rintro ⟨-, h⟩
    rw [hw, getLast_v7] at h
    cases h
  have hl1 : u.length < w.length := by
    rw [hw]; simp
  have hl2 : (u ++ [d] ++ List.replicate m Digit.three).length < w.length := by
    rw [hw]; simp
  have e0 := FLatticePaper.Tiles.GlueFull.evenFull_get f w u (u ++ [d] ++ List.replicate m Digit.three) hnb hreg hc
    hl1 hl2 0 (by norm_num)
  have e1 := FLatticePaper.Tiles.GlueFull.evenFull_get f w u (u ++ [d] ++ List.replicate m Digit.three) hnb hreg hc
    hl1 hl2 1 (by norm_num)
  have e2 := FLatticePaper.Tiles.GlueFull.evenFull_get f w u (u ++ [d] ++ List.replicate m Digit.three) hnb hreg hc
    hl1 hl2 2 (by norm_num)
  have e3 := FLatticePaper.Tiles.GlueFull.evenFull_get f w u (u ++ [d] ++ List.replicate m Digit.three) hnb hreg hc
    hl1 hl2 3 (by norm_num)
  have hp0 : (FLatticePaper.Tiles.GlueFull.evenFull f w)[0]? = some (stdPiece (f u).tOdd
      (FLatticePaper.Tiles.GlueFull.offE w 0)
      (FLatticePaper.Tiles.ClosedPathAssembly.affEven (parentsAt w).odd (parentsAt w).even 0)) := by
    rw [e0, if_pos (show (0 : ℕ) < 4 by norm_num)]
  have hp1 : (FLatticePaper.Tiles.GlueFull.evenFull f w)[1]? = some (stdPiece (f u).tOdd
      (FLatticePaper.Tiles.GlueFull.offE w 1)
      (FLatticePaper.Tiles.ClosedPathAssembly.affEven (parentsAt w).odd (parentsAt w).even 1)) := by
    rw [e1, if_pos (show (1 : ℕ) < 4 by norm_num)]
  have hp2 : (FLatticePaper.Tiles.GlueFull.evenFull f w)[2]? = some (stdPiece (f u).tOdd
      (FLatticePaper.Tiles.GlueFull.offE w 2)
      (FLatticePaper.Tiles.ClosedPathAssembly.affEven (parentsAt w).odd (parentsAt w).even 2)) := by
    rw [e2, if_pos (show (2 : ℕ) < 4 by norm_num)]
  have hp3 : (FLatticePaper.Tiles.GlueFull.evenFull f w)[3]? = some (stdPiece (f u).tOdd
      (FLatticePaper.Tiles.GlueFull.offE w 3)
      (FLatticePaper.Tiles.ClosedPathAssembly.affEven (parentsAt w).odd (parentsAt w).even 3)) := by
    rw [e3, if_pos (show (3 : ℕ) < 4 by norm_num)]
  exact ⟨FLatticePaper.Tiles.SwapBaseClauses.pairCompat_of_disjoint _ 0 3 _ _ _ _ _ hp0 hp3
      (disjoint_of_box _ lx hx ly hy hbox _ _ h03),
    FLatticePaper.Tiles.SwapBaseClauses.pairCompat_of_disjoint _ 1 2 _ _ _ _ _ hp1 hp2
      (disjoint_of_box _ lx hx ly hy hbox _ _ h12)⟩


/-- V7 for the odd base `3^a` (`a ≥ 1`), `d = one`. -/
theorem v7_three_one (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (a m : ℕ) (ha : 1 ≤ a)
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f
      (List.replicate a Digit.three ++ [Digit.one] ++ List.replicate (m + 1) Digit.three).length) :
    PairCompat (FLatticePaper.Tiles.GlueFull.evenFull f (List.replicate a Digit.three ++ [Digit.one] ++
        List.replicate (m + 1) Digit.three)) 0 3 ∧
      PairCompat (FLatticePaper.Tiles.GlueFull.evenFull f (List.replicate a Digit.three ++ [Digit.one] ++
        List.replicate (m + 1) Digit.three)) 1 2 := by
  have hl : (List.replicate a Digit.three).length <
      (List.replicate a Digit.three ++ [Digit.one] ++ List.replicate (m + 1) Digit.three).length := by simp
  have hO := FLatticePaper.Tiles.SwapBaseTiles.base_tiles_paper D hS f _ hG _ hl
    (Or.inr (Or.inl fun d hd => List.eq_of_mem_replicate hd))
  obtain ⟨hOd, -, -, -⟩ := hO.2.1 a ha rfl
  have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
  have ha' : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
  have ha1 : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
  refine v7_glue D hS f (List.replicate a Digit.three) Digit.one (m + 0) _ (Or.inl rfl) rfl hG
    (-(2 * (a : ℤ) + 2) + 2) (2 * (2 * (a : ℤ) + 2)) 0 (2 * (a : ℤ) + 2 + 2) ?_ ?_ ?_
  · intro z hz
    rw [hOd] at hz
    exact ladderF_box _ (by omega) z hz
  · right; right; right
    simp only [FLatticePaper.Tiles.SwapOffsets.offE_3, FLatticePaper.Tiles.SwapOffsets.offE_0,
      phase_three_one7, parents_three_one7, if_true]
    simp [texV1Even, texV2]
    nlinarith [mul_nonneg hm ha', mul_nonneg hm (show (0 : ℤ) ≤ 4 * (a : ℤ) + 8 by positivity)]
  · right; right; right
    simp only [FLatticePaper.Tiles.SwapOffsets.offE_2, FLatticePaper.Tiles.SwapOffsets.offE_1,
      phase_three_one7, parents_three_one7, if_true]
    simp [texV1Even, texV2]
    nlinarith [mul_nonneg hm ha', mul_nonneg hm (show (0 : ℤ) ≤ 4 * (a : ℤ) + 8 by positivity)]

/-- V7 for the odd base `3^a` (`a ≥ 1`), `d = two`. -/
theorem v7_three_two (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (a m : ℕ) (ha : 1 ≤ a)
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f
      (List.replicate a Digit.three ++ [Digit.two] ++ List.replicate (m + 1) Digit.three).length) :
    PairCompat (FLatticePaper.Tiles.GlueFull.evenFull f (List.replicate a Digit.three ++ [Digit.two] ++
        List.replicate (m + 1) Digit.three)) 0 3 ∧
      PairCompat (FLatticePaper.Tiles.GlueFull.evenFull f (List.replicate a Digit.three ++ [Digit.two] ++
        List.replicate (m + 1) Digit.three)) 1 2 := by
  have hl : (List.replicate a Digit.three).length <
      (List.replicate a Digit.three ++ [Digit.two] ++ List.replicate (m + 1) Digit.three).length := by simp
  have hO := FLatticePaper.Tiles.SwapBaseTiles.base_tiles_paper D hS f _ hG _ hl
    (Or.inr (Or.inl fun d hd => List.eq_of_mem_replicate hd))
  obtain ⟨hOd, -, -, -⟩ := hO.2.1 a ha rfl
  have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
  have ha' : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
  have ha1 : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
  refine v7_glue D hS f (List.replicate a Digit.three) Digit.two m _ (Or.inr rfl) rfl hG
    (-(2 * (a : ℤ) + 2) + 2) (2 * (2 * (a : ℤ) + 2)) 0 (2 * (a : ℤ) + 2 + 2) ?_ ?_ ?_
  · intro z hz
    rw [hOd] at hz
    exact ladderF_box _ (by omega) z hz
  · right; right; right
    simp only [FLatticePaper.Tiles.SwapOffsets.offE_3, FLatticePaper.Tiles.SwapOffsets.offE_0,
      phase_three_two7, parents_three_two7, Bool.false_eq_true, if_false]
    simp [texV1Even, texV2]
    nlinarith [mul_nonneg hm ha', mul_nonneg hm (show (0 : ℤ) ≤ 4 * (a : ℤ) + 4 by positivity)]
  · left
    simp only [FLatticePaper.Tiles.SwapOffsets.offE_2, FLatticePaper.Tiles.SwapOffsets.offE_1,
      phase_three_two7, parents_three_two7, Bool.false_eq_true, if_false]
    simp [texV1Even, texV2]
    nlinarith [mul_nonneg hm ha', mul_nonneg hm (show (0 : ℤ) ≤ 4 * (a : ℤ) + 8 by positivity)]

/-- V7 for the even base `2^b` (`b ≥ 0`, the empty word at `b = 0`), `d = one`. -/
theorem v7_two_one (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (b m : ℕ)
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f
      (List.replicate b Digit.two ++ [Digit.one] ++ List.replicate (m + 1) Digit.three).length) :
    PairCompat (FLatticePaper.Tiles.GlueFull.evenFull f (List.replicate b Digit.two ++ [Digit.one] ++
        List.replicate (m + 1) Digit.three)) 0 3 ∧
      PairCompat (FLatticePaper.Tiles.GlueFull.evenFull f (List.replicate b Digit.two ++ [Digit.one] ++
        List.replicate (m + 1) Digit.three)) 1 2 := by
  have hl : (List.replicate b Digit.two).length <
      (List.replicate b Digit.two ++ [Digit.one] ++ List.replicate (m + 1) Digit.three).length := by simp
  have hO := FLatticePaper.Tiles.SwapNonvac.two_odd_tile D hS f _ hG b hl
  have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
  have hb : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
  refine v7_glue D hS f (List.replicate b Digit.two) Digit.one m _ (Or.inl rfl) rfl hG
    0 (2 * (b : ℤ) + 3 + 1) 0 (2 * (2 * (b : ℤ) + 3) - 2) ?_ ?_ ?_
  · intro z hz
    rw [hO.1] at hz
    exact nstairN_box _ (by omega) z hz
  · right; right; right
    simp only [FLatticePaper.Tiles.SwapOffsets.offE_3, FLatticePaper.Tiles.SwapOffsets.offE_0,
      phase_two_one7, parents_two_one7, if_true]
    simp [texV1Even, texV2]
    nlinarith [mul_nonneg hm hb, mul_nonneg hm (show (0 : ℤ) ≤ 6 * (b : ℤ) + 8 by positivity)]
  · right; right; right
    simp only [FLatticePaper.Tiles.SwapOffsets.offE_2, FLatticePaper.Tiles.SwapOffsets.offE_1,
      phase_two_one7, parents_two_one7, if_true]
    simp [texV1Even, texV2]
    nlinarith [mul_nonneg hm hb, mul_nonneg hm (show (0 : ℤ) ≤ 6 * (b : ℤ) + 8 by positivity)]

/-- V7 for the even base `2^b` (`b ≥ 0`), `d = two`. -/
theorem v7_two_two (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (b m : ℕ)
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f
      (List.replicate b Digit.two ++ [Digit.two] ++ List.replicate (m + 1) Digit.three).length) :
    PairCompat (FLatticePaper.Tiles.GlueFull.evenFull f (List.replicate b Digit.two ++ [Digit.two] ++
        List.replicate (m + 1) Digit.three)) 0 3 ∧
      PairCompat (FLatticePaper.Tiles.GlueFull.evenFull f (List.replicate b Digit.two ++ [Digit.two] ++
        List.replicate (m + 1) Digit.three)) 1 2 := by
  have hl : (List.replicate b Digit.two).length <
      (List.replicate b Digit.two ++ [Digit.two] ++ List.replicate (m + 1) Digit.three).length := by simp
  have hO := FLatticePaper.Tiles.SwapNonvac.two_odd_tile D hS f _ hG b hl
  have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
  have hb : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
  refine v7_glue D hS f (List.replicate b Digit.two) Digit.two m _ (Or.inr rfl) rfl hG
    0 (2 * (b : ℤ) + 3 + 1) 0 (2 * (2 * (b : ℤ) + 3) - 2) ?_ ?_ ?_
  · intro z hz
    rw [hO.1] at hz
    exact nstairN_box _ (by omega) z hz
  · right; right; right
    simp only [FLatticePaper.Tiles.SwapOffsets.offE_3, FLatticePaper.Tiles.SwapOffsets.offE_0,
      phase_two_two7, parents_two_two7, Bool.false_eq_true, if_false]
    simp [texV1Even, texV2]
    nlinarith [mul_nonneg hm hb, mul_nonneg hm (show (0 : ℤ) ≤ 2 * (b : ℤ) + 4 by positivity)]
  · left
    simp only [FLatticePaper.Tiles.SwapOffsets.offE_2, FLatticePaper.Tiles.SwapOffsets.offE_1,
      phase_two_two7, parents_two_two7, Bool.false_eq_true, if_false]
    simp [texV1Even, texV2]
    nlinarith [mul_nonneg hm hb, mul_nonneg hm (show (0 : ℤ) ≤ 2 * (b : ℤ) + 6 by positivity)]

/-- **V7**, the vacuous family `u d 3^m` (`u` a base word, `d ∈ {1,2}`, `m ≥ 1`). -/
theorem vac_V7 (D : JointData) (f : Word → JSlice) (u : Word) (d : Digit) (m : ℕ) (w : Word)
    (hS : D.S = paperS) (hu : FLatticePaper.Tiles.Standard.IsBase u) (hd : d = Digit.one ∨ d = Digit.two)
    (hm : 1 ≤ m) (_hex : ¬ (d = Digit.two ∧ m = 1 ∧ ∀ x ∈ u, x = Digit.two))
    (hw : w = u ++ [d] ++ List.replicate m Digit.three)
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f w.length) :
    PairCompat (FLatticePaper.Tiles.GlueFull.evenFull f w) 0 3 ∧
      PairCompat (FLatticePaper.Tiles.GlueFull.evenFull f w) 1 2 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  subst hw
  rcases FLatticePaper.Tiles.SwapBaseInputAssembly.base_cases hu with h | ⟨a, ha, h⟩ | ⟨b, hb, h⟩
  · subst h
    rcases hd with rfl | rfl
    · exact v7_two_one D hS f 0 m' hG
    · exact v7_two_two D hS f 0 m' hG
  · subst h
    rcases hd with rfl | rfl
    · exact v7_three_one D hS f a m' ha hG
    · exact v7_three_two D hS f a m' ha hG
  · subst h
    rcases hd with rfl | rfl
    · exact v7_two_one D hS f b m' hG
    · exact v7_two_two D hS f b m' hG

end FLatticePaper.Tiles.SwapVacuousV27
