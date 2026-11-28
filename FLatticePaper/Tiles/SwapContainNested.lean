import FLatticePaper.Tiles.SwapContainBox
import FLatticePaper.Tiles.AltGlueOdd

/-! # The overlap of a meeting swapped pair: the nested pair

For the odd child `0, 1` after a `2` and the even child `4, 5` after a `3`, the decomposition of the register `u` repeats the swap:
the copies `0` of the first frame and `1` of the second (resp. `4`, `5`) are `G - s` and `G + s`, where `G` is the grandparent copy
and `s` the swap vector of the register, with `s₁ + s₂` even. Their overlap lies in `G` by the midpoint convexity of the closed
form of a tile (`inH_mid`, `SiteInduction.InH`). -/

namespace FLatticePaper.Tiles.SwapContainNested

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.ChildGlue (oddP oddQ evenP evenQ)
open FLatticePaper.Tiles.SwapContainCore (tv1o_cur tv2_curO tv1e_cur tv2_curE)

/-- **Midpoint convexity of the closed form**: with `s₁ + s₂` even, `y - s` and `y + s` in `H_f` give `y` in `H_f`. -/
theorem inH_mid (f : Fraction) (y s : Site) (hs : (s.1 + s.2) % 2 = 0) (h1 : InH f (y - s)) (h2 : InH f (y + s)) :
    InH f y := by
  have e1 : decide (((y - s).1 + (y - s).2) % 2 = 0) = decide ((y.1 + y.2) % 2 = 0) := by
    simp only [Prod.fst_sub, Prod.snd_sub]
    exact decide_eq_decide.2 ⟨fun h => by omega, fun h => by omega⟩
  have e2 : decide (((y + s).1 + (y + s).2) % 2 = 0) = decide ((y.1 + y.2) % 2 = 0) := by
    simp only [Prod.fst_add, Prod.snd_add]
    exact decide_eq_decide.2 ⟨fun h => by omega, fun h => by omega⟩
  have t1 : tCo f (y - s) = tCo f y - tCo f s := by simp only [tCo, Prod.fst_sub, Prod.snd_sub]; ring
  have t2 : tCo f (y + s) = tCo f y + tCo f s := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have s1 : sCo f (y - s) = sCo f y - sCo f s := by simp only [sCo, Prod.fst_sub, Prod.snd_sub]; ring
  have s2 : sCo f (y + s) = sCo f y + sCo f s := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  obtain ⟨a1, a2, a3, a4⟩ := h1
  obtain ⟨b1, b2, b3, b4⟩ := h2
  simp only [e1, t1, s1] at a1 a2 a3 a4
  simp only [e2, t2, s2] at b1 b2 b3 b4
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- A copy of a tile at `g - s` and one at `g + s` overlap inside the copy at `g`, for a closed-form tile. -/
theorem mid_copies (T : Finset Site) (f : Fraction) (hT : ∀ x, x ∈ T ↔ InH f x) (g s : Site) (hs : (s.1 + s.2) % 2 = 0)
    {z : Site} (ha : z - (g - s) ∈ T) (hb : z - (g + s) ∈ T) : z - g ∈ T := by
  rw [hT] at ha hb ⊢
  have e1 : z - (g + s) = (z - g) - s := by abel
  have e2 : z - (g - s) = (z - g) + s := by abel
  rw [e1] at hb
  rw [e2] at ha
  exact inH_mid f _ s hs hb ha

/-- **The nested pair of the odd child after a `2`**: the overlap of the copy `0` of the first frame and the copy `1` of the
second lies in the grandparent copy `1` of the first frame. -/
theorem o01_nested (u : Word) (hu : ¬ IsBase u) (U1 : Word) (hT1 : (stateAt u).tOdd = oddTile U1) {z : Site}
    (ha : z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddP u).getD 0 0) ∈ oddTile U1)
    (hb : z - ((oddP (u ++ [Digit.two])).getD 1 0 + (oddP u).getD 1 0) ∈ oddTile U1) :
    z - ((oddP (u ++ [Digit.two])).getD 0 0 + (oddP u).getD 1 0) ∈ oddTile U1 := by
  have hW : (phase (u ++ [Digit.two]) == 1) = (phase u == 1) := JointRot.phase_snoc_two u
  have hq : (parentsAt (u ++ [Digit.two])).even = (parentsAt u).even := by rw [CeilWords.parentsAt_snoc_two]
  have hP : oddP (u ++ [Digit.two]) = oddP u := by
    unfold oddP MixedPieces.pOffsetsOdd
    rw [hW, hq]
  rw [hP] at ha hb ⊢
  have hs : (((oddP u).getD 1 0 - (oddP u).getD 0 0).1 + ((oddP u).getD 1 0 - (oddP u).getD 0 0).2) % 2 = 0 := by
    unfold oddP MixedPieces.pOffsetsOdd
    split_ifs <;> simp [texV1Even, texV2] <;> omega
  have e1 : (oddP u).getD 0 0 + (oddP u).getD 0 0 =
      ((oddP u).getD 0 0 + (oddP u).getD 1 0) - ((oddP u).getD 1 0 - (oddP u).getD 0 0) := by abel
  have e2 : (oddP u).getD 1 0 + (oddP u).getD 1 0 =
      ((oddP u).getD 0 0 + (oddP u).getD 1 0) + ((oddP u).getD 1 0 - (oddP u).getD 0 0) := by abel
  rw [e1] at ha
  rw [e2] at hb
  refine mid_copies _ (parentsAt u).odd (fun x => ?_) _ _ hs ha hb
  rw [← hT1]
  exact AltGlueOdd.mem_tOdd_iff hu x

/-- **The nested pair of the even child after a `3`**: the overlap of the copy `4` of the first frame and the copy `5` of the
second lies in the grandparent copy `5` of the first frame. -/
theorem e45_nested (u : Word) (hu : ¬ IsBase u) (U2 : Word) (hT2 : (stateAt u).tEven = evenTile U2) {z : Site}
    (ha : z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenQ u).getD 0 0) ∈ evenTile U2)
    (hb : z - ((evenQ (u ++ [Digit.three])).getD 1 0 + (evenQ u).getD 1 0) ∈ evenTile U2) :
    z - ((evenQ (u ++ [Digit.three])).getD 0 0 + (evenQ u).getD 1 0) ∈ evenTile U2 := by
  have hW : (phase (u ++ [Digit.three]) == 1) = (phase u == 1) := JointRot.phase_snoc_three u
  have hp : (parentsAt (u ++ [Digit.three])).odd = (parentsAt u).odd := by rw [CeilWords.parentsAt_snoc_three]
  have hQ : evenQ (u ++ [Digit.three]) = evenQ u := by
    unfold evenQ MixedPieces.qOffsetsEven
    rw [hW, hp]
  rw [hQ] at ha hb ⊢
  have hs : (((evenQ u).getD 1 0 - (evenQ u).getD 0 0).1 + ((evenQ u).getD 1 0 - (evenQ u).getD 0 0).2) % 2 = 0 := by
    unfold evenQ MixedPieces.qOffsetsEven
    split_ifs <;> simp [texV1Odd, texV2] <;> omega
  have e1 : (evenQ u).getD 0 0 + (evenQ u).getD 0 0 =
      ((evenQ u).getD 0 0 + (evenQ u).getD 1 0) - ((evenQ u).getD 1 0 - (evenQ u).getD 0 0) := by abel
  have e2 : (evenQ u).getD 1 0 + (evenQ u).getD 1 0 =
      ((evenQ u).getD 0 0 + (evenQ u).getD 1 0) + ((evenQ u).getD 1 0 - (evenQ u).getD 0 0) := by abel
  rw [e1] at ha
  rw [e2] at hb
  refine mid_copies _ (parentsAt u).even (fun x => ?_) _ _ hs ha hb
  rw [← hT2]
  exact AltGlueOdd.mem_tEven_iff hu x

/-! ### The midpoint pairs of a corrected register

The pairs `1, 2` of the even decomposition of the register (for the odd child `2, 5` and `3, 4` after a `1`) and `2, 5`,
`3, 4` of its odd decomposition (for the even child `1, 2` after a `1`) are the swapped pairs of the register; in the two frames
they are again `G ∓ s`. -/

/-- The midpoint form from the two relations of the offsets: `o_i + a₃ = o_j + a₀` (the grandparent copy in both frames) and
`a₁ + a₂ = a₀ + a₃` (the swapped pair of the register). -/
theorem mid_of_rel (T : Finset Site) (f : Fraction) (hT : ∀ x, x ∈ T ↔ InH f x) (oi oj a0 a1 a2 a3 : Site)
    (hF1 : oi + a3 = oj + a0) (hF2 : a1 + a2 = a0 + a3) (hs : ((a3 - a1).1 + (a3 - a1).2) % 2 = 0) {z : Site}
    (ha : z - (oi + a1) ∈ T) (hb : z - (oj + a2) ∈ T) : z - (oi + a3) ∈ T := by
  have e1 : oi + a1 = (oi + a3) - (a3 - a1) := by abel
  have e2 : oj + a2 = (oi + a3) + (a3 - a1) := by
    have : oj = oi + a3 - a0 := by rw [hF1]; abel
    rw [this]
    have h2 : a2 = a0 + a3 - a1 := by rw [← hF2]; abel
    rw [h2]; abel
  rw [e1] at ha
  rw [e2] at hb
  exact mid_copies T f hT _ _ hs ha hb

set_option hygiene false in
/-- Unfolds the offsets of the frames and of the register's copies into the vectors of the parents of `u`. -/
macro "mid_unfold" : tactic => `(tactic| (simp only [oddP, oddQ, evenP, evenQ, MixedPieces.pOffsetsOdd,
  MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, hfw, hfu, ↓reduceIte, Bool.false_eq_true,
  List.getD_cons_succ, List.getD_cons_zero, CeilWords.parentsAt_snoc_one, tv1o_cur, tv2_curO, tv1e_cur, tv2_curE]))

/-- The pair `1, 2` of the even decomposition of the register, for the copies `3, 4` of the odd child after a `1`. -/
theorem o34_mid (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U1 : Word) (hT1 : (stateAt u).tOdd = oddTile U1)
    {z : Site} (ha : z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenP u).getD 1 0) ∈ oddTile U1)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 2 0 + (evenP u).getD 2 0) ∈ oddTile U1) :
    z - ((oddQ (u ++ [Digit.one])).getD 1 0 + (evenP u).getD 3 0) ∈ oddTile U1 := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  refine mid_of_rel _ (parentsAt u).odd (fun x => by rw [← hT1]; exact AltGlueOdd.mem_tOdd_iff hu x) _ _
    ((evenP u).getD 0 0) _ _ _ ?_ ?_ ?_ ha hb
  · mid_unfold; abel
  · mid_unfold; abel
  · have hq : ((parentsAt u).even.num + (parentsAt u).even.den) % 2 = 0 := (parentsAt_valid u).even_parity
    mid_unfold; simp only [texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega

/-- The pair `1, 2` of the even decomposition of the register, for the copies `2, 5` of the odd child after a `1`. -/
theorem o25_mid (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U1 : Word) (hT1 : (stateAt u).tOdd = oddTile U1)
    {z : Site} (ha : z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenP u).getD 1 0) ∈ oddTile U1)
    (hb : z - ((oddQ (u ++ [Digit.one])).getD 3 0 + (evenP u).getD 2 0) ∈ oddTile U1) :
    z - ((oddQ (u ++ [Digit.one])).getD 0 0 + (evenP u).getD 3 0) ∈ oddTile U1 := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  refine mid_of_rel _ (parentsAt u).odd (fun x => by rw [← hT1]; exact AltGlueOdd.mem_tOdd_iff hu x) _ _
    ((evenP u).getD 0 0) _ _ _ ?_ ?_ ?_ ha hb
  · mid_unfold; abel
  · mid_unfold; abel
  · have hq : ((parentsAt u).even.num + (parentsAt u).even.den) % 2 = 0 := (parentsAt_valid u).even_parity
    mid_unfold; simp only [texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega

/-- The pair `2, 5` of the odd decomposition of the register, for the copies `1, 2` of the even child after a `1`. -/
theorem e12_mid_of (u : Word) (hu : ¬ IsBase u) (hph : phase u = 1) (U2 : Word) (hT2 : (stateAt u).tEven = evenTile U2)
    {z : Site} (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 0 0) ∈ evenTile U2)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 3 0) ∈ evenTile U2) :
    z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 2 0) ∈ evenTile U2 := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = false := by rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = true := by simp [hph]
  refine mid_of_rel _ (parentsAt u).even (fun x => by rw [← hT2]; exact AltGlueOdd.mem_tEven_iff hu x) _ _
    ((oddQ u).getD 1 0) _ _ _ ?_ ?_ ?_ ha hb
  · mid_unfold; abel
  · mid_unfold; abel
  · mid_unfold; simp only [texV1Odd, texV2, Prod.fst_sub, Prod.snd_sub]; omega

/-- The pair `3, 4` of the odd decomposition of the register, for the copies `1, 2` of the even child after a `1`. -/
theorem e12_mid_ef (u : Word) (hu : ¬ IsBase u) (hph : phase u ≠ 1) (U2 : Word) (hT2 : (stateAt u).tEven = evenTile U2)
    {z : Site} (ha : z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 1 0) ∈ evenTile U2)
    (hb : z - ((evenP (u ++ [Digit.one])).getD 2 0 + (oddQ u).getD 2 0) ∈ evenTile U2) :
    z - ((evenP (u ++ [Digit.one])).getD 1 0 + (oddQ u).getD 3 0) ∈ evenTile U2 := by
  have hfw : (phase (u ++ [Digit.one]) == 1) = true := by rw [JointRot.phase_snoc_one]; simp [hph]
  have hfu : (phase u == 1) = false := by simp [hph]
  refine mid_of_rel _ (parentsAt u).even (fun x => by rw [← hT2]; exact AltGlueOdd.mem_tEven_iff hu x) _ _
    ((oddQ u).getD 0 0) _ _ _ ?_ ?_ ?_ ha hb
  · mid_unfold; abel
  · mid_unfold; abel
  · mid_unfold; simp only [texV1Odd, texV2, texV1Even, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega

end FLatticePaper.Tiles.SwapContainNested
