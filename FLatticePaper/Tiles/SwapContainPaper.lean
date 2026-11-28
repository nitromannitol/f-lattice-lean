import FLatticePaper.Tiles.SwapContainMain
import FLatticePaper.Tiles.SwapDisjoint
import FLatticePaper.Tiles.SameParentAlt

/-! # The overlap of a meeting swapped pair (text, lines 4545-4561): `GlueFull.SwapContainInput`

For a swapped pair of copies of one parent in the standard decomposition of a child `w` that is not corrected, and a register
`u` that is not a base word: when the two copies meet, `w = u d` with `d` the letter of the class (odd `0, 1` after a `2`; odd
`2, 5`, `3, 4` and even `1, 2` after a `1`, with the phase that `SwapDisjoint` leaves open; even `4, 5` after a `3`), and the
overlap lies in the copy `X` of the decomposition of `u` in the first frame (`SwapContainMain`), which is the copy `Y` in the second
frame: `off_i + off_X = off_j + off_Y`, with the same total affine factor. In all other cases the two copies do not meet
(`SwapDisjoint`). The entries `X`, `Y` are standard copies of one parent of `u` even when `u` is corrected. -/

namespace FLatticePaper.Tiles.SwapContainPaper

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SwapContainCore
open FLatticePaper.Tiles.JointFamily (JSlice JointData Piece stdPiece below W1Odd CorrectedAfterThree CorrectedAfterTwo
  tileOddPieces tileEvenPieces)
open FLatticePaper.Tiles.ChildGlue (oddP oddQ evenP evenQ)
open FLatticePaper.Tiles.JointInduction (GoodBelow)
open FLatticePaper.Tiles.WeakStepPaper (paperS)
open FLatticePaper.Tiles.SurgicalWeak (regsAt regOdo regStep)
open FLatticePaper.Tiles.GlueFull (SwapData decO decE oddFull evenFull offO offE)
open FLatticePaper.Tiles.ClosedPathAssembly (affOdd affEven)

/-! ### The data of a register -/

/-- A word that is not a base word ends in a letter. -/
theorem snoc_cases (w : Word) (hw : ¬ IsBase w) : ∃ (v : Word) (d : Digit), w = v ++ [d] := by
  cases h : w.getLast? with
  | none => exact absurd (Or.inl (List.getLast?_eq_none_iff.1 h)) hw
  | some d => exact ⟨w.dropLast, d, SameParentAlt.eq_snoc_of_getLast w d h⟩

/-- After a `1`, `W_1` changes parity. -/
theorem phase_one_flip (v : Word) : phase (v ++ [Digit.one]) = 1 ↔ ¬ phase v = 1 := by
  have h := JointRot.phase_snoc_one v
  constructor
  · intro h1 h2
    rw [beq_iff_eq.2 h1, beq_iff_eq.2 h2] at h
    exact absurd h (by decide)
  · intro h1
    have e : (phase v == 1) = false := by simpa using h1
    rw [e] at h
    simpa using h

/-- The registers of the child `w`, their tile fractions and the domains of their tile odometers. -/
theorem frame_facts (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (w u1 u2 : Word)
    (hgood : GoodBelow D f w.length) (hreg : regsAt w = (some u1, some u2)) :
    u1.length < w.length ∧ u2.length < w.length ∧ curO u1 = (parentsAt w).odd ∧ curE u2 = (parentsAt w).even ∧
      (f u1).tOdd.dom = oddTile u1 ∧ (f u2).tEven.dom = evenTile u2 := by
  have hl1 : u1.length < w.length := JointInduction.regsAt_lt w u1 (Or.inl (by rw [hreg]))
  have hl2 : u2.length < w.length := JointInduction.regsAt_lt w u2 (Or.inr (by rw [hreg]))
  obtain ⟨hS1, -⟩ := hgood u1 hl1
  obtain ⟨hS2, -⟩ := hgood u2 hl2
  exact ⟨hl1, hl2, ((WeakStepAssembly.regsAt_parents w).1 u1 (by rw [hreg])).symm,
    ((WeakStepAssembly.regsAt_parents w).2 u2 (by rw [hreg])).symm,
    by rw [(WeakStepAssembly.slice_domains D f u1 hS1).1, hS]; rfl,
    by rw [(WeakStepAssembly.slice_domains D f u2 hS2).2, hS]; rfl⟩

/-- The registers of a register word `u` that is not a base word, with the tiles of `u` and the domains of their odometers. -/
theorem reg_facts (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (n : ℕ) (hgood : GoodBelow D f n) (u : Word)
    (hu : ¬ IsBase u) (hn : u.length < n) :
    ∃ U1 U2 : Word, regsAt u = (some U1, some U2) ∧ (stateAt u).tOdd = oddTile U1 ∧ (stateAt u).tEven = evenTile U2 ∧
      curO U1 = (parentsAt u).odd ∧ curE U2 = (parentsAt u).even ∧ (f U1).tOdd.dom = oddTile U1 ∧
      (f U2).tEven.dom = evenTile U2 ∧ U1.length < u.length ∧ U2.length < u.length := by
  obtain ⟨U1, U2, hreg⟩ := WeakStepAssembly.regsAt_nonbase u hu
  have hl1 : U1.length < u.length := JointInduction.regsAt_lt u U1 (Or.inl (by rw [hreg]))
  have hl2 : U2.length < u.length := JointInduction.regsAt_lt u U2 (Or.inr (by rw [hreg]))
  obtain ⟨hS1, -⟩ := hgood U1 (by omega)
  obtain ⟨hS2, -⟩ := hgood U2 (by omega)
  exact ⟨U1, U2, hreg, (WeakStepPaper.regsAt_tiles u).1 U1 (by rw [hreg]),
    (WeakStepPaper.regsAt_tiles u).2.2.1 U2 (by rw [hreg]),
    ((WeakStepAssembly.regsAt_parents u).1 U1 (by rw [hreg])).symm,
    ((WeakStepAssembly.regsAt_parents u).2 U2 (by rw [hreg])).symm,
    by rw [(WeakStepAssembly.slice_domains D f U1 hS1).1, hS]; rfl,
    by rw [(WeakStepAssembly.slice_domains D f U2 hS2).2, hS]; rfl, hl1, hl2⟩

/-- Membership in a placed standard piece. -/
theorem memF {o : PartialOdometer} {T : Finset Site} (hT : o.dom = T) {off aff z : Site} :
    z ∈ (stdPiece o off aff).placed ↔ z - off ∈ T := by
  rw [GlueFull.mem_placed_std, hT]

/-- The entries of the odd decomposition of a register `u` used as the copies `X`, `Y`: the two copies of the odd parent, and
the copies `2, 5` (`W_1` even) or `3, 4` (`W_1` odd) of the even parent, which are standard copies also after a `3`. -/
theorem decO_get (D : JointData) (f : Word → JSlice) (u U1 U2 : Word) (hreg : regsAt u = (some U1, some U2))
    (hl1 : U1.length < u.length) (hl2 : U2.length < u.length) :
    (decO D f u)[0]? = some (stdPiece (f U1).tOdd (offO u 0) (affOdd (parentsAt u).odd (parentsAt u).even 0)) ∧
      (decO D f u)[1]? = some (stdPiece (f U1).tOdd (offO u 1) (affOdd (parentsAt u).odd (parentsAt u).even 1)) ∧
      (W1Odd u = false →
        (decO D f u)[2]? = some (stdPiece (f U2).tEven (offO u 2) (affOdd (parentsAt u).odd (parentsAt u).even 2)) ∧
        (decO D f u)[5]? = some (stdPiece (f U2).tEven (offO u 5) (affOdd (parentsAt u).odd (parentsAt u).even 5))) ∧
      (W1Odd u = true →
        (decO D f u)[3]? = some (stdPiece (f U2).tEven (offO u 3) (affOdd (parentsAt u).odd (parentsAt u).even 3)) ∧
        (decO D f u)[4]? = some (stdPiece (f U2).tEven (offO u 4) (affOdd (parentsAt u).odd (parentsAt u).even 4))) := by
  have hb1 : below f u U1 = f U1 := by simp only [below, if_pos hl1]
  have hb2 : below f u U2 = f U2 := by simp only [below, if_pos hl2]
  obtain ⟨o0, o1, o2, o3, o4, o5⟩ := GlueFull.offO_eq u
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := GlueFull.affO_eq u
  rw [← o0, ← o1, ← o2, ← o3, ← o4, ← o5, ← a0, ← a1, ← a2, ← a3, ← a4, ← a5]
  refine ⟨?_, ?_, fun ho => ⟨?_, ?_⟩, fun ho => ⟨?_, ?_⟩⟩
  · simp [decO, tileOddPieces, hreg, regOdo, hb1, hb2]
  · simp [decO, tileOddPieces, hreg, regOdo, hb1, hb2]
  all_goals simp [decO, tileOddPieces, hreg, regOdo, hb1, hb2, ho]

/-- The entries of the even decomposition of a register `u` used as the copies `X`, `Y`: the copies `0, 3` of the odd parent and
the two copies of the even parent, which are standard copies also after a `2`. -/
theorem decE_get (D : JointData) (f : Word → JSlice) (u U1 U2 : Word) (hreg : regsAt u = (some U1, some U2))
    (hl1 : U1.length < u.length) (hl2 : U2.length < u.length) :
    (decE D f u)[0]? = some (stdPiece (f U1).tOdd (offE u 0) (affEven (parentsAt u).odd (parentsAt u).even 0)) ∧
      (decE D f u)[3]? = some (stdPiece (f U1).tOdd (offE u 3) (affEven (parentsAt u).odd (parentsAt u).even 3)) ∧
      (decE D f u)[4]? = some (stdPiece (f U2).tEven (offE u 4) (affEven (parentsAt u).odd (parentsAt u).even 4)) ∧
      (decE D f u)[5]? = some (stdPiece (f U2).tEven (offE u 5) (affEven (parentsAt u).odd (parentsAt u).even 5)) := by
  have hb1 : below f u U1 = f U1 := by simp only [below, if_pos hl1]
  have hb2 : below f u U2 = f U2 := by simp only [below, if_pos hl2]
  obtain ⟨o0, -, -, o3, o4, o5⟩ := GlueFull.offE_eq u
  obtain ⟨a0, -, -, a3, a4, a5⟩ := GlueFull.affE_eq u
  rw [← o0, ← o3, ← o4, ← o5, ← a0, ← a3, ← a4, ← a5]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [decE, tileEvenPieces, hreg, regOdo, hb1, hb2]

/-! ### The six swapped pairs -/

/-- **The copies `0`, `1` of the odd child**: they meet only after a `2`, and then their overlap lies in the copy `1` of the odd
decomposition of the register in the first frame, which is its copy `0` in the second. -/
theorem swap_o01 (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (w u1 u2 : Word)
    (hgood : GoodBelow D f w.length) (hw : ¬ IsBase w) (hreg : regsAt w = (some u1, some u2))
    (hc : ¬ CorrectedAfterThree w) (hb : ¬ IsBase u1) : SwapData (oddFull f w) 0 1 (decO D f u1) := by
  obtain ⟨hl1, hl2, hpw, -, hdO, -⟩ := frame_facts D hS f w u1 u2 hgood hreg
  intro p q hp hq hm
  rw [GlueFull.oddFull_get f w u1 u2 hw hreg hc hl1 hl2 0 (by norm_num)] at hp
  rw [GlueFull.oddFull_get f w u1 u2 hw hreg hc hl1 hl2 1 (by norm_num)] at hq
  cases hp; cases hq
  simp only [if_pos (show (0 : ℕ) < 2 by norm_num), if_pos (show (1 : ℕ) < 2 by norm_num)] at hm ⊢
  obtain ⟨v, d, rfl⟩ := snoc_cases w hw
  cases d with
  | one =>
    obtain ⟨z, h1, h2⟩ := hm
    rw [memF hdO] at h1 h2
    have hd : (v ++ [Digit.one]).getLast? = some Digit.one := by simp
    by_cases hph : phase (v ++ [Digit.one]) = 1
    · exact (SwapDisjoint.so01_one_of _ hw hd hph u1 hpw h1 h2).elim
    · exact (SwapDisjoint.so01_one_ef _ hw hd hph u1 hpw h1 h2).elim
  | two =>
    have hu : u1 = v := by
      rw [WeakStepPaper.regsAt_snoc] at hreg
      simp only [regStep, Prod.mk.injEq, Option.some.injEq] at hreg
      exact hreg.1.symm
    subst u1
    obtain ⟨U1, U2, hregu, hT1, hT2, hU1, hU2, hd1, -, hL1, hL2⟩ := reg_facts D hS f _ hgood v hb hl1
    obtain ⟨g0, g1, -, -⟩ := decO_get D f v U1 U2 hregu hL1 hL2
    refine ⟨1, 0, _, _, g1, g0, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · show (oddP (v ++ [Digit.two])).getD 0 0 + (oddP v).getD 1 0 = (oddP (v ++ [Digit.two])).getD 1 0 + (oddP v).getD 0 0
      have hfw : (phase (v ++ [Digit.two]) == 1) = (phase v == 1) := JointRot.phase_snoc_two v
      cases hfu : (phase v == 1) <;> rw [hfu] at hfw <;> rel_unfold <;> abel
    · ext <;> simp [stdPiece, affOdd, CeilWords.parentsAt_snoc_two]
    · intro z h1 h2
      rw [memF hdO] at h1 h2
      rw [memF hd1]
      by_cases hph : phase v = 1
      · exact SwapContainMain.contain_o01_of v hb hph U1 U2 hT1 hT2 hU1 hU2 h1 h2
      · exact SwapContainMain.contain_o01_ef v hb hph U1 U2 hT1 hT2 hU1 hU2 h1 h2
  | three => exact (hc ⟨hw, by simp⟩).elim

/-- **The copies `3`, `4` of the odd child**: they meet only after a `1` with `W_1` of the register odd, and then their overlap lies
in the copy `3` of the even decomposition of the register in the first frame, which is its copy `0` in the second. -/
theorem swap_o34 (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (w u1 u2 : Word)
    (hgood : GoodBelow D f w.length) (hw : ¬ IsBase w) (hreg : regsAt w = (some u1, some u2))
    (hc : ¬ CorrectedAfterThree w) (hb : ¬ IsBase u2) : SwapData (oddFull f w) 3 4 (decE D f u2) := by
  obtain ⟨hl1, hl2, -, hqw, -, hdE⟩ := frame_facts D hS f w u1 u2 hgood hreg
  intro p q hp hq hm
  rw [GlueFull.oddFull_get f w u1 u2 hw hreg hc hl1 hl2 3 (by norm_num)] at hp
  rw [GlueFull.oddFull_get f w u1 u2 hw hreg hc hl1 hl2 4 (by norm_num)] at hq
  cases hp; cases hq
  simp only [if_neg (show ¬ (3 : ℕ) < 2 by norm_num), if_neg (show ¬ (4 : ℕ) < 2 by norm_num)] at hm ⊢
  obtain ⟨v, d, rfl⟩ := snoc_cases w hw
  cases d with
  | one =>
    have hu : u2 = v := by
      rw [WeakStepPaper.regsAt_snoc] at hreg
      simp only [regStep, Prod.mk.injEq, Option.some.injEq] at hreg
      exact hreg.2.symm
    subst u2
    by_cases hph : phase v = 1
    · obtain ⟨U1, U2, hregu, hT1, hT2, hU1, hU2, hd1, -, hL1, hL2⟩ := reg_facts D hS f _ hgood v hb hl2
      obtain ⟨g0, g3, -, -⟩ := decE_get D f v U1 U2 hregu hL1 hL2
      refine ⟨3, 0, _, _, g3, g0, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · show (oddQ (v ++ [Digit.one])).getD 1 0 + (evenP v).getD 3 0 =
          (oddQ (v ++ [Digit.one])).getD 2 0 + (evenP v).getD 0 0
        have hfw : (phase (v ++ [Digit.one]) == 1) = false := by rw [JointRot.phase_snoc_one]; simp [hph]
        have hfu : (phase v == 1) = true := by simp [hph]
        rel_unfold; abel
      · ext
        · simp [stdPiece, affOdd, affEven, CeilWords.parentsAt_snoc_one, Parents.current, Parents.combine]
        · simp [stdPiece, affOdd, affEven, CeilWords.parentsAt_snoc_one, Parents.current, Parents.combine]; ring
      · intro z h1 h2
        rw [memF hdE] at h1 h2
        rw [memF hd1]
        exact SwapContainMain.contain_o34_of v hb hph U1 U2 hT1 hT2 hU1 hU2 h1 h2
    · obtain ⟨z, h1, h2⟩ := hm
      rw [memF hdE] at h1 h2
      exact (SwapDisjoint.so34_one_of _ hw (by simp) ((phase_one_flip v).2 hph) v hqw h1 h2).elim
  | two =>
    obtain ⟨z, h1, h2⟩ := hm
    rw [memF hdE] at h1 h2
    have hd : (v ++ [Digit.two]).getLast? = some Digit.two := by simp
    by_cases hph : phase (v ++ [Digit.two]) = 1
    · exact (SwapDisjoint.so34_two_of _ hw hd hph u2 hqw h1 h2).elim
    · exact (SwapDisjoint.so34_two_ef _ hw hd hph u2 hqw h1 h2).elim
  | three => exact (hc ⟨hw, by simp⟩).elim

/-- **The copies `2`, `5` of the odd child**: they meet only after a `1` with `W_1` of the register even, and then their overlap
lies in the copy `3` of the even decomposition of the register in the first frame, which is its copy `0` in the second. -/
theorem swap_o25 (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (w u1 u2 : Word)
    (hgood : GoodBelow D f w.length) (hw : ¬ IsBase w) (hreg : regsAt w = (some u1, some u2))
    (hc : ¬ CorrectedAfterThree w) (hb : ¬ IsBase u2) : SwapData (oddFull f w) 2 5 (decE D f u2) := by
  obtain ⟨hl1, hl2, -, hqw, -, hdE⟩ := frame_facts D hS f w u1 u2 hgood hreg
  intro p q hp hq hm
  rw [GlueFull.oddFull_get f w u1 u2 hw hreg hc hl1 hl2 2 (by norm_num)] at hp
  rw [GlueFull.oddFull_get f w u1 u2 hw hreg hc hl1 hl2 5 (by norm_num)] at hq
  cases hp; cases hq
  simp only [if_neg (show ¬ (2 : ℕ) < 2 by norm_num), if_neg (show ¬ (5 : ℕ) < 2 by norm_num)] at hm ⊢
  obtain ⟨v, d, rfl⟩ := snoc_cases w hw
  cases d with
  | one =>
    have hu : u2 = v := by
      rw [WeakStepPaper.regsAt_snoc] at hreg
      simp only [regStep, Prod.mk.injEq, Option.some.injEq] at hreg
      exact hreg.2.symm
    subst u2
    by_cases hph : phase v = 1
    · obtain ⟨z, h1, h2⟩ := hm
      rw [memF hdE] at h1 h2
      have hw1 : ¬ phase (v ++ [Digit.one]) = 1 := fun h => (phase_one_flip v).1 h hph
      exact (SwapDisjoint.so25_one_ef _ hw (by simp) hw1 v hqw h1 h2).elim
    · obtain ⟨U1, U2, hregu, hT1, hT2, hU1, hU2, hd1, -, hL1, hL2⟩ := reg_facts D hS f _ hgood v hb hl2
      obtain ⟨g0, g3, -, -⟩ := decE_get D f v U1 U2 hregu hL1 hL2
      refine ⟨3, 0, _, _, g3, g0, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · show (oddQ (v ++ [Digit.one])).getD 0 0 + (evenP v).getD 3 0 =
          (oddQ (v ++ [Digit.one])).getD 3 0 + (evenP v).getD 0 0
        have hfw : (phase (v ++ [Digit.one]) == 1) = true := by rw [JointRot.phase_snoc_one]; simp [hph]
        have hfu : (phase v == 1) = false := by simp [hph]
        rel_unfold; abel
      · ext
        · simp [stdPiece, affOdd, affEven, CeilWords.parentsAt_snoc_one, Parents.current, Parents.combine]
        · simp [stdPiece, affOdd, affEven, CeilWords.parentsAt_snoc_one, Parents.current, Parents.combine]; ring
      · intro z h1 h2
        rw [memF hdE] at h1 h2
        rw [memF hd1]
        exact SwapContainMain.contain_o25_ef v hb hph U1 U2 hT1 hT2 hU1 hU2 h1 h2
  | two =>
    obtain ⟨z, h1, h2⟩ := hm
    rw [memF hdE] at h1 h2
    have hd : (v ++ [Digit.two]).getLast? = some Digit.two := by simp
    by_cases hph : phase (v ++ [Digit.two]) = 1
    · exact (SwapDisjoint.so25_two_of _ hw hd hph u2 hqw h1 h2).elim
    · exact (SwapDisjoint.so25_two_ef _ hw hd hph u2 hqw h1 h2).elim
  | three => exact (hc ⟨hw, by simp⟩).elim

/-- **The copies `0`, `3` of the even child** never meet. -/
theorem swap_e03 (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (w u1 u2 : Word)
    (hgood : GoodBelow D f w.length) (hw : ¬ IsBase w) (hreg : regsAt w = (some u1, some u2))
    (hc : ¬ CorrectedAfterTwo w) : SwapData (evenFull f w) 0 3 (decO D f u1) := by
  obtain ⟨hl1, hl2, hpw, -, hdO, -⟩ := frame_facts D hS f w u1 u2 hgood hreg
  intro p q hp hq hm
  rw [GlueFull.evenFull_get f w u1 u2 hw hreg hc hl1 hl2 0 (by norm_num)] at hp
  rw [GlueFull.evenFull_get f w u1 u2 hw hreg hc hl1 hl2 3 (by norm_num)] at hq
  cases hp; cases hq
  simp only [if_pos (show (0 : ℕ) < 4 by norm_num), if_pos (show (3 : ℕ) < 4 by norm_num)] at hm
  obtain ⟨z, h1, h2⟩ := hm
  rw [memF hdO] at h1 h2
  exfalso
  obtain ⟨v, d, rfl⟩ := snoc_cases w hw
  cases d with
  | one =>
    by_cases hph : phase (v ++ [Digit.one]) = 1
    · exact SwapDisjoint.se03_one_of _ hw (by simp) hph u1 hpw h1 h2
    · exact SwapDisjoint.se03_one_ef _ hw (by simp) hph u1 hpw h1 h2
  | two => exact hc ⟨hw, by simp⟩
  | three =>
    by_cases hph : phase (v ++ [Digit.three]) = 1
    · exact SwapDisjoint.se03_three_of _ hw (by simp) hph u1 hpw h1 h2
    · exact SwapDisjoint.se03_three_ef _ hw (by simp) hph u1 hpw h1 h2

/-- **The copies `1`, `2` of the even child**: they meet only after a `1`, and then their overlap lies in the copy `4` (`W_1` of the
register odd) or `5` (even) of the odd decomposition of the register in the first frame, which is its copy `3` or `2` in the
second. -/
theorem swap_e12 (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (w u1 u2 : Word)
    (hgood : GoodBelow D f w.length) (hw : ¬ IsBase w) (hreg : regsAt w = (some u1, some u2))
    (hc : ¬ CorrectedAfterTwo w) (hb : ¬ IsBase u1) : SwapData (evenFull f w) 1 2 (decO D f u1) := by
  obtain ⟨hl1, hl2, hpw, -, hdO, -⟩ := frame_facts D hS f w u1 u2 hgood hreg
  intro p q hp hq hm
  rw [GlueFull.evenFull_get f w u1 u2 hw hreg hc hl1 hl2 1 (by norm_num)] at hp
  rw [GlueFull.evenFull_get f w u1 u2 hw hreg hc hl1 hl2 2 (by norm_num)] at hq
  cases hp; cases hq
  simp only [if_pos (show (1 : ℕ) < 4 by norm_num), if_pos (show (2 : ℕ) < 4 by norm_num)] at hm ⊢
  obtain ⟨v, d, rfl⟩ := snoc_cases w hw
  cases d with
  | one =>
    have hu : u1 = v := by
      rw [WeakStepPaper.regsAt_snoc] at hreg
      simp only [regStep, Prod.mk.injEq, Option.some.injEq] at hreg
      exact hreg.1.symm
    subst u1
    obtain ⟨U1, U2, hregu, hT1, hT2, hU1, hU2, -, hd2, hL1, hL2⟩ := reg_facts D hS f _ hgood v hb hl1
    obtain ⟨-, -, g25, g34⟩ := decO_get D f v U1 U2 hregu hL1 hL2
    by_cases hph : phase v = 1
    · have hfu : (phase v == 1) = true := by simp [hph]
      have hfw : (phase (v ++ [Digit.one]) == 1) = false := by rw [JointRot.phase_snoc_one]; simp [hph]
      obtain ⟨g3, g4⟩ := g34 hfu
      refine ⟨4, 3, _, _, g4, g3, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · show (evenP (v ++ [Digit.one])).getD 1 0 + (oddQ v).getD 2 0 =
          (evenP (v ++ [Digit.one])).getD 2 0 + (oddQ v).getD 1 0
        rel_unfold; abel
      · ext <;> simp [stdPiece, affOdd, affEven, CeilWords.parentsAt_snoc_one, Parents.current, Parents.combine] <;> ring
      · intro z h1 h2
        rw [memF hdO] at h1 h2
        rw [memF hd2]
        exact SwapContainMain.contain_e12_of v hb hph U1 U2 hT1 hT2 hU1 hU2 h1 h2
    · have hfu : (phase v == 1) = false := by simp [hph]
      have hfw : (phase (v ++ [Digit.one]) == 1) = true := by rw [JointRot.phase_snoc_one]; simp [hph]
      obtain ⟨g2, g5⟩ := g25 hfu
      refine ⟨5, 2, _, _, g5, g2, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · show (evenP (v ++ [Digit.one])).getD 1 0 + (oddQ v).getD 3 0 =
          (evenP (v ++ [Digit.one])).getD 2 0 + (oddQ v).getD 0 0
        rel_unfold; abel
      · ext <;> simp [stdPiece, affOdd, affEven, CeilWords.parentsAt_snoc_one, Parents.current, Parents.combine] <;> ring
      · intro z h1 h2
        rw [memF hdO] at h1 h2
        rw [memF hd2]
        exact SwapContainMain.contain_e12_ef v hb hph U1 U2 hT1 hT2 hU1 hU2 h1 h2
  | two => exact (hc ⟨hw, by simp⟩).elim
  | three =>
    obtain ⟨z, h1, h2⟩ := hm
    rw [memF hdO] at h1 h2
    by_cases hph : phase (v ++ [Digit.three]) = 1
    · exact (SwapDisjoint.se12_three_of _ hw (by simp) hph u1 hpw h1 h2).elim
    · exact (SwapDisjoint.se12_three_ef _ hw (by simp) hph u1 hpw h1 h2).elim

/-- **The copies `4`, `5` of the even child**: they meet only after a `3`, and then their overlap lies in the copy `5` of the even
decomposition of the register in the first frame, which is its copy `4` in the second. -/
theorem swap_e45 (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (w u1 u2 : Word)
    (hgood : GoodBelow D f w.length) (hw : ¬ IsBase w) (hreg : regsAt w = (some u1, some u2))
    (hc : ¬ CorrectedAfterTwo w) (hb : ¬ IsBase u2) : SwapData (evenFull f w) 4 5 (decE D f u2) := by
  obtain ⟨hl1, hl2, -, hqw, -, hdE⟩ := frame_facts D hS f w u1 u2 hgood hreg
  intro p q hp hq hm
  rw [GlueFull.evenFull_get f w u1 u2 hw hreg hc hl1 hl2 4 (by norm_num)] at hp
  rw [GlueFull.evenFull_get f w u1 u2 hw hreg hc hl1 hl2 5 (by norm_num)] at hq
  cases hp; cases hq
  simp only [if_neg (show ¬ (4 : ℕ) < 4 by norm_num), if_neg (show ¬ (5 : ℕ) < 4 by norm_num)] at hm ⊢
  obtain ⟨v, d, rfl⟩ := snoc_cases w hw
  cases d with
  | one =>
    obtain ⟨z, h1, h2⟩ := hm
    rw [memF hdE] at h1 h2
    by_cases hph : phase (v ++ [Digit.one]) = 1
    · exact (SwapDisjoint.se45_one_of _ hw (by simp) hph u2 hqw h1 h2).elim
    · exact (SwapDisjoint.se45_one_ef _ hw (by simp) hph u2 hqw h1 h2).elim
  | two => exact (hc ⟨hw, by simp⟩).elim
  | three =>
    have hu : u2 = v := by
      rw [WeakStepPaper.regsAt_snoc] at hreg
      simp only [regStep, Prod.mk.injEq, Option.some.injEq] at hreg
      exact hreg.2.symm
    subst u2
    obtain ⟨U1, U2, hregu, hT1, hT2, hU1, hU2, -, hd2, hL1, hL2⟩ := reg_facts D hS f _ hgood v hb hl2
    obtain ⟨-, -, g4, g5⟩ := decE_get D f v U1 U2 hregu hL1 hL2
    refine ⟨5, 4, _, _, g5, g4, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · show (evenQ (v ++ [Digit.three])).getD 0 0 + (evenQ v).getD 1 0 =
        (evenQ (v ++ [Digit.three])).getD 1 0 + (evenQ v).getD 0 0
      have hfw : (phase (v ++ [Digit.three]) == 1) = (phase v == 1) := JointRot.phase_snoc_three v
      cases hfu : (phase v == 1) <;> rw [hfu] at hfw <;> rel_unfold <;> abel
    · ext <;> simp [stdPiece, affEven, CeilWords.parentsAt_snoc_three]
    · intro z h1 h2
      rw [memF hdE] at h1 h2
      rw [memF hd2]
      by_cases hph : phase v = 1
      · exact SwapContainMain.contain_e45_of v hb hph U1 U2 hT1 hT2 hU1 hU2 h1 h2
      · exact SwapContainMain.contain_e45_ef v hb hph U1 U2 hT1 hT2 hU1 hU2 h1 h2

/-- **`SwapContainInput`** (text, lines 4545-4561): the overlap of a meeting swapped pair of copies of one parent lies in one copy
of the decomposition of the register, placed at the same point with the same affine factor in the two frames. -/
theorem swapContain_paper (D : JointData) : GlueFull.SwapContainInput D := by
  intro hS f w u1 u2 hgood hw hreg
  exact ⟨fun hc => ⟨fun hb => swap_o01 D hS f w u1 u2 hgood hw hreg hc hb,
      fun hb => ⟨swap_o34 D hS f w u1 u2 hgood hw hreg hc hb, swap_o25 D hS f w u1 u2 hgood hw hreg hc hb⟩⟩,
    fun hc => ⟨fun hb => ⟨swap_e03 D hS f w u1 u2 hgood hw hreg hc, swap_e12 D hS f w u1 u2 hgood hw hreg hc hb⟩,
      fun hb => swap_e45 D hS f w u1 u2 hgood hw hreg hc hb⟩⟩

end FLatticePaper.Tiles.SwapContainPaper
