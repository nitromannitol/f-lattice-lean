import FLatticePaper.Tiles.GlueBlockBounds

/-! # The block exclusions of the glued children

The sites of a block of a copy on the child's boundary strings lie in no earlier copy of the same register other than its doubled
partner (`GlueRespectsAll.BlockExclOdd`, `BlockExclEven`), at the children that Section 8 does not correct. For each pair of
copies and each block the block lies in the strip of its string in one of the coordinates `x`, `y`, `x + y`, `x - y`
(`GlueBlockBounds`), and the earlier copy lies in the box and the diagonal strip of its register (`ClosedPathExcluded`,
`ClosedPathDiagonal`); with the linear relations of the parents to the previous parents by the last digit (`last_facts`) the
two are disjoint. This fails only for the plain copies after a doubling of their register, `P^-` against `P^+` in the odd
child after a `2` and `Q^-` against `Q^+` in the even child after a `3`, and for the one word `w = 1`, where the strips of
the block and the copy overlap; these are the column inputs `ColumnExclOdd`, `ColumnExclEven`. -/

namespace FLatticePaper.Tiles.GlueBlockExcl

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.GlueRespectsAll
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)
open FLatticePaper.Tiles.SurgicalWeak (regsAt)
open FLatticePaper.Tiles.ChildGlue (oddP oddQ evenP evenQ tOddSet tEvenSet pieceSet pieceFlag dblOdd dblEven)
open FLatticePaper.Tiles.SiteInduction (shiftS)

/-- **The column input of the odd child**: after a `2` the block of `P^-` avoids `P^+`, and at `w = 1` the block of `Q^{-,2}`
avoids `Q^{+,1}`. -/
def ColumnExclOdd (w u1 u2 : Word) : Prop :=
  (w.getLast? = some Digit.two → ∀ x ∈ blockSitesOdd w u1 u2 1,
    x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 0 → False) ∧
  ((∃ d, w = [d]) → w.getLast? = some Digit.one → ∀ x ∈ blockSitesOdd w u1 u2 5,
    x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 2 → False)

/-- **The column input of the even child**: after a `3` the block of `Q^-` avoids `Q^+`. -/
def ColumnExclEven (w u1 u2 : Word) : Prop :=
  w.getLast? = some Digit.three → ∀ x ∈ blockSitesEven w u1 u2 5,
    x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 4 → False

/-- **The block exclusions of the odd child, W_1 even.** -/
theorem odd_ef_excl (w u1 u2 : Word) (hw : w ≠ []) (hph : phase w ≠ 1) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hlast : w.getLast? ≠ some Digit.three)
    (hcol : ColumnExclOdd w u1 u2) : BlockExclOdd w u1 u2 := by
  have hP := ClosedPathAssembly.oddP_ef w hph
  have hQ := ClosedPathAssembly.oddQ_ef w hph
  have pc0 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 0 = shiftS (tOddSet u1) (texV1Even (fracEven u2) + texV1Even (fracEven u2)) := by
    simp [pieceSet, hP, hq]
  have pc1 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 1 = shiftS (tOddSet u1) (texV2 (fracEven u2)) := by
    simp [pieceSet, hP, hq]
  have pc2 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 2 = shiftS (tEvenSet u2) (0) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have pc3 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 3 = shiftS (tEvenSet u2) (texV1Even (fracEven u2)) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have pc4 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 4 = shiftS (tEvenSet u2) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1)) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have pc5 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 5 = shiftS (tEvenSet u2) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV1Even (fracEven u2)) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have hpl : 0 < (fracOdd u1).num ∧ (fracOdd u1).num < (fracOdd u1).den := SiteHullOdd.curO_pos_lt u1
  have hql : 0 < (fracEven u2).num ∧ (fracEven u2).num < (fracEven u2).den := SiteHullEven.curE_pos_lt u2
  have hpo : ((fracOdd u1).num + (fracOdd u1).den) % 2 = 1 := SiteHullOdd.curO_odd u1
  have hqe : ((fracEven u2).num + (fracEven u2).den) % 2 = 0 := SiteHullEven.curE_num_add_den_even u2
  obtain ⟨p', q', f1, f2, f3, f4, f5, f6, hsmall, h1, h2, h3⟩ := GlueBlockBounds.last_facts w hw
  rw [hp, hq] at h1 h2 h3
  obtain ⟨dg, hdg⟩ : ∃ d, w.getLast? = some d := Option.ne_none_iff_exists'.1 (by simpa using hw)
  have hlin : (w.getLast? = some Digit.one ∧ ((fracOdd u1).num = p'.num + q'.num ∧ (fracOdd u1).den = p'.den + q'.den ∧ (fracEven u2).num = 2 * p'.num + q'.num ∧ (fracEven u2).den = 2 * p'.den + q'.den)) ∨
      (w.getLast? = some Digit.two ∧ ((fracOdd u1).num = p'.num + q'.num ∧ (fracOdd u1).den = p'.den + q'.den ∧ (fracEven u2).num = q'.num ∧ (fracEven u2).den = q'.den)) := by
    cases dg
    · exact Or.inl ⟨hdg, h1 hdg⟩
    · exact Or.inr ⟨hdg, h2 hdg⟩
    · exact absurd hdg hlast
  have c10 : ∀ x ∈ blockSitesOdd w u1 u2 1, x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 0 → False := by
    intro x hx0 hxj0
    have hx := hx0
    have hxj := hxj0
    simp only [blockSitesOdd, if_neg hph, List.mem_append] at hx
    rw [pc0] at hxj
    have bj := ClosedPathExcluded.box_shift_odd u1 _ x hxj
    have dj := ClosedPathDiagonal.diag_shift_odd u1 _ x hxj
    simp only [texV1Even, Prod.fst_add, Prod.snd_add] at bj dj
    rcases hx with hx | hx
    · have hb := GlueBlockBounds.top_lin _ _ (by simpa using GlueStringDecomp.hWord_ne u1 false) x hx
      rw [GlueStringDecomp.lp_top_odd] at hb
      simp only [texV1Odd, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨hl, -⟩
      · omega
      · exact hcol.1 hl x hx0 hxj0
    · have hb := GlueBlockBounds.left_lin _ _ (by simpa using GlueStringDecomp.vWord_odd_ne u1) x hx
      rw [GlueStringDecomp.lp_left_odd] at hb
      simp only [texV2, Prod.fst_add, Prod.snd_add] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨hl, -⟩
      · omega
      · exact hcol.1 hl x hx0 hxj0
  have c42 : ∀ x ∈ blockSitesOdd w u1 u2 4, x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 2 → False := by
    intro x hx0 hxj0
    have hx := hx0
    have hxj := hxj0
    simp only [blockSitesOdd, if_neg hph] at hx
    rw [pc2] at hxj
    have bj := ClosedPathExcluded.box_shift_even u2 _ x hxj
    have dj := ClosedPathDiagonal.diag_shift_even u2 _ x hxj
    simp only [Prod.fst_zero, Prod.snd_zero] at bj dj
    have hb := GlueBlockBounds.top_lin _ _ (by simpa using GlueStringDecomp.hWord_ne u2 true) x hx
    rw [GlueStringDecomp.lp_top_even] at hb
    simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
    rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
  have c52 : ∀ x ∈ blockSitesOdd w u1 u2 5, x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 2 → False := by
    intro x hx0 hxj0
    have hx := hx0
    have hxj := hxj0
    simp only [blockSitesOdd, if_neg hph, List.mem_append] at hx
    rw [pc2] at hxj
    have bj := ClosedPathExcluded.box_shift_even u2 _ x hxj
    have dj := ClosedPathDiagonal.diag_shift_even u2 _ x hxj
    simp only [Prod.fst_zero, Prod.snd_zero] at bj dj
    rcases hx with hx | hx
    · have hb := GlueBlockBounds.top_lin _ _ (by simpa using GlueStringDecomp.hWord_ne u2 true) x hx
      rw [GlueStringDecomp.lp_top_even] at hb
      simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
    · have hb := GlueBlockBounds.right_lin _ _ (GlueStringDecomp.vWord_even_ne u2) x hx
      rw [GlueStringDecomp.lp_right_even] at hb
      simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
  have c43 : ∀ x ∈ blockSitesOdd w u1 u2 4, x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 3 → False := by
    intro x hx0 hxj0
    have hx := hx0
    have hxj := hxj0
    simp only [blockSitesOdd, if_neg hph] at hx
    rw [pc3] at hxj
    have bj := ClosedPathExcluded.box_shift_even u2 _ x hxj
    have dj := ClosedPathDiagonal.diag_shift_even u2 _ x hxj
    simp only [texV1Even] at bj dj
    have hb := GlueBlockBounds.top_lin _ _ (by simpa using GlueStringDecomp.hWord_ne u2 true) x hx
    rw [GlueStringDecomp.lp_top_even] at hb
    simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
    rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
  have c53 : ∀ x ∈ blockSitesOdd w u1 u2 5, x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 3 → False := by
    intro x hx0 hxj0
    have hx := hx0
    have hxj := hxj0
    simp only [blockSitesOdd, if_neg hph, List.mem_append] at hx
    rw [pc3] at hxj
    have bj := ClosedPathExcluded.box_shift_even u2 _ x hxj
    have dj := ClosedPathDiagonal.diag_shift_even u2 _ x hxj
    simp only [texV1Even] at bj dj
    rcases hx with hx | hx
    · have hb := GlueBlockBounds.top_lin _ _ (by simpa using GlueStringDecomp.hWord_ne u2 true) x hx
      rw [GlueStringDecomp.lp_top_even] at hb
      simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
    · have hb := GlueBlockBounds.right_lin _ _ (GlueStringDecomp.vWord_even_ne u2) x hx
      rw [GlueStringDecomp.lp_right_even] at hb
      simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
  intro i j hj hi hf hd x hx hxj
  interval_cases i <;> interval_cases j <;>
    first
    | (simp [pieceFlag, ClosedPathCycle.oddP_length] at hf; done)
    | (simp [dblOdd, ClosedPathCycle.oddP_length] at hd; done)
    | exact c10 x hx hxj
    | exact c42 x hx hxj
    | exact c52 x hx hxj
    | exact c43 x hx hxj
    | exact c53 x hx hxj

/-- **The block exclusions of the odd child, W_1 odd.** -/
theorem odd_of_excl (w u1 u2 : Word) (hw : w ≠ []) (hph : phase w = 1) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hlast : w.getLast? ≠ some Digit.three)
    (hcol : ColumnExclOdd w u1 u2) : BlockExclOdd w u1 u2 := by
  have hP := ClosedPathAssembly.oddP_of w hph
  have hQ := ClosedPathAssembly.oddQ_of w hph
  have pc0 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 0 = shiftS (tOddSet u1) (0) := by
    simp [pieceSet, hP, hq, add_assoc]
  have pc1 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 1 = shiftS (tOddSet u1) (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2)) := by
    simp [pieceSet, hP, hq, add_assoc]
  have pc2 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 2 = shiftS (tEvenSet u2) (texV1Odd (fracOdd u1)) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have pc3 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 3 = shiftS (tEvenSet u2) (texV1Odd (fracOdd u1) + texV1Even (fracEven u2)) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have pc4 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 4 = shiftS (tEvenSet u2) (texV2 (fracOdd u1)) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have pc5 : pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 5 = shiftS (tEvenSet u2) (texV2 (fracOdd u1) + texV1Even (fracEven u2)) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have hpl : 0 < (fracOdd u1).num ∧ (fracOdd u1).num < (fracOdd u1).den := SiteHullOdd.curO_pos_lt u1
  have hql : 0 < (fracEven u2).num ∧ (fracEven u2).num < (fracEven u2).den := SiteHullEven.curE_pos_lt u2
  have hpo : ((fracOdd u1).num + (fracOdd u1).den) % 2 = 1 := SiteHullOdd.curO_odd u1
  have hqe : ((fracEven u2).num + (fracEven u2).den) % 2 = 0 := SiteHullEven.curE_num_add_den_even u2
  obtain ⟨p', q', f1, f2, f3, f4, f5, f6, hsmall, h1, h2, h3⟩ := GlueBlockBounds.last_facts w hw
  rw [hp, hq] at h1 h2 h3
  obtain ⟨dg, hdg⟩ : ∃ d, w.getLast? = some d := Option.ne_none_iff_exists'.1 (by simpa using hw)
  have hlin : (w.getLast? = some Digit.one ∧ ((fracOdd u1).num = p'.num + q'.num ∧ (fracOdd u1).den = p'.den + q'.den ∧ (fracEven u2).num = 2 * p'.num + q'.num ∧ (fracEven u2).den = 2 * p'.den + q'.den)) ∨
      (w.getLast? = some Digit.two ∧ ((fracOdd u1).num = p'.num + q'.num ∧ (fracOdd u1).den = p'.den + q'.den ∧ (fracEven u2).num = q'.num ∧ (fracEven u2).den = q'.den)) := by
    cases dg
    · exact Or.inl ⟨hdg, h1 hdg⟩
    · exact Or.inr ⟨hdg, h2 hdg⟩
    · exact absurd hdg hlast
  have c10 : ∀ x ∈ blockSitesOdd w u1 u2 1, x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 0 → False := by
    intro x hx0 hxj0
    have hx := hx0
    have hxj := hxj0
    simp only [blockSitesOdd, if_pos hph, List.mem_append] at hx
    rw [pc0] at hxj
    have bj := ClosedPathExcluded.box_shift_odd u1 _ x hxj
    have dj := ClosedPathDiagonal.diag_shift_odd u1 _ x hxj
    simp only [Prod.fst_zero, Prod.snd_zero] at bj dj
    rcases hx with hx | hx
    · have hb := GlueBlockBounds.top_lin _ _ (by simpa using GlueStringDecomp.hWord_ne u1 false) x hx
      rw [GlueStringDecomp.lp_top_odd] at hb
      simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨hl, -⟩
      · omega
      · exact hcol.1 hl x hx0 hxj0
    · have hb := GlueBlockBounds.right_lin _ _ (GlueStringDecomp.vWord_odd_ne u1) x hx
      rw [GlueStringDecomp.lp_right_odd] at hb
      simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨hl, -⟩
      · omega
      · exact hcol.1 hl x hx0 hxj0
  have c42 : ∀ x ∈ blockSitesOdd w u1 u2 4, x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 2 → False := by
    intro x hx0 hxj0
    have hx := hx0
    have hxj := hxj0
    simp only [blockSitesOdd, if_pos hph, List.mem_append] at hx
    rw [pc2] at hxj
    have bj := ClosedPathExcluded.box_shift_even u2 _ x hxj
    have dj := ClosedPathDiagonal.diag_shift_even u2 _ x hxj
    simp only [texV1Odd] at bj dj
    rcases hx with hx | hx
    · have hb := GlueBlockBounds.top_lin _ _ (by simpa using GlueStringDecomp.hWord_ne u2 true) x hx
      rw [GlueStringDecomp.lp_top_even] at hb
      simp only [texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
    · have hb := GlueBlockBounds.left_lin _ _ (by simpa using GlueStringDecomp.vWord_even_ne u2) x hx
      rw [GlueStringDecomp.lp_left_even] at hb
      simp only [texV2, Prod.fst_add, Prod.snd_add] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
  have c52 : ∀ x ∈ blockSitesOdd w u1 u2 5, x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 2 → False := by
    intro x hx0 hxj0
    have hx := hx0
    have hxj := hxj0
    simp only [blockSitesOdd, if_pos hph] at hx
    rw [pc2] at hxj
    have bj := ClosedPathExcluded.box_shift_even u2 _ x hxj
    have dj := ClosedPathDiagonal.diag_shift_even u2 _ x hxj
    simp only [texV1Odd] at bj dj
    have hb := GlueBlockBounds.top_lin _ _ (by simpa using GlueStringDecomp.hWord_ne u2 true) x hx
    rw [GlueStringDecomp.lp_top_even] at hb
    simp only [texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
    rcases hlin with ⟨hl, hh⟩ | ⟨-, hh⟩
    · rcases hsmall with hs | hs
      · exact hcol.2 hs hl x hx0 hxj0
      · omega
    · omega
  have c43 : ∀ x ∈ blockSitesOdd w u1 u2 4, x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 3 → False := by
    intro x hx0 hxj0
    have hx := hx0
    have hxj := hxj0
    simp only [blockSitesOdd, if_pos hph, List.mem_append] at hx
    rw [pc3] at hxj
    have bj := ClosedPathExcluded.box_shift_even u2 _ x hxj
    have dj := ClosedPathDiagonal.diag_shift_even u2 _ x hxj
    simp only [texV1Odd, texV1Even, Prod.fst_add, Prod.snd_add] at bj dj
    rcases hx with hx | hx
    · have hb := GlueBlockBounds.top_lin _ _ (by simpa using GlueStringDecomp.hWord_ne u2 true) x hx
      rw [GlueStringDecomp.lp_top_even] at hb
      simp only [texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
    · have hb := GlueBlockBounds.left_lin _ _ (by simpa using GlueStringDecomp.vWord_even_ne u2) x hx
      rw [GlueStringDecomp.lp_left_even] at hb
      simp only [texV2, Prod.fst_add, Prod.snd_add] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
  have c53 : ∀ x ∈ blockSitesOdd w u1 u2 5, x ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) 3 → False := by
    intro x hx0 hxj0
    have hx := hx0
    have hxj := hxj0
    simp only [blockSitesOdd, if_pos hph] at hx
    rw [pc3] at hxj
    have bj := ClosedPathExcluded.box_shift_even u2 _ x hxj
    have dj := ClosedPathDiagonal.diag_shift_even u2 _ x hxj
    simp only [texV1Odd, texV1Even, Prod.fst_add, Prod.snd_add] at bj dj
    have hb := GlueBlockBounds.top_lin _ _ (by simpa using GlueStringDecomp.hWord_ne u2 true) x hx
    rw [GlueStringDecomp.lp_top_even] at hb
    simp only [texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
    rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
  intro i j hj hi hf hd x hx hxj
  interval_cases i <;> interval_cases j <;>
    first
    | (simp [pieceFlag, ClosedPathCycle.oddP_length] at hf; done)
    | (simp [dblOdd, ClosedPathCycle.oddP_length] at hd; done)
    | exact c10 x hx hxj
    | exact c42 x hx hxj
    | exact c52 x hx hxj
    | exact c43 x hx hxj
    | exact c53 x hx hxj

/-- **The block exclusions of the even child, W_1 even.** -/
theorem even_ef_excl (w u1 u2 : Word) (hw : w ≠ []) (hph : phase w ≠ 1) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hlast : w.getLast? ≠ some Digit.two)
    (hcol : ColumnExclEven w u1 u2) : BlockExclEven w u1 u2 := by
  have hP := ClosedPathAssembly.evenP_ef w hph
  have hQ := ClosedPathAssembly.evenQ_ef w hph
  have pc0 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 0 = shiftS (tOddSet u1) (texV1Even (fracEven u2)) := by
    simp [pieceSet, hP, hp, hq]
  have pc1 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 1 = shiftS (tOddSet u1) (texV1Even (fracEven u2) + texV2 (fracOdd u1)) := by
    simp [pieceSet, hP, hp, hq]
  have pc2 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 2 = shiftS (tOddSet u1) (texV2 (fracEven u2)) := by
    simp [pieceSet, hP, hp, hq]
  have pc3 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 3 = shiftS (tOddSet u1) (texV2 (fracEven u2) + texV2 (fracOdd u1)) := by
    simp [pieceSet, hP, hp, hq]
  have pc4 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 4 = shiftS (tEvenSet u2) (0) := by
    simp [pieceSet, hP, hQ, hp, hq]
  have pc5 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 5 = shiftS (tEvenSet u2) (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1)) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have hpl : 0 < (fracOdd u1).num ∧ (fracOdd u1).num < (fracOdd u1).den := SiteHullOdd.curO_pos_lt u1
  have hql : 0 < (fracEven u2).num ∧ (fracEven u2).num < (fracEven u2).den := SiteHullEven.curE_pos_lt u2
  have hpo : ((fracOdd u1).num + (fracOdd u1).den) % 2 = 1 := SiteHullOdd.curO_odd u1
  have hqe : ((fracEven u2).num + (fracEven u2).den) % 2 = 0 := SiteHullEven.curE_num_add_den_even u2
  obtain ⟨p', q', f1, f2, f3, f4, f5, f6, hsmall, h1, h2, h3⟩ := GlueBlockBounds.last_facts w hw
  rw [hp, hq] at h1 h2 h3
  obtain ⟨dg, hdg⟩ : ∃ d, w.getLast? = some d := Option.ne_none_iff_exists'.1 (by simpa using hw)
  have hlin : (w.getLast? = some Digit.one ∧ ((fracOdd u1).num = p'.num + q'.num ∧ (fracOdd u1).den = p'.den + q'.den ∧ (fracEven u2).num = 2 * p'.num + q'.num ∧ (fracEven u2).den = 2 * p'.den + q'.den)) ∨
      (w.getLast? = some Digit.three ∧ ((fracOdd u1).num = p'.num ∧ (fracOdd u1).den = p'.den ∧ (fracEven u2).num = 2 * p'.num + q'.num ∧ (fracEven u2).den = 2 * p'.den + q'.den)) := by
    cases dg
    · exact Or.inl ⟨hdg, h1 hdg⟩
    · exact absurd hdg hlast
    · exact Or.inr ⟨hdg, h3 hdg⟩
  have c20 : ∀ x ∈ blockSitesEven w u1 u2 2, x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 0 → False := by
    intro x hx0 hxj0
    have hx := hx0
    have hxj := hxj0
    simp only [blockSitesEven, if_neg hph] at hx
    rw [pc0] at hxj
    have bj := ClosedPathExcluded.box_shift_odd u1 _ x hxj
    have dj := ClosedPathDiagonal.diag_shift_odd u1 _ x hxj
    simp only [texV1Even] at bj dj
    have hb := GlueBlockBounds.left_lin _ _ (by simpa using GlueStringDecomp.vWord_odd_ne u1) x hx
    rw [GlueStringDecomp.lp_left_odd] at hb
    simp only [texV2, Prod.fst_add, Prod.snd_add] at hb
    rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
  have c30 : ∀ x ∈ blockSitesEven w u1 u2 3, x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 0 → False := by
    intro x hx0 hxj0
    have hx := hx0
    have hxj := hxj0
    simp only [blockSitesEven, if_neg hph, List.mem_append] at hx
    rw [pc0] at hxj
    have bj := ClosedPathExcluded.box_shift_odd u1 _ x hxj
    have dj := ClosedPathDiagonal.diag_shift_odd u1 _ x hxj
    simp only [texV1Even] at bj dj
    rcases hx with hx | hx
    · have hb := GlueBlockBounds.top_lin _ _ (by simpa using GlueStringDecomp.hWord_ne u1 false) x hx
      rw [GlueStringDecomp.lp_top_odd] at hb
      simp only [texV1Odd, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
    · have hb := GlueBlockBounds.left_lin _ _ (by simpa using GlueStringDecomp.vWord_odd_ne u1) x hx
      rw [GlueStringDecomp.lp_left_odd] at hb
      simp only [texV2, Prod.fst_add, Prod.snd_add] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
  have c21 : ∀ x ∈ blockSitesEven w u1 u2 2, x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 1 → False := by
    intro x hx0 hxj0
    have hx := hx0
    have hxj := hxj0
    simp only [blockSitesEven, if_neg hph] at hx
    rw [pc1] at hxj
    have bj := ClosedPathExcluded.box_shift_odd u1 _ x hxj
    have dj := ClosedPathDiagonal.diag_shift_odd u1 _ x hxj
    simp only [texV1Even, texV2, Prod.fst_add, Prod.snd_add] at bj dj
    have hb := GlueBlockBounds.left_lin _ _ (by simpa using GlueStringDecomp.vWord_odd_ne u1) x hx
    rw [GlueStringDecomp.lp_left_odd] at hb
    simp only [texV2, Prod.fst_add, Prod.snd_add] at hb
    rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
  have c31 : ∀ x ∈ blockSitesEven w u1 u2 3, x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 1 → False := by
    intro x hx0 hxj0
    have hx := hx0
    have hxj := hxj0
    simp only [blockSitesEven, if_neg hph, List.mem_append] at hx
    rw [pc1] at hxj
    have bj := ClosedPathExcluded.box_shift_odd u1 _ x hxj
    have dj := ClosedPathDiagonal.diag_shift_odd u1 _ x hxj
    simp only [texV1Even, texV2, Prod.fst_add, Prod.snd_add] at bj dj
    rcases hx with hx | hx
    · have hb := GlueBlockBounds.top_lin _ _ (by simpa using GlueStringDecomp.hWord_ne u1 false) x hx
      rw [GlueStringDecomp.lp_top_odd] at hb
      simp only [texV1Odd, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
    · have hb := GlueBlockBounds.left_lin _ _ (by simpa using GlueStringDecomp.vWord_odd_ne u1) x hx
      rw [GlueStringDecomp.lp_left_odd] at hb
      simp only [texV2, Prod.fst_add, Prod.snd_add] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
  have c54 : ∀ x ∈ blockSitesEven w u1 u2 5, x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 4 → False := by
    intro x hx0 hxj0
    have hx := hx0
    have hxj := hxj0
    simp only [blockSitesEven, if_neg hph, List.mem_append] at hx
    rw [pc4] at hxj
    have bj := ClosedPathExcluded.box_shift_even u2 _ x hxj
    have dj := ClosedPathDiagonal.diag_shift_even u2 _ x hxj
    simp only [Prod.fst_zero, Prod.snd_zero] at bj dj
    rcases hx with hx | hx
    · have hb := GlueBlockBounds.top_lin _ _ (by simpa using GlueStringDecomp.hWord_ne u2 true) x hx
      rw [GlueStringDecomp.lp_top_even] at hb
      simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨hl, -⟩
      · omega
      · exact hcol hl x hx0 hxj0
    · have hb := GlueBlockBounds.right_lin _ _ (GlueStringDecomp.vWord_even_ne u2) x hx
      rw [GlueStringDecomp.lp_right_even] at hb
      simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨hl, -⟩
      · omega
      · exact hcol hl x hx0 hxj0
  intro i j hj hi hf hd x hx hxj
  interval_cases i <;> interval_cases j <;>
    first
    | (simp [pieceFlag, ClosedPathCycle.evenP_length] at hf; done)
    | (simp [dblEven] at hd; done)
    | exact c20 x hx hxj
    | exact c30 x hx hxj
    | exact c21 x hx hxj
    | exact c31 x hx hxj
    | exact c54 x hx hxj

/-- **The block exclusions of the even child, W_1 odd.** -/
theorem even_of_excl (w u1 u2 : Word) (hw : w ≠ []) (hph : phase w = 1) (hp : (parentsAt w).odd = fracOdd u1)
    (hq : (parentsAt w).even = fracEven u2) (hlast : w.getLast? ≠ some Digit.two)
    (hcol : ColumnExclEven w u1 u2) : BlockExclEven w u1 u2 := by
  have hP := ClosedPathAssembly.evenP_of w hph
  have hQ := ClosedPathAssembly.evenQ_of w hph
  have pc0 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 0 = shiftS (tOddSet u1) (0) := by
    simp [pieceSet, hP, hp, hq, add_assoc]
  have pc1 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 1 = shiftS (tOddSet u1) (texV2 (fracOdd u1)) := by
    simp [pieceSet, hP, hp, hq, add_assoc]
  have pc2 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 2 = shiftS (tOddSet u1) (texV1Even (fracEven u2) + texV2 (fracEven u2)) := by
    simp [pieceSet, hP, hp, hq, add_assoc]
  have pc3 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 3 = shiftS (tOddSet u1) (texV1Even (fracEven u2) + texV2 (fracEven u2) + texV2 (fracOdd u1)) := by
    simp [pieceSet, hP, hp, hq, add_assoc]
  have pc4 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 4 = shiftS (tEvenSet u2) (texV1Odd (fracOdd u1)) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have pc5 : pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 5 = shiftS (tEvenSet u2) (texV2 (fracOdd u1) + texV2 (fracOdd u1)) := by
    simp [pieceSet, hP, hQ, hp, hq, add_assoc]
  have hpl : 0 < (fracOdd u1).num ∧ (fracOdd u1).num < (fracOdd u1).den := SiteHullOdd.curO_pos_lt u1
  have hql : 0 < (fracEven u2).num ∧ (fracEven u2).num < (fracEven u2).den := SiteHullEven.curE_pos_lt u2
  have hpo : ((fracOdd u1).num + (fracOdd u1).den) % 2 = 1 := SiteHullOdd.curO_odd u1
  have hqe : ((fracEven u2).num + (fracEven u2).den) % 2 = 0 := SiteHullEven.curE_num_add_den_even u2
  obtain ⟨p', q', f1, f2, f3, f4, f5, f6, hsmall, h1, h2, h3⟩ := GlueBlockBounds.last_facts w hw
  rw [hp, hq] at h1 h2 h3
  obtain ⟨dg, hdg⟩ : ∃ d, w.getLast? = some d := Option.ne_none_iff_exists'.1 (by simpa using hw)
  have hlin : (w.getLast? = some Digit.one ∧ ((fracOdd u1).num = p'.num + q'.num ∧ (fracOdd u1).den = p'.den + q'.den ∧ (fracEven u2).num = 2 * p'.num + q'.num ∧ (fracEven u2).den = 2 * p'.den + q'.den)) ∨
      (w.getLast? = some Digit.three ∧ ((fracOdd u1).num = p'.num ∧ (fracOdd u1).den = p'.den ∧ (fracEven u2).num = 2 * p'.num + q'.num ∧ (fracEven u2).den = 2 * p'.den + q'.den)) := by
    cases dg
    · exact Or.inl ⟨hdg, h1 hdg⟩
    · exact absurd hdg hlast
    · exact Or.inr ⟨hdg, h3 hdg⟩
  have c20 : ∀ x ∈ blockSitesEven w u1 u2 2, x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 0 → False := by
    intro x hx0 hxj0
    have hx := hx0
    have hxj := hxj0
    simp only [blockSitesEven, if_pos hph] at hx
    rw [pc0] at hxj
    have bj := ClosedPathExcluded.box_shift_odd u1 _ x hxj
    have dj := ClosedPathDiagonal.diag_shift_odd u1 _ x hxj
    simp only [Prod.fst_zero, Prod.snd_zero] at bj dj
    have hb := GlueBlockBounds.right_lin _ _ (GlueStringDecomp.vWord_odd_ne u1) x hx
    rw [GlueStringDecomp.lp_right_odd] at hb
    simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
    rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
  have c30 : ∀ x ∈ blockSitesEven w u1 u2 3, x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 0 → False := by
    intro x hx0 hxj0
    have hx := hx0
    have hxj := hxj0
    simp only [blockSitesEven, if_pos hph, List.mem_append] at hx
    rw [pc0] at hxj
    have bj := ClosedPathExcluded.box_shift_odd u1 _ x hxj
    have dj := ClosedPathDiagonal.diag_shift_odd u1 _ x hxj
    simp only [Prod.fst_zero, Prod.snd_zero] at bj dj
    rcases hx with hx | hx
    · have hb := GlueBlockBounds.top_lin _ _ (by simpa using GlueStringDecomp.hWord_ne u1 false) x hx
      rw [GlueStringDecomp.lp_top_odd] at hb
      simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
    · have hb := GlueBlockBounds.right_lin _ _ (GlueStringDecomp.vWord_odd_ne u1) x hx
      rw [GlueStringDecomp.lp_right_odd] at hb
      simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
  have c21 : ∀ x ∈ blockSitesEven w u1 u2 2, x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 1 → False := by
    intro x hx0 hxj0
    have hx := hx0
    have hxj := hxj0
    simp only [blockSitesEven, if_pos hph] at hx
    rw [pc1] at hxj
    have bj := ClosedPathExcluded.box_shift_odd u1 _ x hxj
    have dj := ClosedPathDiagonal.diag_shift_odd u1 _ x hxj
    simp only [texV2] at bj dj
    have hb := GlueBlockBounds.right_lin _ _ (GlueStringDecomp.vWord_odd_ne u1) x hx
    rw [GlueStringDecomp.lp_right_odd] at hb
    simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
    rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
  have c31 : ∀ x ∈ blockSitesEven w u1 u2 3, x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 1 → False := by
    intro x hx0 hxj0
    have hx := hx0
    have hxj := hxj0
    simp only [blockSitesEven, if_pos hph, List.mem_append] at hx
    rw [pc1] at hxj
    have bj := ClosedPathExcluded.box_shift_odd u1 _ x hxj
    have dj := ClosedPathDiagonal.diag_shift_odd u1 _ x hxj
    simp only [texV2] at bj dj
    rcases hx with hx | hx
    · have hb := GlueBlockBounds.top_lin _ _ (by simpa using GlueStringDecomp.hWord_ne u1 false) x hx
      rw [GlueStringDecomp.lp_top_odd] at hb
      simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
    · have hb := GlueBlockBounds.right_lin _ _ (GlueStringDecomp.vWord_odd_ne u1) x hx
      rw [GlueStringDecomp.lp_right_odd] at hb
      simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨-, hh⟩ <;> omega
  have c54 : ∀ x ∈ blockSitesEven w u1 u2 5, x ∈ pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) 4 → False := by
    intro x hx0 hxj0
    have hx := hx0
    have hxj := hxj0
    simp only [blockSitesEven, if_pos hph, List.mem_append] at hx
    rw [pc4] at hxj
    have bj := ClosedPathExcluded.box_shift_even u2 _ x hxj
    have dj := ClosedPathDiagonal.diag_shift_even u2 _ x hxj
    simp only [texV1Odd] at bj dj
    rcases hx with hx | hx
    · have hb := GlueBlockBounds.top_lin _ _ (by simpa using GlueStringDecomp.hWord_ne u2 true) x hx
      rw [GlueStringDecomp.lp_top_even] at hb
      simp only [texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨hl, -⟩
      · omega
      · exact hcol hl x hx0 hxj0
    · have hb := GlueBlockBounds.left_lin _ _ (by simpa using GlueStringDecomp.vWord_even_ne u2) x hx
      rw [GlueStringDecomp.lp_left_even] at hb
      simp only [texV2, Prod.fst_add, Prod.snd_add] at hb
      rcases hlin with ⟨-, hh⟩ | ⟨hl, -⟩
      · omega
      · exact hcol hl x hx0 hxj0
  intro i j hj hi hf hd x hx hxj
  interval_cases i <;> interval_cases j <;>
    first
    | (simp [pieceFlag, ClosedPathCycle.evenP_length] at hf; done)
    | (simp [dblEven] at hd; done)
    | exact c20 x hx hxj
    | exact c30 x hx hxj
    | exact c21 x hx hxj
    | exact c31 x hx hxj
    | exact c54 x hx hxj

/-! ### The uncorrected children -/

/-- **The block exclusions of the odd child** at the words that Section 8 does not correct, given the column input. -/
theorem blockExclOdd_of (w u1 u2 : Word) (hw : ¬ Standard.IsBase w) (hreg : regsAt w = (some u1, some u2))
    (hc : ¬ JointFamily.CorrectedAfterThree w) (hcol : ColumnExclOdd w u1 u2) : BlockExclOdd w u1 u2 := by
  have hp : (parentsAt w).odd = fracOdd u1 := (WeakStepAssembly.regsAt_parents w).1 u1 (by rw [hreg])
  have hq : (parentsAt w).even = fracEven u2 := (WeakStepAssembly.regsAt_parents w).2 u2 (by rw [hreg])
  have hne : w ≠ [] := fun h => hw (Or.inl h)
  have hl : w.getLast? ≠ some Digit.three := fun h => hc ⟨hw, h⟩
  by_cases hph : phase w = 1
  · exact odd_of_excl w u1 u2 hne hph hp hq hl hcol
  · exact odd_ef_excl w u1 u2 hne hph hp hq hl hcol

/-- **The block exclusions of the even child** at the words that Section 8 does not correct, given the column input. -/
theorem blockExclEven_of (w u1 u2 : Word) (hw : ¬ Standard.IsBase w) (hreg : regsAt w = (some u1, some u2))
    (hc : ¬ JointFamily.CorrectedAfterTwo w) (hcol : ColumnExclEven w u1 u2) : BlockExclEven w u1 u2 := by
  have hp : (parentsAt w).odd = fracOdd u1 := (WeakStepAssembly.regsAt_parents w).1 u1 (by rw [hreg])
  have hq : (parentsAt w).even = fracEven u2 := (WeakStepAssembly.regsAt_parents w).2 u2 (by rw [hreg])
  have hne : w ≠ [] := fun h => hw (Or.inl h)
  have hl : w.getLast? ≠ some Digit.two := fun h => hc ⟨hw, h⟩
  by_cases hph : phase w = 1
  · exact even_of_excl w u1 u2 hne hph hp hq hl hcol
  · exact even_ef_excl w u1 u2 hne hph hp hq hl hcol

/-- The column inputs at the uncorrected children. -/
def ColumnInput : Prop :=
  ∀ w u1 u2 : Word, ¬ Standard.IsBase w → regsAt w = (some u1, some u2) →
    (¬ JointFamily.CorrectedAfterThree w → ColumnExclOdd w u1 u2) ∧
      (¬ JointFamily.CorrectedAfterTwo w → ColumnExclEven w u1 u2)

theorem blockExcl_of_columns (hcol : ColumnInput) (w u1 u2 : Word) (hw : ¬ Standard.IsBase w)
    (hreg : regsAt w = (some u1, some u2)) :
    (¬ JointFamily.CorrectedAfterThree w → BlockExclOdd w u1 u2) ∧
      (¬ JointFamily.CorrectedAfterTwo w → BlockExclEven w u1 u2) :=
  ⟨fun hc => blockExclOdd_of w u1 u2 hw hreg hc ((hcol w u1 u2 hw hreg).1 hc),
    fun hc => blockExclEven_of w u1 u2 hw hreg hc ((hcol w u1 u2 hw hreg).2 hc)⟩

/-- **`GlueRespectsInput` for the paper's data from the column inputs.** -/
theorem glueRespectsInput_of_columns (D : JointFamily.JointData) (hS : D.S = WeakStepPaper.paperS) (hcol : ColumnInput) :
    WeakStepAssembly.GlueRespectsInput D :=
  glueRespectsInput D hS (blockExcl_of_columns hcol)

/-- **`GlueLatticeInput` for the paper's data from the column inputs.** -/
theorem glueLatticeInput_of_columns (D : JointFamily.JointData) (hS : D.S = WeakStepPaper.paperS)
    (hsl : WeakStepAssembly.TileSlopeZero D) (hcol : ColumnInput) : WeakStepAssembly.GlueLatticeInput D :=
  glueLatticeInput D hS hsl (blockExcl_of_columns hcol)

end FLatticePaper.Tiles.GlueBlockExcl
