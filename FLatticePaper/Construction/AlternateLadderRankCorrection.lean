import FLatticePaper.Construction.AlternateLadderExtension

namespace FLatticePaper.Construction

open Farey

abbrev LadderOddAltTop (den : ℤ) (point : Site) : Prop :=
  point.2 = den + 2 ∧ 0 ≤ point.1 ∧ point.1 ≤ den - 1

abbrev LadderOddAltShelf (den : ℤ) (point : Site) : Prop :=
  point.2 = den + 1 ∧ 0 ≤ point.1 ∧ point.1 ≤ den - 1

abbrev LadderOddAltBand (den : ℤ) (point : Site) : Prop :=
  point.1 + point.2 = 2 * den ∧ den ≤ point.1 ∧ point.1 ≤ 2 * den - 2

abbrev LadderOddAltLeftHigh (den : ℤ) (point : Site) : Prop :=
  0 ≤ point.1 ∧ 0 ≤ point.2 ∧ point.1 + point.2 ≤ den - 1

abbrev LadderOddAltRightHigh (den : ℤ) (point : Site) : Prop :=
  den - 1 ≤ point.1 ∧ 1 ≤ point.2 ∧ point.2 ≤ den ∧ point.1 + point.2 ≤ 2 * den - 1

abbrev LadderOddAltMiddle (den : ℤ) (point : Site) : Prop :=
  1 ≤ point.1 ∧ point.1 ≤ den - 2 ∧ point.2 ≤ den ∧ den + 1 ≤ point.1 + point.2

/-- The B7 correction in the regions of formula (13). -/
def ladderOddAltRankCorrection (den : ℤ) (point : Site) : ℤ :=
  let parity := (point.1 + point.2) % 2
  if BaseMask.LadderOddAltCorner den point then 4
  else if point.1 = den ∧ point.2 = den + 1 then 5
  else if LadderOddAltTop den point then 8 * (den - point.1) + parity
  else if LadderOddAltShelf den point then 8 * den - 4 * point.1 + parity
  else if LadderOddAltBand den point then 8
  else if BaseMask.LadderOddAltDiagonal den point then 8 * (den + point.2) - 4
  else if LadderOddAltLeftHigh den point then 8 * (2 * den - 1 - point.1) + parity
  else if LadderOddAltRightHigh den point then 8 * (2 * den - 1 - point.1) + parity
  else if LadderOddAltMiddle den point then 8 * den - 4 * point.1 + parity
  else parity

local macro "alternate_ladder_rank" : tactic => `(tactic|
  (simp (disch := omega) only [ladderOddAltRankCorrection, BaseMask.LadderOddAltCorner,
      BaseMask.LadderOddAltDiagonal, LadderOddAltTop, LadderOddAltShelf, LadderOddAltBand,
      LadderOddAltLeftHigh, LadderOddAltRightHigh, LadderOddAltMiddle, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub, if_pos, if_neg]
   repeat' first | omega | (split <;> rename_i hclause <;>
     simp only [true_and, and_true, true_or, or_true, false_and, and_false, false_or, or_false,
       not_true_eq_false, not_false_eq_true] at hclause)))

private theorem ladderOddAlt_rankCorrection_kernel {den : ℤ} (hmin : 4 ≤ den) {point : Site}
    (hp : point ∈ (BaseMask.ladderOddAlt.raw den).sites)
    (hq : point + (2 * den, 2) ∈ (BaseMask.ladderOddAlt.raw den).sites) :
    ladderOddAltRankCorrection den (point + (2 * den, 2)) = ladderOddAltRankCorrection den point := by
  have hs := ladderOddAlt_kernel_overlap hp hq
  obtain ⟨x, y⟩ := point
  dsimp only at hs
  alternate_ladder_rank

private theorem ladderOddAlt_rankCorrection_transverse {den : ℤ} (hmin : 4 ≤ den) {point : Site}
    (hp : point ∈ (BaseMask.ladderOddAlt.raw den).sites)
    (hq : point + (1 - den, den + 1) ∈ (BaseMask.ladderOddAlt.raw den).sites) :
    ladderOddAltRankCorrection den (point + (1 - den, den + 1)) = ladderOddAltRankCorrection den point := by
  have hs := ladderOddAlt_transverse_overlap hp hq
  obtain ⟨x, y⟩ := point
  dsimp only at hs
  rcases hs with h | h | h <;> alternate_ladder_rank

private theorem ladderOddAlt_rankCorrection_diagonal {den : ℤ} {point : Site}
    (hp : point ∈ (BaseMask.ladderOddAlt.raw den).sites)
    (hq : point + (den + 1, den + 3) ∈ (BaseMask.ladderOddAlt.raw den).sites) :
    ladderOddAltRankCorrection den (point + (den + 1, den + 3)) = ladderOddAltRankCorrection den point := by
  have heq := ladderOddAlt_diagonal_overlap hp hq
  subst point
  have ha : BaseMask.LadderOddAltCorner den (-1, -1) := Or.inl ⟨rfl, rfl⟩
  have hb : BaseMask.LadderOddAltCorner den (((-1, -1) : Site) + (den + 1, den + 3)) := by
    simp only [BaseMask.LadderOddAltCorner, Prod.fst_add, Prod.snd_add]
    omega
  simp only [ladderOddAltRankCorrection, if_pos ha, if_pos hb]

private theorem ladderOddAlt_rankCorrection_positive {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    {first second : Site} (hp : first ∈ (BaseMask.ladderOddAlt.raw den).sites)
    (hq : second ∈ (BaseMask.ladderOddAlt.raw den).sites) {i j : ℤ}
    (hshift : second = first + (reciprocalLadderDeck den).combine i j)
    (hindex : (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 1)) :
    ladderOddAltRankCorrection den second = ladderOddAltRankCorrection den first := by
  rw [reciprocalLadderDeck_eq hden.2] at hshift
  rcases hindex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have heq : second = first + (2 * den, 2) := by simpa [PeriodDeck.combine] using hshift
    simpa only [heq] using ladderOddAlt_rankCorrection_kernel hden.1 hp (heq ▸ hq)
  · have heq : second = first + (1 - den, den + 1) := by simpa [PeriodDeck.combine, add_comm 1 den] using hshift
    simpa only [heq] using ladderOddAlt_rankCorrection_transverse hden.1 hp (heq ▸ hq)
  · have heq : second = first + (den + 1, den + 3) := by
      rw [hshift]
      apply congrArg (first + ·)
      apply Prod.ext <;> simp only [PeriodDeck.combine, one_mul] <;> omega
    simpa only [heq] using ladderOddAlt_rankCorrection_diagonal hp (heq ▸ hq)

theorem ladderOddAlt_rankCorrection_class_constant {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    {first second : Site} (hp : first ∈ (BaseMask.ladderOddAlt.raw den).sites)
    (hq : second ∈ (BaseMask.ladderOddAlt.raw den).sites)
    (hclass : second - first ∈ (reciprocalLadderDeck den).span) :
    ladderOddAltRankCorrection den second = ladderOddAltRankCorrection den first := by
  obtain ⟨i, j, hdiff⟩ := hclass
  have hshift : second = first + (reciprocalLadderDeck den).combine i j := by
    rw [← hdiff, add_comm first, sub_add_cancel]
  have hindex := ladderOddAlt_overlap_indices hden hp hq hshift
  have hneg {p q : ℤ}
      (hmove : second = first + (reciprocalLadderDeck den).combine (-p) (-q))
      (hpos : (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 1)) :
      ladderOddAltRankCorrection den second = ladderOddAltRankCorrection den first := by
    have hrev : first = second + (reciprocalLadderDeck den).combine p q := by
      rw [hmove]
      apply Prod.ext <;> simp only [PeriodDeck.combine, Prod.fst_add, Prod.snd_add] <;> ring
    exact (ladderOddAlt_rankCorrection_positive hden hq hp hrev hpos).symm
  rcases hindex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa [PeriodDeck.combine, show ((0, 0) : Site) = 0 from rfl] using
      congrArg (ladderOddAltRankCorrection den) hshift
  · exact ladderOddAlt_rankCorrection_positive hden hp hq hshift (Or.inl ⟨rfl, rfl⟩)
  · exact hneg (p := 1) (q := 0) hshift (Or.inl ⟨rfl, rfl⟩)
  · exact ladderOddAlt_rankCorrection_positive hden hp hq hshift (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact hneg (p := 0) (q := 1) hshift (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact ladderOddAlt_rankCorrection_positive hden hp hq hshift (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · exact hneg (p := 1) (q := 1) hshift (Or.inr (Or.inr ⟨rfl, rfl⟩))

theorem ladderOddAlt_exists_periodic_rankCorrection {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den) :
    ∃ correction : Field, (∀ point ∈ (BaseMask.ladderOddAlt.raw den).sites,
      correction point = ladderOddAltRankCorrection den point) ∧
      ∀ step ∈ (reciprocalLadderDeck den).span, Function.Periodic correction step := by
  classical
  let deck := reciprocalLadderDeck den
  have hcover : deck.Covers (BaseMask.ladderOddAlt.raw den).sites := ladderOddAlt_raw_cover hden
  choose repr hmem hspan using hcover
  have hpos : 0 < deck.det := by
    apply Fraction.det_modifiedDeck_pos
    have := hden.1
    exact ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩
  have hclass (site : Site) : deck.classCode site = deck.classCode (repr site) :=
    (deck.classCode_eq_iff (ne_of_gt hpos) ..).mpr (hspan site)
  refine ⟨fun site => ladderOddAltRankCorrection den (repr site), ?_, ?_⟩
  · intro site hsite
    exact ladderOddAlt_rankCorrection_class_constant hden hsite (hmem site)
      ((deck.classCode_eq_iff (ne_of_gt hpos) ..).mp (hclass site).symm)
  · intro step hstep site
    have hshift : deck.classCode (site + step) = deck.classCode site :=
      (deck.classCode_eq_iff (ne_of_gt hpos) ..).mpr (by simpa only [add_sub_cancel_left] using hstep)
    exact ladderOddAlt_rankCorrection_class_constant hden (hmem site) (hmem (site + step))
      ((deck.classCode_eq_iff (ne_of_gt hpos) ..).mp ((hclass (site + step)).symm.trans (hshift.trans (hclass site))))

end FLatticePaper.Construction
