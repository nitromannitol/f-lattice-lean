import FLatticePaper.Construction.LadderExtension

namespace FLatticePaper.Construction

open Farey

/-- The ordered B5 rank correction of formula (5) on the raw mask. -/
def ladderOddRankCorrection (den : ℤ) (point : Site) : ℤ :=
  let sum := point.1 + point.2
  let parity := sum % 2
  if (point.1 = 0 ∧ point.2 = 0) ∨ (point.1 = 2 * den ∧ point.2 = 2) then 4
  else if (point.1 = 2 * den ∧ point.2 = 1) ∨ (point.1 = den + 1 ∧ point.2 = den + 2) then 5
  else if point.1 = den + 2 ∧ point.2 = den + 2 then 0
  else if point.2 = 0 ∨ point.1 ≤ 0 then parity
  else if point.2 = den + 2 ∨ (point.2 = 1 ∧ den + 2 ≤ point.1) ∨
      (point.1 ≤ den ∧ den + 3 ≤ sum) then 8 + parity
  else if sum ≤ den + 1 then 8 * (den + 1 - point.1) + parity
  else if sum = den + 2 ∧ (point.1 = 1 ∨ point.1 = den + 1) then 8
  else if sum = den + 2 then 8 * den
  else if sum ≤ 2 * den + 1 then 8 * (2 * den - point.1) + parity
  else if sum = 2 * den + 2 then 8
  else 1

local macro "ladder_rank" : tactic => `(tactic|
  (simp (disch := omega) only [ladderOddRankCorrection, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub, if_pos, if_neg]
   repeat' first | omega | (split <;> rename_i hclause <;>
     simp only [true_and, and_true, true_or, or_true, false_and, and_false, false_or, or_false,
       not_true_eq_false, not_false_eq_true] at hclause)))

private theorem ladderOdd_rankCorrection_kernel {den : ℤ} (hmin : 4 ≤ den) {point : Site}
    (hp : point ∈ (BaseMask.ladderOdd.raw den).sites)
    (hq : point + (2 * den, 2) ∈ (BaseMask.ladderOdd.raw den).sites) :
    ladderOddRankCorrection den (point + (2 * den, 2)) = ladderOddRankCorrection den point := by
  have h := ladderOdd_kernel_overlap hmin hp hq
  obtain ⟨x, y⟩ := point
  dsimp only at h
  rcases h with h | h | h <;> ladder_rank

private theorem ladderOdd_rankCorrection_transverse {den : ℤ} (hmin : 4 ≤ den) {point : Site}
    (hp : point ∈ (BaseMask.ladderOdd.raw den).sites)
    (hq : point + (1 - den, den + 1) ∈ (BaseMask.ladderOdd.raw den).sites) :
    ladderOddRankCorrection den (point + (1 - den, den + 1)) = ladderOddRankCorrection den point := by
  have h := ladderOdd_transverse_overlap hp hq
  obtain ⟨x, y⟩ := point
  dsimp only at h
  rcases h with h | h
  · ladder_rank
  · by_cases hx : x = 2 * den <;> ladder_rank

/-- The raw B5 rank correction is constant on each modified deck class. -/
theorem ladderOdd_rankCorrection_class_constant {den : ℤ} (hden : BaseMask.ladderOdd.Valid den)
    {first second : Site} (hp : first ∈ (BaseMask.ladderOdd.raw den).sites)
    (hq : second ∈ (BaseMask.ladderOdd.raw den).sites)
    (hclass : second - first ∈ (reciprocalLadderDeck den).span) :
    ladderOddRankCorrection den second = ladderOddRankCorrection den first := by
  obtain ⟨i, j, hdiff⟩ := hclass
  have hshift : second = first + (reciprocalLadderDeck den).combine i j := by
    rw [← hdiff, add_comm first, sub_add_cancel]
  have hindex := ladderOdd_overlap_indices hden hp hq hshift
  rw [reciprocalLadderDeck_eq hden.2] at hshift
  rcases hindex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa [PeriodDeck.combine, show ((0, 0) : Site) = 0 from rfl] using
      congrArg (ladderOddRankCorrection den) hshift
  · have heq : second = first + (2 * den, 2) := by simpa [PeriodDeck.combine] using hshift
    simpa only [heq] using ladderOdd_rankCorrection_kernel hden.1 hp (heq ▸ hq)
  · have heq : first = second + (2 * den, 2) := by
      apply Prod.ext
      · have h := congrArg Prod.fst hshift
        dsimp [PeriodDeck.combine] at h ⊢
        omega
      · have h := congrArg Prod.snd hshift
        dsimp [PeriodDeck.combine] at h ⊢
        omega
    simpa only [heq] using (ladderOdd_rankCorrection_kernel hden.1 hq (heq ▸ hp)).symm
  · have heq : second = first + (1 - den, den + 1) := by simpa [PeriodDeck.combine, add_comm 1 den] using hshift
    simpa only [heq] using ladderOdd_rankCorrection_transverse hden.1 hp (heq ▸ hq)
  · have heq : first = second + (1 - den, den + 1) := by
      apply Prod.ext
      · have h := congrArg Prod.fst hshift
        dsimp [PeriodDeck.combine] at h ⊢
        omega
      · have h := congrArg Prod.snd hshift
        dsimp [PeriodDeck.combine] at h ⊢
        omega
    simpa only [heq] using (ladderOdd_rankCorrection_transverse hden.1 hq (heq ▸ hp)).symm

theorem ladderOdd_exists_periodic_rankCorrection {den : ℤ} (hden : BaseMask.ladderOdd.Valid den) :
    ∃ correction : Field, (∀ point ∈ (BaseMask.ladderOdd.raw den).sites,
      correction point = ladderOddRankCorrection den point) ∧
      ∀ step ∈ (reciprocalLadderDeck den).span, Function.Periodic correction step := by
  classical
  let deck := reciprocalLadderDeck den
  have hcover : deck.Covers (BaseMask.ladderOdd.raw den).sites := ladderOdd_raw_cover hden
  choose repr hmem hspan using hcover
  have hpos : 0 < deck.det := by
    apply Fraction.det_modifiedDeck_pos
    have := hden.1
    exact ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩
  have hclass (site : Site) : deck.classCode site = deck.classCode (repr site) :=
    (deck.classCode_eq_iff (ne_of_gt hpos) ..).mpr (hspan site)
  refine ⟨fun site => ladderOddRankCorrection den (repr site), ?_, ?_⟩
  · intro site hsite
    exact ladderOdd_rankCorrection_class_constant hden hsite (hmem site)
      ((deck.classCode_eq_iff (ne_of_gt hpos) ..).mp (hclass site).symm)
  · intro step hstep site
    have hshift : deck.classCode (site + step) = deck.classCode site :=
      (deck.classCode_eq_iff (ne_of_gt hpos) ..).mpr (by simpa only [add_sub_cancel_left] using hstep)
    exact ladderOdd_rankCorrection_class_constant hden (hmem site) (hmem (site + step))
      ((deck.classCode_eq_iff (ne_of_gt hpos) ..).mp ((hclass (site + step)).symm.trans (hshift.trans (hclass site))))

end FLatticePaper.Construction
