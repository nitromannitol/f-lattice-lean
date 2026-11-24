import FLatticePaper.Construction.StaircaseLaplacian
import FLatticePaper.Plane.Recurrence

namespace FLatticePaper.Construction

open Farey

/-- The source rank correction on the B1 mask, in the stated clause order. -/
def stairEvenRankCorrection (den : ℤ) (point : Site) : ℤ :=
  let parity := (point.1 + point.2) % 2
  if (point.1 = 0 ∧ point.2 = 0) ∨ (point.1 = den ∧ point.2 = 1) then 4
  else if (point.1 = den ∧ point.2 = 0) ∨ (point.1 = 1 ∧ point.2 = den + 1) then 5
  else if point.2 = 0 ∨ point.2 = den + 1 ∨ point.1 ≤ 0 then parity
  else if point.1 + point.2 ≤ den then 8 * (den - point.1) + parity
  else if point.1 + point.2 = den + 1 then 8
  else 1

local macro "staircase_rank" : tactic => `(tactic|
  (simp (disch := omega) only [stairEvenRankCorrection, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub, if_pos, if_neg]
   repeat' first | omega | (split <;> rename_i hclause <;>
     simp only [true_and, and_true, true_or, or_true, false_and, and_false, false_or, or_false,
       not_true_eq_false, not_false_eq_true] at hclause)))

private theorem rankCorrection_kernel {den : ℤ} (hden : BaseMask.stairEven.Valid den) {point : Site}
    (hp : point ∈ (BaseMask.stairEven.raw den).sites)
    (hq : point + (den, 1) ∈ (BaseMask.stairEven.raw den).sites) :
    stairEvenRankCorrection den (point + (den, 1)) = stairEvenRankCorrection den point := by
  have hmin := hden.1
  have hodd := hden.2
  obtain ⟨hx, hy, hs⟩ := BaseMask.mem_stairEven_raw_iff.mp hp
  obtain ⟨hx', hy', hs'⟩ := BaseMask.mem_stairEven_raw_iff.mp hq
  simp only [BaseMask.StairEvenCorner, Prod.fst_add, Prod.snd_add] at hx' hy' hs hs'
  by_cases hzero : point.1 = 0 ∧ point.2 = 0
  · staircase_rank
  · by_cases htop : point.1 = 2 - den ∧ point.2 = den
    · staircase_rank
    · have hsum : point.1 + point.2 = 1 := by omega
      staircase_rank

private theorem rankCorrection_transverse {den : ℤ} (hden : BaseMask.stairEven.Valid den) {point : Site}
    (hp : point ∈ (BaseMask.stairEven.raw den).sites)
    (hq : point + (1 - den, den + 1) ∈ (BaseMask.stairEven.raw den).sites) :
    stairEvenRankCorrection den (point + (1 - den, den + 1)) = stairEvenRankCorrection den point := by
  have hmin := hden.1
  have hodd := hden.2
  obtain ⟨hx, hy, _⟩ := BaseMask.mem_stairEven_raw_iff.mp hp
  obtain ⟨hx', hy', _⟩ := BaseMask.mem_stairEven_raw_iff.mp hq
  simp only [Prod.fst_add, Prod.snd_add] at hx' hy'
  have hy0 : point.2 = 0 := by omega
  by_cases hlast : point.1 = den
  · staircase_rank
  · staircase_rank

theorem stairEven_rankCorrection_class_constant {den : ℤ} (hden : BaseMask.stairEven.Valid den)
    {first second : Site} (hp : first ∈ (BaseMask.stairEven.raw den).sites)
    (hq : second ∈ (BaseMask.stairEven.raw den).sites)
    (hclass : second - first ∈ (reciprocalEvenDeck den).span) :
    stairEvenRankCorrection den second = stairEvenRankCorrection den first := by
  obtain ⟨i, j, hdiff⟩ := hclass
  have hshift : second = first + (reciprocalEvenDeck den).combine i j := by
    rw [← hdiff, add_comm first, sub_add_cancel]
  have hindex := stairEven_overlap_indices hden hp hq hshift
  rw [reciprocalEvenDeck_eq hden.2] at hshift
  rcases hindex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa [PeriodDeck.combine, show ((0, 0) : Site) = 0 from rfl] using
      congrArg (stairEvenRankCorrection den) hshift
  · have heq : second = first + (den, 1) := by simpa [PeriodDeck.combine] using hshift
    simpa only [heq] using rankCorrection_kernel hden hp (heq ▸ hq)
  · have heq : first = second + (den, 1) := by
      apply Prod.ext
      · have h := congrArg Prod.fst hshift
        dsimp [PeriodDeck.combine] at h ⊢
        omega
      · have h := congrArg Prod.snd hshift
        dsimp [PeriodDeck.combine] at h ⊢
        omega
    simpa only [heq] using (rankCorrection_kernel hden hq (heq ▸ hp)).symm
  · have heq : second = first + (1 - den, den + 1) := by
      simpa [PeriodDeck.combine, add_comm 1 den] using hshift
    simpa only [heq] using rankCorrection_transverse hden hp (heq ▸ hq)
  · have heq : first = second + (1 - den, den + 1) := by
      apply Prod.ext
      · have h := congrArg Prod.fst hshift
        dsimp [PeriodDeck.combine] at h ⊢
        omega
      · have h := congrArg Prod.snd hshift
        dsimp [PeriodDeck.combine] at h ⊢
        omega
    simpa only [heq] using (rankCorrection_transverse hden hq (heq ▸ hp)).symm

/-- The stated rank correction descends to every modified deck class. -/
theorem stairEven_exists_periodic_rankCorrection {den : ℤ} (hden : BaseMask.stairEven.Valid den) :
    ∃ correction : Field, (∀ point ∈ (BaseMask.stairEven.raw den).sites,
        correction point = stairEvenRankCorrection den point) ∧
      ∀ step ∈ (reciprocalEvenDeck den).span, Function.Periodic correction step := by
  classical
  let deck := reciprocalEvenDeck den
  have hcover : deck.Covers (BaseMask.stairEven.raw den).sites := stairEven_raw_cover hden
  choose repr hmem hspan using hcover
  have hpos : 0 < deck.det := by
    apply Fraction.det_modifiedDeck_pos
    have := hden.1
    exact ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩
  have hclass (site : Site) : deck.classCode site = deck.classCode (repr site) :=
    (deck.classCode_eq_iff (ne_of_gt hpos) ..).mpr (hspan site)
  refine ⟨fun site => stairEvenRankCorrection den (repr site), ?_, ?_⟩
  · intro site hsite
    exact stairEven_rankCorrection_class_constant hden hsite (hmem site)
      ((deck.classCode_eq_iff (ne_of_gt hpos) ..).mp (hclass site).symm)
  · intro step hstep site
    have hshift : deck.classCode (site + step) = deck.classCode site :=
      (deck.classCode_eq_iff (ne_of_gt hpos) ..).mpr (by simpa only [add_sub_cancel_left] using hstep)
    exact stairEven_rankCorrection_class_constant hden (hmem site) (hmem (site + step))
      ((deck.classCode_eq_iff (ne_of_gt hpos) ..).mp ((hclass (site + step)).symm.trans (hshift.trans (hclass site))))

local macro "staircase_mem" : tactic => `(tactic|
  (apply BaseMask.mem_stairEven_raw_iff.mpr
   simp only [BaseMask.StairEvenCorner, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
   omega))

private theorem stairEven_rank_on_raw_even {den : ℤ} (hden : BaseMask.stairEven.Valid den) {field correction : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (hcorrect : ∀ point ∈ (BaseMask.stairEven.raw den).sites, correction point = stairEvenRankCorrection den point)
    (hperiodic : ∀ step ∈ (reciprocalEvenDeck den).span, Function.Periodic correction step)
    (point : Site) (hpoint : point ∈ (BaseMask.stairEven.raw den).sites)
    (heven : EvenSite point) :
    let rank : Field := fun site => 6 * site.1 + correction site
    (laplacian field point = -1 ∧ rank (incomingNeg point) < rank point ∧ rank (incomingPos point) < rank point) ∨
      (laplacian field point = 0 ∧ (rank (incomingNeg point) < rank point ∨ rank (incomingPos point) < rank point))
  := by
  have hmin := hden.1
  have hodd := hden.2
  have hspanU : (den, 1) ∈ (reciprocalEvenDeck den).span := by
    rw [reciprocalEvenDeck_eq hodd]
    exact ⟨1, 0, by apply Prod.ext <;> simp [PeriodDeck.combine]⟩
  have hspanV : (1 - den, den + 1) ∈ (reciprocalEvenDeck den).span := by
    rw [reciprocalEvenDeck_eq hodd]
    exact ⟨0, 1, by apply Prod.ext <;> simp [PeriodDeck.combine, add_comm 1 den]⟩
  have hplus {step : Site} (hspan : step ∈ (reciprocalEvenDeck den).span) (site : Site)
      (hmem : site + step ∈ (BaseMask.stairEven.raw den).sites) :
      correction site = stairEvenRankCorrection den (site + step) :=
    (hperiodic step hspan site).symm.trans (hcorrect _ hmem)
  have hminus {step : Site} (hspan : step ∈ (reciprocalEvenDeck den).span) (site : Site)
      (hmem : site - step ∈ (BaseMask.stairEven.raw den).sites) :
      correction site = stairEvenRankCorrection den (site - step) := by
    have h := hperiodic step hspan (site - step)
    rw [sub_add_cancel] at h
    exact h.trans (hcorrect _ hmem)
  obtain ⟨x, y⟩ := point
  obtain ⟨hx, hy, hband⟩ := BaseMask.mem_stairEven_raw_iff.mp hpoint
  simp only [BaseMask.StairEvenCorner] at hband
  have hlap := stairEven_laplacian_on_raw hden hagree hperiod (x, y) hpoint
  dsimp only
  rw [hcorrect _ hpoint]
  have he : (x + y) % 2 = 0 := heven
  simp only [incomingNeg, incomingPos, if_pos heven] at hlap ⊢
  by_cases hblack : x = 1
  · subst x
    left
    refine ⟨by simpa using hlap, ?_, ?_⟩
    · have hmem : (1 - 1, y) ∈ (BaseMask.stairEven.raw den).sites := by staircase_mem
      rw [hcorrect _ hmem]
      by_cases hyLast : y = den <;> staircase_rank
    · have hmem : (1 + 1, y) ∈ (BaseMask.stairEven.raw den).sites := by staircase_mem
      rw [hcorrect _ hmem]
      by_cases hyLast : y = den <;> staircase_rank
  · right
    refine ⟨by simpa only [if_neg hblack] using hlap, ?_⟩
    by_cases hleft : x ≤ 0
    · left
      by_cases hcorner : x = 0 ∧ y = 0
      · have hmem : ((x - 1, y) : Site) + (den, 1) ∈ (BaseMask.stairEven.raw den).sites := by staircase_mem
        rw [hplus hspanU _ hmem]
        staircase_rank
      · by_cases hboundary : x = 2 - den ∧ y = den
        · have hmem : ((x - 1, y) : Site) + (den, 1) ∈ (BaseMask.stairEven.raw den).sites := by staircase_mem
          rw [hplus hspanU _ hmem]
          staircase_rank
        · have hmem : (x - 1, y) ∈ (BaseMask.stairEven.raw den).sites := by staircase_mem
          rw [hcorrect _ hmem]
          staircase_rank
    · by_cases hend : y = 0 ∨ y = den + 1 ∨ (x = den ∧ y = 1)
      · left
        have hmem : (x - 1, y) ∈ (BaseMask.stairEven.raw den).sites := by staircase_mem
        rw [hcorrect _ hmem]
        rcases hend with hb | ht | hd <;> staircase_rank
      · right
        have hmem : (x + 1, y) ∈ (BaseMask.stairEven.raw den).sites := by staircase_mem
        rw [hcorrect _ hmem]
        by_cases hdiag : x + y = den + 1 <;> staircase_rank


private theorem stairEven_rank_on_raw_odd_black {den : ℤ} (hden : BaseMask.stairEven.Valid den) {field correction : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (hcorrect : ∀ point ∈ (BaseMask.stairEven.raw den).sites, correction point = stairEvenRankCorrection den point)
    (hperiodic : ∀ step ∈ (reciprocalEvenDeck den).span, Function.Periodic correction step)
    (point : Site) (hpoint : point ∈ (BaseMask.stairEven.raw den).sites)
    (heven : ¬ EvenSite point)
    (hb : 0 < point.2 ∧ point.2 < den + 1 ∧ 1 < point.1 + point.2 ∧ point.1 + point.2 < den + 2) :
    let rank : Field := fun site => 6 * site.1 + correction site
    (laplacian field point = -1 ∧ rank (incomingNeg point) < rank point ∧ rank (incomingPos point) < rank point) ∨
      (laplacian field point = 0 ∧ (rank (incomingNeg point) < rank point ∨ rank (incomingPos point) < rank point))
  := by
  have hmin := hden.1
  have hodd := hden.2
  have hspanU : (den, 1) ∈ (reciprocalEvenDeck den).span := by
    rw [reciprocalEvenDeck_eq hodd]
    exact ⟨1, 0, by apply Prod.ext <;> simp [PeriodDeck.combine]⟩
  have hspanV : (1 - den, den + 1) ∈ (reciprocalEvenDeck den).span := by
    rw [reciprocalEvenDeck_eq hodd]
    exact ⟨0, 1, by apply Prod.ext <;> simp [PeriodDeck.combine, add_comm 1 den]⟩
  have hplus {step : Site} (hspan : step ∈ (reciprocalEvenDeck den).span) (site : Site)
      (hmem : site + step ∈ (BaseMask.stairEven.raw den).sites) :
      correction site = stairEvenRankCorrection den (site + step) :=
    (hperiodic step hspan site).symm.trans (hcorrect _ hmem)
  have hminus {step : Site} (hspan : step ∈ (reciprocalEvenDeck den).span) (site : Site)
      (hmem : site - step ∈ (BaseMask.stairEven.raw den).sites) :
      correction site = stairEvenRankCorrection den (site - step) := by
    have h := hperiodic step hspan (site - step)
    rw [sub_add_cancel] at h
    exact h.trans (hcorrect _ hmem)
  obtain ⟨x, y⟩ := point
  obtain ⟨hx, hy, hband⟩ := BaseMask.mem_stairEven_raw_iff.mp hpoint
  simp only [BaseMask.StairEvenCorner] at hband
  have hlap := stairEven_laplacian_on_raw hden hagree hperiod (x, y) hpoint
  dsimp only
  rw [hcorrect _ hpoint]
  have he : (x + y) % 2 ≠ 0 := heven
  simp only [incomingNeg, incomingPos, if_neg heven] at hlap ⊢
  have hblack : 0 < y ∧ y < den + 1 ∧ 1 < x + y ∧ x + y < den + 2 := hb
  · left
    refine ⟨by simpa only [if_pos hblack] using hlap, ?_, ?_⟩
    · have hmem : (x, y - 1) ∈ (BaseMask.stairEven.raw den).sites := by staircase_mem
      rw [hcorrect _ hmem]
      by_cases hcol : x ≤ 0
      · staircase_rank
      · by_cases hrow : y = 1 <;> staircase_rank
    · have hmem : (x, y + 1) ∈ (BaseMask.stairEven.raw den).sites := by staircase_mem
      rw [hcorrect _ hmem]
      by_cases hcol : x ≤ 0
      · staircase_rank
      · by_cases hdiag : x + y = den <;> staircase_rank

private theorem stairEven_rank_on_raw_odd_white {den : ℤ} (hden : BaseMask.stairEven.Valid den) {field correction : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (hcorrect : ∀ point ∈ (BaseMask.stairEven.raw den).sites, correction point = stairEvenRankCorrection den point)
    (hperiodic : ∀ step ∈ (reciprocalEvenDeck den).span, Function.Periodic correction step)
    (point : Site) (hpoint : point ∈ (BaseMask.stairEven.raw den).sites)
    (heven : ¬ EvenSite point)
    (hw : ¬ (0 < point.2 ∧ point.2 < den + 1 ∧ 1 < point.1 + point.2 ∧ point.1 + point.2 < den + 2)) :
    let rank : Field := fun site => 6 * site.1 + correction site
    (laplacian field point = -1 ∧ rank (incomingNeg point) < rank point ∧ rank (incomingPos point) < rank point) ∨
      (laplacian field point = 0 ∧ (rank (incomingNeg point) < rank point ∨ rank (incomingPos point) < rank point))
  := by
  have hmin := hden.1
  have hodd := hden.2
  have hspanU : (den, 1) ∈ (reciprocalEvenDeck den).span := by
    rw [reciprocalEvenDeck_eq hodd]
    exact ⟨1, 0, by apply Prod.ext <;> simp [PeriodDeck.combine]⟩
  have hspanV : (1 - den, den + 1) ∈ (reciprocalEvenDeck den).span := by
    rw [reciprocalEvenDeck_eq hodd]
    exact ⟨0, 1, by apply Prod.ext <;> simp [PeriodDeck.combine, add_comm 1 den]⟩
  have hplus {step : Site} (hspan : step ∈ (reciprocalEvenDeck den).span) (site : Site)
      (hmem : site + step ∈ (BaseMask.stairEven.raw den).sites) :
      correction site = stairEvenRankCorrection den (site + step) :=
    (hperiodic step hspan site).symm.trans (hcorrect _ hmem)
  have hminus {step : Site} (hspan : step ∈ (reciprocalEvenDeck den).span) (site : Site)
      (hmem : site - step ∈ (BaseMask.stairEven.raw den).sites) :
      correction site = stairEvenRankCorrection den (site - step) := by
    have h := hperiodic step hspan (site - step)
    rw [sub_add_cancel] at h
    exact h.trans (hcorrect _ hmem)
  obtain ⟨x, y⟩ := point
  obtain ⟨hx, hy, hband⟩ := BaseMask.mem_stairEven_raw_iff.mp hpoint
  simp only [BaseMask.StairEvenCorner] at hband
  have hlap := stairEven_laplacian_on_raw hden hagree hperiod (x, y) hpoint
  dsimp only
  rw [hcorrect _ hpoint]
  have he : (x + y) % 2 ≠ 0 := heven
  simp only [incomingNeg, incomingPos, if_neg heven] at hlap ⊢
  have hblack : ¬ (0 < y ∧ y < den + 1 ∧ 1 < x + y ∧ x + y < den + 2) := hw
  · right
    refine ⟨by simpa only [if_neg hblack] using hlap, ?_⟩
    by_cases hbottom : y = 0
    · by_cases hend : x = den
      · right
        have hmem : (x, y + 1) ∈ (BaseMask.stairEven.raw den).sites := by staircase_mem
        rw [hcorrect _ hmem]
        staircase_rank
      · left
        have hmem : ((x, y - 1) : Site) + (1 - den, den + 1) ∈ (BaseMask.stairEven.raw den).sites := by staircase_mem
        rw [hplus hspanV _ hmem]
        staircase_rank
    · by_cases htop : y = den + 1
      · by_cases hend : x = 1
        · right
          have hmem : ((x, y + 1) : Site) - (1 - den, den + 1) ∈ (BaseMask.stairEven.raw den).sites := by staircase_mem
          rw [hminus hspanV _ hmem]
          staircase_rank
        · left
          have hmem : (x, y - 1) ∈ (BaseMask.stairEven.raw den).sites := by staircase_mem
          rw [hcorrect _ hmem]
          staircase_rank
      · right
        by_cases hlower : x + y = 1
        · have hmem : (x, y + 1) ∈ (BaseMask.stairEven.raw den).sites := by staircase_mem
          rw [hcorrect _ hmem]
          staircase_rank
        · by_cases hend : y = den
          · have hmem : (x, y + 1) ∈ (BaseMask.stairEven.raw den).sites := by staircase_mem
            rw [hcorrect _ hmem]
            staircase_rank
          · have hmem : ((x, y + 1) : Site) - (den, 1) ∈ (BaseMask.stairEven.raw den).sites := by staircase_mem
            rw [hminus hspanU _ hmem]
            staircase_rank

private theorem stairEven_rank_on_raw {den : ℤ} (hden : BaseMask.stairEven.Valid den) {field correction : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (hcorrect : ∀ point ∈ (BaseMask.stairEven.raw den).sites, correction point = stairEvenRankCorrection den point)
    (hperiodic : ∀ step ∈ (reciprocalEvenDeck den).span, Function.Periodic correction step)
    (point : Site) (hpoint : point ∈ (BaseMask.stairEven.raw den).sites) :
    let rank : Field := fun site => 6 * site.1 + correction site
    (laplacian field point = -1 ∧ rank (incomingNeg point) < rank point ∧ rank (incomingPos point) < rank point) ∨
      (laplacian field point = 0 ∧ (rank (incomingNeg point) < rank point ∨ rank (incomingPos point) < rank point)) := by
  by_cases heven : EvenSite point
  · exact stairEven_rank_on_raw_even hden hagree hperiod hcorrect hperiodic point hpoint heven
  · by_cases hb : 0 < point.2 ∧ point.2 < den + 1 ∧ 1 < point.1 + point.2 ∧ point.1 + point.2 < den + 2
    · exact stairEven_rank_on_raw_odd_black hden hagree hperiod hcorrect hperiodic point hpoint heven hb
    · exact stairEven_rank_on_raw_odd_white hden hagree hperiod hcorrect hperiodic point hpoint heven hb


/-- The explicit B1 rank from the replacement recurrence proof works at every
site of the compatible literal height extension, including both seams. -/
theorem stairEven_exists_burningRank {den : ℤ} (hden : BaseMask.stairEven.Valid den) {field : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den)) :
    ∃ correction : Field,
      (∀ point ∈ (BaseMask.stairEven.raw den).sites, correction point = stairEvenRankCorrection den point) ∧
      (∀ step ∈ (reciprocalEvenDeck den).span, Function.Periodic correction step) ∧
      IsBurningRank field (fun point => 6 * point.1 + correction point) := by
  obtain ⟨correction, hcorrect, hperiodic⟩ := stairEven_exists_periodic_rankCorrection hden
  let fraction := Fraction.mk 1 den
  have hinterval : fraction.InUnitInterval := by
    have := hden.1
    exact ⟨by dsimp [fraction]; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp [fraction]; omega⟩
  refine ⟨correction, hcorrect, hperiodic, ?_⟩
  intro point
  obtain ⟨site, hsite, hspan⟩ := stairEven_raw_cover hden point
  let step := point - site
  have hpoint : site + step = point := by dsimp [step]; rw [add_comm, sub_add_cancel]
  have heven : EvenSite step := ((fraction.mem_modifiedDeck_iff step).mp hspan).2
  rw [← hpoint, laplacian_periodic_of_generatorPeriods hinterval hperiod hspan site,
    incomingNeg_add_of_even site step heven, incomingPos_add_of_even site step heven]
  simp only [hperiodic step hspan site, hperiodic step hspan (incomingNeg site),
    hperiodic step hspan (incomingPos site), Prod.fst_add]
  have hlocal := stairEven_rank_on_raw hden hagree hperiod hcorrect hperiodic site hsite
  rcases hlocal with ⟨h, hn, hp⟩ | ⟨h, hn | hp⟩
  · exact Or.inl ⟨h, by dsimp at hn; omega, by dsimp at hp; omega⟩
  · exact Or.inr ⟨h, Or.inl (by dsimp at hn; omega)⟩
  · exact Or.inr ⟨h, Or.inr (by dsimp at hp; omega)⟩

/-- The raw reciprocal standard initializer is the restriction of a recurrent
plane height with the prescribed periods and growth. -/
theorem stairEven_exists_recurrent_extension {den : ℤ} (hden : BaseMask.stairEven.Valid den) :
    ∃ field : Field, (BaseMask.stairEven.raw den).Agrees field 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den) ∧
      HasQuadraticGrowth field (Fraction.mk 1 den).matrix ∧ Superharmonic field ∧ Recurrent field := by
  obtain ⟨field, hagree, hperiod, hgrowth⟩ := stairEven_exists_extension hden
  obtain ⟨_, _, _, hrank⟩ := stairEven_exists_burningRank hden hagree hperiod
  exact ⟨field, hagree, hperiod, hgrowth, hrank.superharmonic, hrank.recurrent⟩

/-- The native even standard at the empty word extends to the recurrent
reciprocal staircase at slope `1/3`. -/
theorem evaluateNative_empty_even_standard_recurrent :
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative [] = .ok registers ∧ registers.standard.currentEven.val.Agrees field 0 ∧
      HasGeneratorPeriods ((parentsAt []).current .even) field 0 (stairEvenConstantV 3) ∧
      HasQuadraticGrowth field ((parentsAt []).current .even).matrix ∧
      Superharmonic field ∧ Recurrent field := by
  have hvalid : BaseMask.stairEven.Valid 3 := by simp [BaseMask.Valid]
  obtain ⟨field, hagree, hperiod, hgrowth, hsuper, hrec⟩ := stairEven_exists_recurrent_extension hvalid
  exact ⟨BaseRun.empty.registers.llCenter, field, evaluateNative_base .empty,
    BaseMask.stairEven_llCenter_agrees hvalid hagree, hperiod, hgrowth, hsuper, hrec⟩

/-- The native even standard at every nonempty pure-3 run has literal height
agreement with its recurrent extension in the constructor's centered frame. -/
theorem evaluateNative_threes_even_standard_recurrent (extra : ℕ) :
    let word := (BaseRun.threes extra).word
    let fraction := (parentsAt word).current .even
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative word = .ok registers ∧ registers.standard.currentEven.val.Agrees field 0 ∧
      HasGeneratorPeriods fraction field 0 (stairEvenConstantV (2 * (extra : ℤ) + 3 + 2)) ∧
      HasQuadraticGrowth field fraction.matrix ∧ Superharmonic field ∧ Recurrent field := by
  dsimp only
  rw [threes_current_even]
  have hvalid : BaseMask.stairEven.Valid (2 * (extra : ℤ) + 3 + 2) := by
    change 3 ≤ 2 * (extra : ℤ) + 3 + 2 ∧ (2 * (extra : ℤ) + 3 + 2) % 2 = 1
    omega
  obtain ⟨field, hagree, hperiod, hgrowth, hsuper, hrec⟩ := stairEven_exists_recurrent_extension hvalid
  exact ⟨(BaseRun.threes extra).registers.llCenter, field, evaluateNative_base _,
    BaseMask.stairEven_llCenter_agrees hvalid hagree, hperiod, hgrowth, hsuper, hrec⟩

end FLatticePaper.Construction
