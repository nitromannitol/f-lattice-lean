import FLatticePaper.Construction.AlternateStaircaseExtension

namespace FLatticePaper.Construction

open Farey

abbrev StairEvenAltLeftHigh (den : ℤ) (point : Site) : Prop :=
  0 ≤ point.2 ∧ point.2 ≤ den - 1 ∧ 2 - den ≤ point.1 ∧ point.1 ≤ 0 ∧ point.1 + point.2 ≤ 1

abbrev StairEvenAltRightHigh (den : ℤ) (point : Site) : Prop :=
  1 ≤ point.2 ∧ point.2 ≤ den ∧ 2 ≤ point.1

/-- The rank correction on the raw B3 mask, in the order of formula (7). -/
def stairEvenAltRankCorrection (den : ℤ) (point : Site) : ℤ :=
  let parity := (point.1 + point.2) % 2
  if (point.1 = 1 - den ∧ point.2 = 0) ∨ (point.1 = 1 ∧ point.2 = 1) then 8 * den
  else if point.1 = 3 ∧ point.2 = den then 8 * den - 12
  else if point.1 + point.2 = 2 ∧ 2 ≤ point.2 ∧ point.2 ≤ den - 1 then 8 * point.2 - 4
  else if StairEvenAltLeftHigh den point then 8 * (1 - point.1) + parity
  else if StairEvenAltRightHigh den point then 8 * (den + 1 - point.1) + parity
  else parity

local macro "alternate_staircase_rank" : tactic => `(tactic|
  (simp (disch := omega) only [stairEvenAltRankCorrection, StairEvenAltLeftHigh,
      StairEvenAltRightHigh, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      if_pos, if_neg]
   repeat' first | omega | (split <;> rename_i hclause <;>
     simp only [true_and, and_true, true_or, or_true, false_and, and_false, false_or, or_false,
       not_true_eq_false, not_false_eq_true] at hclause)))

local macro "alternate_staircase_mem" : tactic => `(tactic|
  (apply BaseMask.mem_stairEvenAlt_raw_iff.mpr
   simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
   omega))

set_option maxHeartbeats 800000 in
private theorem stairEvenAlt_rankCorrection_add_kernel {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {point : Site} (hp : point ∈ (BaseMask.stairEvenAlt.raw den).sites)
    (hq : point + (den, 1) ∈ (BaseMask.stairEvenAlt.raw den).sites) :
    stairEvenAltRankCorrection den (point + (den, 1)) = stairEvenAltRankCorrection den point := by
  have ⟨hmin, hodd⟩ := hden
  obtain ⟨x, y⟩ := point
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_stairEvenAlt_raw_iff.mp hp
  obtain ⟨hx', hy', hshape'⟩ := BaseMask.mem_stairEvenAlt_raw_iff.mp hq
  simp only [Prod.fst_add, Prod.snd_add] at hx hy hshape hx' hy' hshape'
  by_cases hb : y = -1
  · have hrange : 1 - den ≤ x ∧ x ≤ 0 := by omega
    clear hshape hshape'
    alternate_staircase_rank
  · by_cases hb' : y = 0
    · have hrange : 1 - den ≤ x ∧ x ≤ 0 := by omega
      clear hshape hshape'
      by_cases hc : x = 1 - den <;> alternate_staircase_rank
    · by_cases ht : y = den
      · have hrange : 4 - 2 * den ≤ x ∧ x ≤ 3 - den := by omega
        clear hshape hshape'
        alternate_staircase_rank
      · by_cases hc : y = den - 1 ∧ x = 3 - den
        · alternate_staircase_rank
        · have hrange : 1 ≤ y ∧ y ≤ den - 1 ∧ 2 - den ≤ x + y ∧ x + y ≤ 1 := by omega
          clear hshape hshape'
          by_cases hxleft : 2 - den ≤ x <;> alternate_staircase_rank

private theorem stairEvenAlt_rankCorrection_of_level_eq_of_row_le {den : ℤ}
    (hden : BaseMask.stairEvenAlt.Valid den) {first second : Site}
    (hp : first ∈ (BaseMask.stairEvenAlt.raw den).sites)
    (hq : second ∈ (BaseMask.stairEvenAlt.raw den).sites)
    (hlevel : staircaseLevel den first = staircaseLevel den second) (hrow : first.2 ≤ second.2) :
    stairEvenAltRankCorrection den second = stairEvenAltRankCorrection den first := by
  have hmin := hden.1
  obtain ⟨x, y⟩ := first
  obtain ⟨z, w⟩ := second
  obtain ⟨hx, hy, hpShape⟩ := BaseMask.mem_stairEvenAlt_raw_iff.mp hp
  obtain ⟨hz, hw, hqShape⟩ := BaseMask.mem_stairEvenAlt_raw_iff.mp hq
  dsimp only [staircaseLevel] at hlevel
  dsimp only at hrow hx hy hpShape hz hw hqShape
  have hsum : z + w = x + y + (den + 1) * (w - y) := by linear_combination -hlevel
  have hpSum : -den ≤ x + y ∧ x + y ≤ den + 4 := by omega
  have hqSum : -den ≤ z + w ∧ z + w ≤ den + 4 := by omega
  have hgap : w - y ≤ 2 := by
    by_contra! hbig
    have hmul := mul_le_mul_of_nonneg_left (show 3 ≤ w - y by omega)
      (show 0 ≤ den + 1 by omega)
    linarith
  have hnoTwo : w - y ≠ 2 := by
    intro htwo
    have hstart : x + y ≤ 2 - den := by rw [htwo] at hsum; omega
    have hcol : z = x + 2 * den := by
      linear_combination -hlevel + den * htwo
    by_cases hsmall : x + y ≤ 1 - den
    · have hleft : 1 - den ≤ x := by omega
      omega
    · have hlast : z + w = den + 4 := by rw [htwo] at hsum; omega
      have hright : z = 3 := by omega
      omega
  have hcases : w - y = 0 ∨ w - y = 1 := by omega
  rcases hcases with hzero | hone
  · have hcol : z = x := by linear_combination -hlevel + den * hzero
    have hrowEq : w = y := by omega
    subst z
    subst w
    rfl
  · have hcol : z = x + den := by linear_combination -hlevel + den * hone
    have hrowEq : w = y + 1 := by omega
    subst z
    subst w
    exact stairEvenAlt_rankCorrection_add_kernel hden hp hq

private theorem stairEvenAlt_rankCorrection_of_level_eq {den : ℤ}
    (hden : BaseMask.stairEvenAlt.Valid den) {first second : Site}
    (hp : first ∈ (BaseMask.stairEvenAlt.raw den).sites)
    (hq : second ∈ (BaseMask.stairEvenAlt.raw den).sites)
    (hlevel : staircaseLevel den first = staircaseLevel den second) :
    stairEvenAltRankCorrection den second = stairEvenAltRankCorrection den first := by
  rcases le_total first.2 second.2 with h | h
  · exact stairEvenAlt_rankCorrection_of_level_eq_of_row_le hden hp hq hlevel h
  · exact (stairEvenAlt_rankCorrection_of_level_eq_of_row_le hden hq hp hlevel.symm h).symm

private theorem stairEvenAlt_rankCorrection_of_level_drop {den : ℤ}
    (hden : BaseMask.stairEvenAlt.Valid den) {first second : Site}
    (hp : first ∈ (BaseMask.stairEvenAlt.raw den).sites)
    (hq : second ∈ (BaseMask.stairEvenAlt.raw den).sites) {index : ℤ}
    (hstep : staircaseLevel den second =
      staircaseLevel den first - (Fraction.mk 1 den).periodDenominator * index)
    (horder : staircaseLevel den second ≤ staircaseLevel den first) :
    stairEvenAltRankCorrection den second = stairEvenAltRankCorrection den first := by
  have ⟨hmin, hodd⟩ := hden
  let T := (Fraction.mk 1 den).periodDenominator
  have hT : den - 3 < T := by
    dsimp [T, Fraction.periodDenominator]
    nlinarith only [hmin, sq_nonneg den]
  have hTpos : 0 < T := by omega
  have hpBounds := stairEvenAlt_level_bounds hmin hp
  have hqBounds := stairEvenAlt_level_bounds hmin hq
  change 3 - T ≤ staircaseLevel den first ∧ staircaseLevel den first ≤ den at hpBounds
  change 3 - T ≤ staircaseLevel den second ∧ staircaseLevel den second ≤ den at hqBounds
  change staircaseLevel den second = staircaseLevel den first - T * index at hstep
  have hlo : 0 ≤ index := by
    by_contra! hneg
    have hmul := mul_neg_of_pos_of_neg hTpos hneg
    omega
  have hhi : index ≤ 1 := by
    by_contra! hbig
    have hmul := mul_le_mul_of_nonneg_left (show 2 ≤ index by omega) hTpos.le
    omega
  rcases (show index = 0 ∨ index = 1 by omega) with rfl | rfl
  · exact stairEvenAlt_rankCorrection_of_level_eq hden hp hq (by omega)
  · let s := staircaseLevel den first
    have hsLo : 3 ≤ s := by dsimp only [s]; omega
    have hsHi : s ≤ den := hpBounds.2
    have hup : (s, 0) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
    have hdown : (s + 1 - den, den + 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by
      apply BaseMask.mem_stairEvenAlt_raw_iff.mpr
      refine ⟨⟨?_, ?_⟩, ⟨?_, le_rfl⟩, Or.inr (Or.inr (Or.inl ⟨rfl, ?_, ?_⟩))⟩ <;>
        dsimp only <;> omega
    have hlevel : staircaseLevel den (s + 1 - den, den + 1) = staircaseLevel den second := by
      rw [hstep]
      change staircaseLevel den (s + 1 - den, den + 1) = s - T * 1
      simp only [staircaseLevel, T, Fraction.periodDenominator]
      ring
    calc
      stairEvenAltRankCorrection den second = stairEvenAltRankCorrection den (s + 1 - den, den + 1) :=
        stairEvenAlt_rankCorrection_of_level_eq hden hdown hq hlevel
      _ = stairEvenAltRankCorrection den (s, 0) := by alternate_staircase_rank
      _ = stairEvenAltRankCorrection den first :=
        stairEvenAlt_rankCorrection_of_level_eq hden hp hup (by simp [staircaseLevel, s])

/-- The raw rank correction is constant on each modified deck class. -/
theorem stairEvenAlt_rankCorrection_class_constant {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {first second : Site} (hp : first ∈ (BaseMask.stairEvenAlt.raw den).sites)
    (hq : second ∈ (BaseMask.stairEvenAlt.raw den).sites)
    (hclass : second - first ∈ (reciprocalEvenDeck den).span) :
    stairEvenAltRankCorrection den second = stairEvenAltRankCorrection den first := by
  let fraction := Fraction.mk 1 den
  obtain ⟨i, j, hdiff⟩ := hclass
  change second - first = fraction.modifiedDeck.combine i j at hdiff
  have hgrade := Fraction.transverseGrade_combine fraction (fraction.periodMultiplicity * i) j
  rw [← Fraction.modifiedDeck_combine, ← hdiff] at hgrade
  change den * (second.2 - first.2) - 1 * (second.1 - first.1) =
    fraction.periodDenominator * j at hgrade
  have hstep : staircaseLevel den second =
      staircaseLevel den first - fraction.periodDenominator * j := by
    simp only [staircaseLevel]
    linear_combination -hgrade
  rcases le_total (staircaseLevel den second) (staircaseLevel den first) with h | h
  · exact stairEvenAlt_rankCorrection_of_level_drop hden hp hq hstep h
  · symm
    apply stairEvenAlt_rankCorrection_of_level_drop hden hq hp (index := -j) _ h
    linear_combination -hstep

/-- The source B3 correction admits a periodic extension to the entire plane. -/
theorem stairEvenAlt_exists_periodic_rankCorrection {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den) :
    ∃ correction : Field, (∀ point ∈ (BaseMask.stairEvenAlt.raw den).sites,
      correction point = stairEvenAltRankCorrection den point) ∧
      ∀ step ∈ (reciprocalEvenDeck den).span, Function.Periodic correction step := by
  classical
  let deck := reciprocalEvenDeck den
  have hcover : deck.Covers (BaseMask.stairEvenAlt.raw den).sites := stairEvenAlt_raw_cover hden
  choose repr hmem hspan using hcover
  have hpos : 0 < deck.det := by
    apply Fraction.det_modifiedDeck_pos
    have := hden.1
    exact ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩
  have hclass (site : Site) : deck.classCode site = deck.classCode (repr site) :=
    (deck.classCode_eq_iff (ne_of_gt hpos) ..).mpr (hspan site)
  refine ⟨fun site => stairEvenAltRankCorrection den (repr site), ?_, ?_⟩
  · intro site hsite
    exact stairEvenAlt_rankCorrection_class_constant hden hsite (hmem site)
      ((deck.classCode_eq_iff (ne_of_gt hpos) ..).mp (hclass site).symm)
  · intro step hstep site
    have hshift : deck.classCode (site + step) = deck.classCode site :=
      (deck.classCode_eq_iff (ne_of_gt hpos) ..).mpr (by simpa only [add_sub_cancel_left] using hstep)
    exact stairEvenAlt_rankCorrection_class_constant hden (hmem site) (hmem (site + step))
      ((deck.classCode_eq_iff (ne_of_gt hpos) ..).mp ((hclass (site + step)).symm.trans (hshift.trans (hclass site))))

end FLatticePaper.Construction
