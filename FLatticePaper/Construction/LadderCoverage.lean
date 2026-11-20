import FLatticePaper.Construction.StaircaseCoverage

namespace FLatticePaper.Construction

open Farey

def reciprocalLadderDeck (den : ℤ) : PeriodDeck :=
  (Fraction.mk 1 den).modifiedDeck

theorem reciprocalLadderDeck_eq {den : ℤ} (heven : den % 2 = 0) :
    reciprocalLadderDeck den = ⟨(2 * den, 2), (1 - den, 1 + den)⟩ := by
  have hodd : (1 + den) % 2 ≠ 0 := by omega
  simp [reciprocalLadderDeck, Fraction.modifiedDeck, Fraction.periodMultiplicity,
    Fraction.unmodifiedDeck, hodd]

private theorem reciprocalLadderDeck_pos {den : ℤ} (hden : 4 ≤ den) :
    0 < (reciprocalLadderDeck den).det :=
  Fraction.det_modifiedDeck_pos (fraction := ⟨1, den⟩)
    ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩

private theorem ladder_cell_bounds {den : ℤ} {point : Site} (hden : 4 ≤ den)
    (heven : den % 2 = 0) (hcell : (reciprocalLadderDeck den).InHalfShiftedCell point) :
    (2 - den ≤ point.1 ∧ point.1 ≤ 2 * den) ∧ (0 ≤ point.2 ∧ point.2 ≤ den + 2) ∧
    (1 ≤ point.1 + point.2 ∧ point.1 + point.2 ≤ 2 * den + 3) ∧
    (point.2 = 0 → point.1 < den) ∧ (point.2 = den + 2 → 2 < point.1) ∧
    (point.1 = 2 * den → point.2 = 2) := by
  rw [reciprocalLadderDeck_eq heven] at hcell
  obtain ⟨u, v, hu0, hu1, hv0, hv1, hcol, hrow⟩ := hcell
  change (point.1 : ℝ) = 1 / 2 + u * ((2 * den : ℤ) : ℝ) + v * ((1 - den : ℤ) : ℝ) at hcol
  change (point.2 : ℝ) = -(1 / 2) + u * 2 + v * ((1 + den : ℤ) : ℝ) at hrow
  push_cast at hcol hrow
  have hd : (4 : ℝ) ≤ (den : ℝ) := by exact_mod_cast hden
  have hux := mul_nonneg hu0 (by linarith : 0 ≤ 2 * (den : ℝ))
  have huv := mul_nonneg (by linarith : 0 ≤ 1 - u) (by linarith : 0 ≤ 2 * (den : ℝ))
  have hvx := mul_nonneg hv0 (by linarith : 0 ≤ (den : ℝ) - 1)
  have hvv := mul_nonneg (by linarith : 0 ≤ 1 - v) (by linarith : 0 ≤ (den : ℝ) - 1)
  have hvy := mul_nonneg hv0 (by linarith : 0 ≤ 1 + (den : ℝ))
  have hvw := mul_nonneg (by linarith : 0 ≤ 1 - v) (by linarith : 0 ≤ 1 + (den : ℝ))
  have hcolLo : ((1 - den : ℤ) : ℝ) < (point.1 : ℝ) := by
    push_cast
    nlinarith only [hcol, hux, hvv]
  have hcolHi : (point.1 : ℝ) < ((2 * den + 1 : ℤ) : ℝ) := by
    push_cast
    nlinarith only [hcol, huv, hvx]
  have hrowLo : ((-1 : ℤ) : ℝ) < (point.2 : ℝ) := by
    push_cast
    linarith only [hrow, hu0, hvy]
  have hrowHi : (point.2 : ℝ) < ((den + 3 : ℤ) : ℝ) := by
    push_cast
    nlinarith only [hrow, hu1, hvw]
  have hsum : (point.1 : ℝ) + (point.2 : ℝ) = u * (2 * (den : ℝ) + 2) + 2 * v := by
    rw [hcol, hrow]
    ring
  have hsumLo : (0 : ℝ) < (point.1 : ℝ) + (point.2 : ℝ) := by
    by_contra! h
    have hmul := mul_nonneg hu0 (by linarith : 0 ≤ 2 * (den : ℝ) + 2)
    have hv : v = 0 := by linarith only [hsum, h, hmul, hv0]
    have hu : u = 0 := by
      have hzero : u * (2 * (den : ℝ) + 2) = 0 := by linarith only [hsum, hmul, h, hv]
      exact (mul_eq_zero.mp hzero).resolve_right (by linarith)
    have hhalf : (2 : ℝ) * (point.1 : ℝ) = 1 := by rw [hu, hv] at hcol; linarith
    have hhalfInt : (2 : ℤ) * point.1 = 1 := by exact_mod_cast hhalf
    omega
  have hsumHi : (point.1 : ℝ) + (point.2 : ℝ) < ((2 * den + 4 : ℤ) : ℝ) := by
    have hker := mul_lt_mul_of_pos_right hu1 (by linarith : 0 < 2 * (den : ℝ) + 2)
    push_cast
    linarith only [hsum, hker, hv1]
  have hxLo : 1 - den < point.1 := by exact_mod_cast hcolLo
  have hxHi : point.1 < 2 * den + 1 := by exact_mod_cast hcolHi
  have hyLo : -1 < point.2 := by exact_mod_cast hrowLo
  have hyHi : point.2 < den + 3 := by exact_mod_cast hrowHi
  have hsLo : 0 < point.1 + point.2 := by exact_mod_cast hsumLo
  have hsHi : point.1 + point.2 < 2 * den + 4 := by exact_mod_cast hsumHi
  refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_, ?_, ?_⟩
  · intro hbottom
    have hbottomR : (point.2 : ℝ) = 0 := by exact_mod_cast hbottom
    have huSmall : u ≤ 1 / 4 := by linarith only [hbottomR, hrow, hvy]
    have hbound := mul_nonneg (sub_nonneg.mpr huSmall) (by linarith : 0 ≤ 2 * (den : ℝ))
    have h : (point.1 : ℝ) < (den : ℝ) := by nlinarith only [hd, hcol, hvx, hbound]
    exact_mod_cast h
  · intro htop
    have htopR : (point.2 : ℝ) = (den : ℝ) + 2 := by exact_mod_cast htop
    have huBig : 3 / 4 ≤ u := by nlinarith only [htopR, hrow, hvw]
    have hbound := mul_nonneg (sub_nonneg.mpr huBig) (by linarith : 0 ≤ 2 * (den : ℝ))
    have h : (2 : ℝ) < (point.1 : ℝ) := by nlinarith only [hd, hcol, hvv, hbound]
    exact_mod_cast h
  · intro hright
    have hrightR : (point.1 : ℝ) = 2 * (den : ℝ) := by exact_mod_cast hright
    have hvBound : v * ((den : ℝ) - 1) ≤ 1 / 2 := by nlinarith only [hrightR, hcol, huv]
    have huBig : 3 / 4 < u := by
      by_contra! huSmall
      have hbound := mul_nonneg (sub_nonneg.mpr huSmall) (by linarith : 0 ≤ 2 * (den : ℝ))
      nlinarith only [hd, hrightR, hcol, hvx, hbound]
    have hvBound' : v * (1 + (den : ℝ)) ≤ 1 := by
      nlinarith only [hvBound, mul_nonneg hv0 (by linarith : 0 ≤ (den : ℝ) - 3)]
    have hlo : (1 : ℝ) < (point.2 : ℝ) := by nlinarith only [hrow, huBig, hvy]
    have hhi : (point.2 : ℝ) < 3 := by nlinarith only [hrow, hu1, hvBound']
    have hloInt : 1 < point.2 := by exact_mod_cast hlo
    have hhiInt : point.2 < 3 := by exact_mod_cast hhi
    omega

theorem ladderOdd_raw_cover {den : ℤ} (hden : BaseMask.ladderOdd.Valid den) :
    (reciprocalLadderDeck den).Covers (BaseMask.ladderOdd.raw den).sites := by
  obtain ⟨hmin, heven⟩ := hden
  apply PeriodDeck.covers_of_halfShiftedCell _ (ne_of_gt (reciprocalLadderDeck_pos hmin))
  intro point hcell
  obtain ⟨hx, hy, hband, hbottom, htop, _⟩ := ladder_cell_bounds hmin heven hcell
  refine ⟨point, BaseMask.mem_ladderOdd_body hx hy hband ?_, ⟨0, 0, ?_⟩⟩
  · rintro (⟨hrow, hcol⟩ | ⟨hrow, hcol⟩)
    · exact (not_lt_of_ge hcol) (hbottom hrow)
    · exact (not_lt_of_ge hcol) (htop hrow)
  · simp [PeriodDeck.combine]
    rfl

private theorem ladderOddAlt_raw_cover {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den) :
    (reciprocalLadderDeck den).Covers (BaseMask.ladderOddAlt.raw den).sites := by
  obtain ⟨hmin, heven⟩ := hden
  apply covers_of_place (1, 1) 0
  apply PeriodDeck.covers_of_halfShiftedCell _ (ne_of_gt (reciprocalLadderDeck_pos hmin))
  intro point hcell
  obtain ⟨hx, hy, hband, hbottom, htop, hright⟩ := ladder_cell_bounds hmin heven hcell
  by_cases hcol : point.1 = 2 * den
  · have hp : point = (2 * den, 2) := Prod.ext hcol (hright hcol)
    refine ⟨0, BaseMask.zero_mem_ladderOddAlt_placed hmin, 1, 0, ?_⟩
    rw [hp, reciprocalLadderDeck_eq heven]
    simp [PeriodDeck.combine]
  · by_cases hstrip : point.2 ≤ 1 ∧ den + 1 ≤ point.1
    · have hrow : point.2 = 1 := by
        by_contra! hrow
        have hzero : point.2 = 0 := by omega
        have := hbottom hzero
        omega
      let paid : Site := point + (1 - den, 1 + den)
      have hpaidX : paid.1 = point.1 + (1 - den) := rfl
      have hpaidY : paid.2 = den + 2 := by dsimp [paid]; omega
      refine ⟨paid, BaseMask.mem_ladderOddAlt_placed_body
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega), 0, -1, ?_⟩
      rw [reciprocalLadderDeck_eq heven]
      apply Prod.ext <;> simp [PeriodDeck.combine, paid]
    · refine ⟨point, BaseMask.mem_ladderOddAlt_placed_body ⟨hx.1, by omega⟩
        ⟨hy.1, by omega⟩ hband ?_, ⟨0, 0, ?_⟩⟩
      · rintro (h | ⟨hrow, hleft⟩)
        · exact hstrip h
        · have := htop (by omega)
          omega
      · simp [PeriodDeck.combine]
        rfl

theorem ladderOdd_cover {den : ℤ} (hden : BaseMask.ladderOdd.Valid den) :
    (Fraction.mk 1 den).modifiedDeck.Covers (BaseMask.ladderOdd.tile den hden).sites :=
  covers_trim (ladderOdd_raw_cover hden) _

theorem ladderOddAlt_cover {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den) :
    (Fraction.mk 1 den).modifiedDeck.Covers (BaseMask.ladderOddAlt.tile den hden).sites :=
  covers_trim (ladderOddAlt_raw_cover hden) _

theorem nearOneLadderDeck_eq {den : ℤ} (heven : den % 2 = 0) :
    (Fraction.mk 1 den).rotate.modifiedDeck = ⟨(den + 1, den - 1), (-2, 2 * den)⟩ := by
  have hodd : (Fraction.mk 1 den).Odd := by
    change (1 + den) % 2 = 1
    omega
  rw [Fraction.rotate_of_odd hodd]
  have hsum : (den - 1 + (den + 1)) % 2 = 0 := by omega
  simp only [Fraction.modifiedDeck, Fraction.periodMultiplicity, Fraction.unmodifiedDeck, if_pos hsum]
  apply congrArg₂ PeriodDeck.mk <;> apply Prod.ext <;> dsimp <;> omega

private theorem covers_nearOne_ladder_of_mapSite {den : ℤ} (heven : den % 2 = 0)
    {reciprocal nearOne : Finset Site} (offset : Site)
    (hmap : ∀ point ∈ reciprocal, QuarterTurn.counterclockwise.mapSite offset point ∈ nearOne)
    (hcover : (reciprocalLadderDeck den).Covers reciprocal) :
    (Fraction.mk 1 den).rotate.modifiedDeck.Covers nearOne := by
  rw [reciprocalLadderDeck_eq heven] at hcover
  rw [nearOneLadderDeck_eq heven]
  refine covers_counterclockwise offset rfl ?_ hmap hcover
  apply Prod.ext <;> dsimp [QuarterTurn.turn] <;> omega

theorem ladderEven_cover {den : ℤ} (hden : BaseMask.ladderEven.Valid den) :
    (Fraction.mk 1 den).rotate.modifiedDeck.Covers (BaseMask.ladderEven.tile den hden).sites := by
  apply covers_trim
  exact covers_nearOne_ladder_of_mapSite hden.2 (den + 1, den - 1)
    (fun point hmem => (BaseMask.mem_ladderEven_raw_iff point).mpr hmem) (ladderOdd_raw_cover hden)

theorem ladderEvenAlt_cover {den : ℤ} (hden : BaseMask.ladderEvenAlt.Valid den) :
    (Fraction.mk 1 den).rotate.modifiedDeck.Covers (BaseMask.ladderEvenAlt.tile den hden).sites := by
  apply covers_trim
  exact covers_nearOne_ladder_of_mapSite hden.2 (den, den)
    (fun point hmem => (BaseMask.mem_ladderEvenAlt_raw_iff point).mpr hmem) (ladderOddAlt_raw_cover hden)

theorem threes_current_odd (extra : ℕ) :
    (parentsAt (BaseRun.threes extra).word).current .odd = ⟨1, 2 * (extra : ℤ) + 3 + 1⟩ := by
  rw [BaseRun.word, parentsAt_replicate_three]
  apply Fraction.ext <;> simp [Parents.current, Parents.combine, Nat.cast_add]
  all_goals omega

theorem twos_current_even (extra : ℕ) :
    (parentsAt (BaseRun.twos extra).word).current .even =
      (Fraction.mk 1 (2 * (extra : ℤ) + 3 + 1)).rotate := by
  have hparents := parentsAt_valid (BaseRun.threes extra).word
  rw [← threes_current_odd, hparents.rotate_current_odd, rotate_parentsAt]
  simp [BaseRun.word, Digit.swapTwoThree]

/-- The actual odd standard and alternate doubled ladders at a nonempty pure-3 run. -/
theorem evaluateNative_threes_odd_covers (extra : ℕ) :
    let word := (BaseRun.threes extra).word
    let deck := (parentsAt word).current .odd |>.modifiedDeck
    ∃ registers, evaluateNative word = .ok registers ∧
      deck.Covers registers.standard.currentOdd.val.sites ∧
      deck.Covers registers.alternate.currentOdd.val.sites := by
  dsimp only
  rw [threes_current_odd]
  have hvalid : BaseMask.ladderOdd.Valid (2 * (extra : ℤ) + 3 + 1) := by
    change 4 ≤ 2 * (extra : ℤ) + 3 + 1 ∧ (2 * (extra : ℤ) + 3 + 1) % 2 = 0
    omega
  refine ⟨(BaseRun.threes extra).registers.llCenter, evaluateNative_base _, ?_, ?_⟩
  · apply covers_place
    exact ladderOdd_cover hvalid
  · apply covers_place
    exact ladderOddAlt_cover hvalid

/-- The actual even standard and alternate doubled ladders at a nonempty pure-2 run. -/
theorem evaluateNative_twos_even_covers (extra : ℕ) :
    let word := (BaseRun.twos extra).word
    let deck := (parentsAt word).current .even |>.modifiedDeck
    ∃ registers, evaluateNative word = .ok registers ∧
      deck.Covers registers.standard.currentEven.val.sites ∧
      deck.Covers registers.alternate.currentEven.val.sites := by
  dsimp only
  rw [twos_current_even]
  have hvalid : BaseMask.ladderEven.Valid (2 * (extra : ℤ) + 3 + 1) := by
    change 4 ≤ 2 * (extra : ℤ) + 3 + 1 ∧ (2 * (extra : ℤ) + 3 + 1) % 2 = 0
    omega
  refine ⟨(BaseRun.twos extra).registers.llCenter, evaluateNative_base _, ?_, ?_⟩
  · apply covers_place
    exact ladderEven_cover hvalid
  · apply covers_place
    exact ladderEvenAlt_cover hvalid

end FLatticePaper.Construction
