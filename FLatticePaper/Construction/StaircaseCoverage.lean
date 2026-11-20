import FLatticePaper.Construction.Native
import FLatticePaper.Farey.CenteredCell
import FLatticePaper.Farey.Rotation

namespace FLatticePaper.Construction

open Farey

theorem covers_place {deck : PeriodDeck} {tile : HeightTile Site}
    (hcover : deck.Covers tile.sites) (offset slope : Site) :
    deck.Covers (tile.place offset slope).sites := by
  intro site
  obtain ⟨point, hpoint, hspan⟩ := hcover (site - offset)
  refine ⟨point + offset, (tile.mem_place_sites offset slope _).mpr ?_, ?_⟩
  · rwa [add_sub_cancel_right]
  · rw [sub_add_eq_sub_sub, sub_right_comm]
    exact hspan

theorem covers_trim {deck : PeriodDeck} {tile : HeightTile Site}
    (hcover : deck.Covers tile.sites) (hne : tile.sites.Nonempty) :
    deck.Covers (tile.trim hne).sites :=
  covers_place hcover _ _

theorem covers_of_place {deck : PeriodDeck} {tile : HeightTile Site} (offset slope : Site)
    (hcover : deck.Covers (tile.place offset slope).sites) : deck.Covers tile.sites := by
  intro site
  obtain ⟨point, hpoint, hspan⟩ := hcover (site + offset)
  refine ⟨point - offset, (tile.mem_place_sites offset slope _).mp hpoint, ?_⟩
  have heq : site - (point - offset) = site + offset - point := by abel
  rwa [heq]

private theorem int_le_of_lt_cast_succ {first second : ℤ}
    (hlt : (first : ℝ) < (second : ℝ) + 1) : first ≤ second := by
  have : first < second + 1 := by exact_mod_cast hlt
  omega

private theorem int_le_of_cast_pred_lt {first second : ℤ}
    (hlt : (first : ℝ) - 1 < (second : ℝ)) : first ≤ second := by
  have : first - 1 < second := by exact_mod_cast hlt
  omega

def reciprocalEvenDeck (den : ℤ) : PeriodDeck :=
  (Fraction.mk 1 den).modifiedDeck

theorem reciprocalEvenDeck_eq {den : ℤ} (hodd : den % 2 = 1) :
    reciprocalEvenDeck den = ⟨(den, 1), (1 - den, 1 + den)⟩ := by
  have heven : (1 + den) % 2 = 0 := by omega
  simp [reciprocalEvenDeck, Fraction.modifiedDeck, Fraction.periodMultiplicity,
    Fraction.unmodifiedDeck, heven]

private theorem reciprocalEvenDeck_pos {den : ℤ} (hden : 3 ≤ den) :
    0 < (reciprocalEvenDeck den).det :=
  Fraction.det_modifiedDeck_pos (fraction := ⟨1, den⟩)
    ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩

private theorem reciprocal_cell_coordinates {den : ℤ} {point : Site}
    (hodd : den % 2 = 1) (hcell : (reciprocalEvenDeck den).InHalfShiftedCell point) :
    ∃ alongKernel alongTransverse : ℝ,
      0 ≤ alongKernel ∧ alongKernel < 1 ∧ 0 ≤ alongTransverse ∧ alongTransverse < 1 ∧
      (point.1 : ℝ) = 1 / 2 + alongKernel * (den : ℝ) + alongTransverse * (1 - (den : ℝ)) ∧
      (point.2 : ℝ) = -(1 / 2) + alongKernel + alongTransverse * (1 + (den : ℝ)) := by
  rw [reciprocalEvenDeck_eq hodd] at hcell
  simpa [PeriodDeck.InHalfShiftedCell] using hcell

private theorem reciprocal_cell_bounds {den : ℤ} {point : Site} (hden : 3 ≤ den)
    (hodd : den % 2 = 1) (hcell : (reciprocalEvenDeck den).InHalfShiftedCell point) :
    (2 - den ≤ point.1 ∧ point.1 ≤ den) ∧ (0 ≤ point.2 ∧ point.2 ≤ den + 1) ∧
      1 ≤ point.1 + point.2 ∧ point.1 + point.2 ≤ den + 2 := by
  obtain ⟨alongKernel, alongTransverse, hker0, hker1, htra0, htra1, hcol, hrow⟩ :=
    reciprocal_cell_coordinates hodd hcell
  have hdenR : (3 : ℝ) ≤ (den : ℝ) := by exact_mod_cast hden
  have hcolLo : (3 : ℝ) / 2 - (den : ℝ) ≤ (point.1 : ℝ) := by
    nlinarith only [hcol, mul_nonneg hker0 (by linarith : 0 ≤ (den : ℝ)),
      mul_nonneg (by linarith : 0 ≤ 1 - alongTransverse) (by linarith : 0 ≤ (den : ℝ) - 1)]
  have hcolHi : (point.1 : ℝ) ≤ (den : ℝ) + 1 / 2 := by
    nlinarith only [hcol, mul_nonneg (by linarith : 0 ≤ 1 - alongKernel) (by linarith : 0 ≤ (den : ℝ)),
      mul_nonneg htra0 (by linarith : 0 ≤ (den : ℝ) - 1)]
  have hrowLo : -(1 / 2 : ℝ) ≤ (point.2 : ℝ) := by
    nlinarith only [hrow, hker0, mul_nonneg htra0 (by linarith : 0 ≤ 1 + (den : ℝ))]
  have hrowHi : (point.2 : ℝ) ≤ (den : ℝ) + 3 / 2 := by
    nlinarith only [hrow, hker1,
      mul_nonneg (by linarith : 0 ≤ 1 - alongTransverse) (by linarith : 0 ≤ 1 + (den : ℝ))]
  have hsum : (point.1 : ℝ) + (point.2 : ℝ) =
      alongKernel * (1 + (den : ℝ)) + 2 * alongTransverse := by rw [hcol, hrow]; ring
  have hmul : 0 ≤ alongKernel * (1 + (den : ℝ)) :=
    mul_nonneg hker0 (by linarith)
  have hsumPos : 0 < (point.1 : ℝ) + (point.2 : ℝ) := by
    by_contra! h
    have htraZero : alongTransverse = 0 := by linarith only [h, hsum, hmul, htra0]
    have hkerZero : alongKernel = 0 := by
      have hzero : alongKernel * (1 + (den : ℝ)) = 0 := by
        rw [htraZero] at hsum
        linarith
      exact (mul_eq_zero.mp hzero).resolve_right (by linarith)
    rw [htraZero, hkerZero] at hcol
    have htwice : (2 : ℝ) * (point.1 : ℝ) = 1 := by linarith
    have himpossible : (2 : ℤ) * point.1 = 1 := by exact_mod_cast htwice
    omega
  have hsumHi : (point.1 : ℝ) + (point.2 : ℝ) < (den : ℝ) + 3 := by
    have hk := mul_lt_mul_of_pos_right hker1 (by linarith : 0 < 1 + (den : ℝ))
    linarith only [hsum, hk, htra1]
  have hsumPosInt : 0 < point.1 + point.2 := by exact_mod_cast hsumPos
  refine ⟨⟨int_le_of_cast_pred_lt ?_, int_le_of_lt_cast_succ ?_⟩,
    ⟨int_le_of_cast_pred_lt ?_, int_le_of_lt_cast_succ ?_⟩,
    by omega, int_le_of_lt_cast_succ ?_⟩
  all_goals
    push_cast
    linarith

private theorem reciprocal_cell_top_bounds {den : ℤ} {point : Site} (hden : 3 ≤ den)
    (hodd : den % 2 = 1) (hcell : (reciprocalEvenDeck den).InHalfShiftedCell point)
    (htop : point.2 = den + 1) :
    (3 - (den : ℝ)) / 2 ≤ (point.1 : ℝ) ∧ point.1 ≤ 1 := by
  obtain ⟨alongKernel, alongTransverse, _, hker1, _, htra1, hcol, hrow⟩ :=
    reciprocal_cell_coordinates hodd hcell
  rw [htop] at hrow
  push_cast at hrow
  have hdenR : (3 : ℝ) ≤ (den : ℝ) := by exact_mod_cast hden
  have hvLoss := mul_nonneg (by linarith : 0 ≤ 1 - alongTransverse) (by linarith : 0 ≤ 1 + (den : ℝ))
  have hkerHalf : (1 : ℝ) / 2 ≤ alongKernel := by nlinarith only [hrow, hvLoss]
  constructor
  · nlinarith only [hcol, mul_nonneg (sub_nonneg.mpr hkerHalf) (by linarith : 0 ≤ (den : ℝ)),
      mul_nonneg (by linarith : 0 ≤ 1 - alongTransverse) (by linarith : 0 ≤ (den : ℝ) - 1)]
  · apply int_le_of_lt_cast_succ
    push_cast
    have hmaxLoss : (1 + (den : ℝ)) * (1 - alongTransverse) ≤ 1 / 2 := by
      nlinarith only [hrow, hker1]
    nlinarith only [hcol, hmaxLoss, htra1,
      mul_pos (by linarith : 0 < 1 - alongKernel) (by linarith : 0 < (den : ℝ))]

theorem stairEven_raw_cover {den : ℤ} (hden : BaseMask.stairEven.Valid den) :
    (reciprocalEvenDeck den).Covers (BaseMask.stairEven.raw den).sites := by
  obtain ⟨hmin, hodd⟩ := hden
  apply PeriodDeck.covers_of_halfShiftedCell _ (ne_of_gt (reciprocalEvenDeck_pos hmin))
  intro point hcell
  obtain ⟨hx, hy, hband⟩ := reciprocal_cell_bounds hmin hodd hcell
  refine ⟨point, BaseMask.mem_stairEven_body hx hy hband, ⟨0, 0, ?_⟩⟩
  simp [PeriodDeck.combine]
  rfl

private theorem stairEvenAlt_raw_cover {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den) :
    (reciprocalEvenDeck den).Covers (BaseMask.stairEvenAlt.raw den).sites := by
  obtain ⟨hmin, hodd⟩ := hden
  apply PeriodDeck.covers_of_halfShiftedCell _ (ne_of_gt (reciprocalEvenDeck_pos hmin))
  intro point hcell
  obtain ⟨⟨hcolLo, hcolHi⟩, ⟨hrowLo, hrowHi⟩, hsumLo, hsumHi⟩ :=
    reciprocal_cell_bounds hmin hodd hcell
  have hpoint (hshape : (2 - den ≤ point.1 + point.2 ∧ point.1 + point.2 ≤ den + 2 ∧
      0 ≤ point.2 ∧ point.2 ≤ den) ∨ (point.2 = den + 1 ∧ 4 - den ≤ point.1 ∧ point.1 ≤ 3)) :
      ∃ representative ∈ (BaseMask.stairEvenAlt.raw den).sites,
        point - representative ∈ (reciprocalEvenDeck den).span := by
    refine ⟨point, BaseMask.mem_stairEvenAlt_body_or_rail ⟨by omega, hcolHi⟩
      ⟨by omega, hrowHi⟩ hshape, ⟨0, 0, ?_⟩⟩
    simp [PeriodDeck.combine]
    rfl
  by_cases hbody : point.2 ≤ den
  · exact hpoint (Or.inl ⟨by omega, hsumHi, hrowLo, hbody⟩)
  · have htop : point.2 = den + 1 := by omega
    obtain ⟨hlo, hhi⟩ := reciprocal_cell_top_bounds hmin hodd hcell htop
    by_cases hsmall : den = 3
    · have hnonneg : 0 ≤ point.1 := by
        rw [hsmall] at hlo
        have hc : (0 : ℝ) ≤ (point.1 : ℝ) := by linarith
        exact_mod_cast hc
      by_cases hzero : point.1 = 0
      · have hp : point = (0, 4) := Prod.ext hzero (by omega)
        subst den
        rw [hp]
        exact ⟨(2, 0), by decide, ⟨0, 1, rfl⟩⟩
      · exact hpoint (Or.inr ⟨htop, by omega, by omega⟩)
    · have hbig : (5 : ℝ) ≤ (den : ℝ) := by
        exact_mod_cast (show (5 : ℤ) ≤ den by omega)
      have hx : 4 - den ≤ point.1 := by
        have hc : (4 : ℝ) - (den : ℝ) ≤ (point.1 : ℝ) := by linarith
        exact_mod_cast hc
      exact hpoint (Or.inr ⟨htop, hx, by omega⟩)

theorem stairEven_cover {den : ℤ} (hden : BaseMask.stairEven.Valid den) :
    (Fraction.mk 1 den).modifiedDeck.Covers (BaseMask.stairEven.tile den hden).sites :=
  covers_trim (stairEven_raw_cover hden) _

theorem stairEvenAlt_cover {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den) :
    (Fraction.mk 1 den).modifiedDeck.Covers (BaseMask.stairEvenAlt.tile den hden).sites :=
  covers_trim (stairEvenAlt_raw_cover hden) _

theorem nearOneDeck_eq {den : ℤ} (hodd : den % 2 = 1) :
    (Fraction.mk 1 den).rotate.modifiedDeck = ⟨(den + 1, den - 1), (-1, den)⟩ := by
  have heven : (Fraction.mk 1 den).Even := by
    change (1 + den) % 2 = 0
    omega
  rw [Fraction.rotate_of_even heven]
  have hsum : ((den - 1) / 2 + (den + 1) / 2) % 2 ≠ 0 := by omega
  simp only [Fraction.modifiedDeck, Fraction.periodMultiplicity, Fraction.unmodifiedDeck,
    if_neg hsum]
  apply congrArg₂ PeriodDeck.mk <;> apply Prod.ext <;> dsimp <;> omega

/-- Transport coverage when a counterclockwise turn takes the two original
generators to the new transverse generator and the negative new kernel. -/
theorem covers_counterclockwise {before after : PeriodDeck} {original rotated : Finset Site}
    (offset : Site)
    (hkernel : QuarterTurn.counterclockwise.turn before.kernel = after.transverse)
    (htransverse : QuarterTurn.counterclockwise.turn before.transverse = -after.kernel)
    (hmap : ∀ point ∈ original, QuarterTurn.counterclockwise.mapSite offset point ∈ rotated)
    (hcover : before.Covers original) : after.Covers rotated := by
  intro site
  obtain ⟨point, rfl⟩ := (QuarterTurn.counterclockwise.siteEquiv offset).surjective site
  obtain ⟨representative, hrep, kernel, transverse, hspan⟩ := hcover point
  refine ⟨_, hmap representative hrep, -transverse, kernel, Prod.ext ?_ ?_⟩
  · have hk := congrArg Prod.fst hkernel
    have ht := congrArg Prod.fst htransverse
    have h := congrArg Prod.snd hspan
    dsimp [QuarterTurn.turn] at hk ht
    dsimp [QuarterTurn.siteEquiv, QuarterTurn.mapSite, QuarterTurn.turn, PeriodDeck.combine] at h ⊢
    linear_combination -h + kernel * hk + transverse * ht
  · have hk := congrArg Prod.snd hkernel
    have ht := congrArg Prod.snd htransverse
    have h := congrArg Prod.fst hspan
    dsimp [QuarterTurn.turn] at hk ht
    dsimp [QuarterTurn.siteEquiv, QuarterTurn.mapSite, QuarterTurn.turn, PeriodDeck.combine] at h ⊢
    linear_combination h + kernel * hk + transverse * ht

private theorem covers_nearOne_of_mapSite {den : ℤ} (hodd : den % 2 = 1)
    {reciprocal nearOne : Finset Site} (offset : Site)
    (hmap : ∀ point ∈ reciprocal, QuarterTurn.counterclockwise.mapSite offset point ∈ nearOne)
    (hcover : (reciprocalEvenDeck den).Covers reciprocal) :
    (Fraction.mk 1 den).rotate.modifiedDeck.Covers nearOne := by
  rw [reciprocalEvenDeck_eq hodd] at hcover
  rw [nearOneDeck_eq hodd]
  refine covers_counterclockwise offset rfl ?_ hmap hcover
  apply Prod.ext <;> dsimp [QuarterTurn.turn] <;> omega

theorem stairOdd_cover {den : ℤ} (hden : BaseMask.stairOdd.Valid den) :
    (Fraction.mk 1 den).rotate.modifiedDeck.Covers (BaseMask.stairOdd.tile den hden).sites := by
  apply covers_trim
  exact covers_nearOne_of_mapSite hden.2 (den + 1, den - 1)
    (fun point hmem => (BaseMask.mem_stairOdd_raw_iff point).mpr hmem) (stairEven_raw_cover hden)

theorem stairOddAlt_cover {den : ℤ} (hden : BaseMask.stairOddAlt.Valid den) :
    (Fraction.mk 1 den).rotate.modifiedDeck.Covers (BaseMask.stairOddAlt.tile den hden).sites := by
  apply covers_trim
  exact covers_nearOne_of_mapSite hden.2 (den, 2 * den - 3)
    (fun point hmem => (BaseMask.mem_stairOddAlt_raw_iff point).mpr hmem) (stairEvenAlt_raw_cover hden)

theorem parentsAt_replicate_three (count : ℕ) :
    parentsAt (List.replicate count .three) = ⟨⟨0, 1⟩, ⟨1, 2 * (count : ℤ) + 1⟩⟩ := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [List.replicate_succ', parentsAt_append_singleton, ih]
    apply congrArg (Parents.mk ⟨0, 1⟩)
    apply Fraction.ext <;> simp [Parents.current, Parents.combine, Nat.cast_succ]
    all_goals omega

theorem threes_current_even (extra : ℕ) :
    (parentsAt (BaseRun.threes extra).word).current .even = ⟨1, 2 * (extra : ℤ) + 3 + 2⟩ := by
  rw [BaseRun.word, parentsAt_replicate_three]
  apply Fraction.ext <;> simp [Parents.current, Parents.combine, Nat.cast_add]
  all_goals omega

/-- The actual even standard and alternate outputs of every nonempty initial
run of digit three cover their own modified period classes. -/
theorem evaluateNative_threes_even_covers (extra : ℕ) :
    let word := (BaseRun.threes extra).word
    let deck := (parentsAt word).current .even |>.modifiedDeck
    ∃ registers, evaluateNative word = .ok registers ∧
      deck.Covers registers.standard.currentEven.val.sites ∧
      deck.Covers registers.alternate.currentEven.val.sites := by
  dsimp only
  rw [threes_current_even]
  have hvalid : BaseMask.stairEven.Valid (2 * (extra : ℤ) + 3 + 2) := by
    change 3 ≤ 2 * (extra : ℤ) + 3 + 2 ∧ (2 * (extra : ℤ) + 3 + 2) % 2 = 1
    omega
  refine ⟨(BaseRun.threes extra).registers.llCenter, evaluateNative_base _, ?_, ?_⟩
  · apply covers_place
    exact stairEven_cover hvalid
  · apply covers_place
    exact stairEvenAlt_cover hvalid

theorem twos_current_odd (extra : ℕ) :
    (parentsAt (BaseRun.twos extra).word).current .odd =
      (Fraction.mk 1 (2 * (extra : ℤ) + 3 + 2)).rotate := by
  have hparents := parentsAt_valid (BaseRun.threes extra).word
  rw [← threes_current_even, hparents.rotate_current_even, rotate_parentsAt]
  simp [BaseRun.word, Digit.swapTwoThree]

/-- The actual odd standard and alternate outputs of every nonempty initial
run of digit two cover their own modified period classes. -/
theorem evaluateNative_twos_odd_covers (extra : ℕ) :
    let word := (BaseRun.twos extra).word
    let deck := (parentsAt word).current .odd |>.modifiedDeck
    ∃ registers, evaluateNative word = .ok registers ∧
      deck.Covers registers.standard.currentOdd.val.sites ∧
      deck.Covers registers.alternate.currentOdd.val.sites := by
  dsimp only
  rw [twos_current_odd]
  have hvalid : BaseMask.stairOdd.Valid (2 * (extra : ℤ) + 3 + 2) := by
    change 3 ≤ 2 * (extra : ℤ) + 3 + 2 ∧ (2 * (extra : ℤ) + 3 + 2) % 2 = 1
    omega
  refine ⟨(BaseRun.twos extra).registers.llCenter, evaluateNative_base _, ?_, ?_⟩
  · apply covers_place
    exact stairOdd_cover hvalid
  · apply covers_place
    exact stairOddAlt_cover hvalid

end FLatticePaper.Construction
