import FLatticePaper.Construction.AlternateStaircaseLaplacian
import FLatticePaper.Construction.AlternateStaircaseRankCorrection
import FLatticePaper.Plane.Recurrence

namespace FLatticePaper.Construction

open Farey

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

private theorem rankCorrection_add_representative {den : ℤ} {correction : Field}
    (hcorrect : ∀ point ∈ (BaseMask.stairEvenAlt.raw den).sites, correction point = stairEvenAltRankCorrection den point)
    (hperiodic : ∀ step ∈ (reciprocalEvenDeck den).span, Function.Periodic correction step)
    {step : Site} (hstep : step ∈ (reciprocalEvenDeck den).span) (point : Site)
    (hmem : point + step ∈ (BaseMask.stairEvenAlt.raw den).sites) :
    correction point = stairEvenAltRankCorrection den (point + step) :=
  (hperiodic step hstep point).symm.trans (hcorrect _ hmem)

private theorem rankCorrection_sub_representative {den : ℤ} {correction : Field}
    (hcorrect : ∀ point ∈ (BaseMask.stairEvenAlt.raw den).sites, correction point = stairEvenAltRankCorrection den point)
    (hperiodic : ∀ step ∈ (reciprocalEvenDeck den).span, Function.Periodic correction step)
    {step : Site} (hstep : step ∈ (reciprocalEvenDeck den).span) (point : Site)
    (hmem : point - step ∈ (BaseMask.stairEvenAlt.raw den).sites) :
    correction point = stairEvenAltRankCorrection den (point - step) := by
  have h := hperiodic step hstep (point - step)
  rw [sub_add_cancel] at h
  exact h.trans (hcorrect _ hmem)

private theorem stairEvenAlt_kernel_mem_span {den : ℤ} (hodd : den % 2 = 1) :
    (den, 1) ∈ (reciprocalEvenDeck den).span := by
  rw [reciprocalEvenDeck_eq hodd]
  exact ⟨1, 0, by apply Prod.ext <;> simp [PeriodDeck.combine]⟩

private theorem stairEvenAlt_transverse_mem_span {den : ℤ} (hodd : den % 2 = 1) :
    (1 - den, den + 1) ∈ (reciprocalEvenDeck den).span := by
  rw [reciprocalEvenDeck_eq hodd]
  exact ⟨0, 1, by apply Prod.ext <;> simp [PeriodDeck.combine, add_comm 1 den]⟩

private theorem stairEvenAlt_diagonal_mem_span {den : ℤ} (hodd : den % 2 = 1) :
    (1, den + 2) ∈ (reciprocalEvenDeck den).span := by
  rw [reciprocalEvenDeck_eq hodd]
  exact ⟨1, 1, by apply Prod.ext <;> simp only [PeriodDeck.combine, one_mul] <;> omega⟩

private theorem stairEvenAlt_rank_even_black {den x y : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {correction : Field} (hcorrect : ∀ point ∈ (BaseMask.stairEvenAlt.raw den).sites,
      correction point = stairEvenAltRankCorrection den point)
    (hperiodic : ∀ step ∈ (reciprocalEvenDeck den).span, Function.Periodic correction step)
    (hpoint : (x, y) ∈ (BaseMask.stairEvenAlt.raw den).sites)
    (heven : (x + y) % 2 = 0) (hblack : StairEvenAltEvenBlack den (x, y)) :
    6 * (x - 1) + correction (x - 1, y) < 6 * x + correction (x, y) ∧
    6 * (x + 1) + correction (x + 1, y) < 6 * x + correction (x, y) := by
  have ⟨hmin, hodd⟩ := hden
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_stairEvenAlt_raw_iff.mp hpoint
  dsimp only at hx hy hshape
  rw [hcorrect _ hpoint]
  have hU := stairEvenAlt_kernel_mem_span hodd
  rcases hblack with ⟨hyLo, hyHi, hxLeft | hxRight | hdiag⟩ | hleft | hright
  · have hleft : (x - 1, y) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
    have hright : (x + 1, y) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
    rw [hcorrect _ hleft, hcorrect _ hright]
    constructor <;> alternate_staircase_rank
  · have hleft : (x - 1, y) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
    have hright : (x + 1, y) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
    rw [hcorrect _ hleft, hcorrect _ hright]
    constructor <;> alternate_staircase_rank
  · have hleft : (x - 1, y) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
    have hright : (x + 1, y) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
    rw [hcorrect _ hleft, hcorrect _ hright]
    by_cases hyOne : y = 1
    · constructor <;> alternate_staircase_rank
    · constructor <;> alternate_staircase_rank
  · have hleft' : ((x - 1, y) : Site) + (den, 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by
      alternate_staircase_mem
    have hright' : (x + 1, y) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
    rw [rankCorrection_add_representative hcorrect hperiodic hU _ hleft', hcorrect _ hright']
    constructor <;> alternate_staircase_rank
  · have hleft' : (x - 1, y) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
    have hright' : ((x + 1, y) : Site) - (den, 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by
      alternate_staircase_mem
    rw [hcorrect _ hleft', rankCorrection_sub_representative hcorrect hperiodic hU _ hright']
    constructor <;> alternate_staircase_rank

private theorem stairEvenAlt_rank_even_white_left {den x y : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {correction : Field} (hcorrect : ∀ point ∈ (BaseMask.stairEvenAlt.raw den).sites,
      correction point = stairEvenAltRankCorrection den point)
    (_hperiodic : ∀ step ∈ (reciprocalEvenDeck den).span, Function.Periodic correction step)
    (hpoint : (x, y) ∈ (BaseMask.stairEvenAlt.raw den).sites)
    (heven : (x + y) % 2 = 0) (_hwhite : ¬ StairEvenAltEvenBlack den (x, y))
    (hl : StairEvenAltLeftHigh den (x, y)) :
    6 * (x - 1) + correction (x - 1, y) < 6 * x + correction (x, y) ∨
    6 * (x + 1) + correction (x + 1, y) < 6 * x + correction (x, y) := by
  have ⟨hmin, hodd⟩ := hden
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_stairEvenAlt_raw_iff.mp hpoint
  dsimp only at hx hy hshape
  rw [hcorrect _ hpoint]
  have hU := stairEvenAlt_kernel_mem_span hodd
  simp only [StairEvenAltLeftHigh] at hl
  right
  have hright : (x + 1, y) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
  rw [hcorrect _ hright]
  alternate_staircase_rank


private theorem stairEvenAlt_rank_even_white_right {den x y : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {correction : Field} (hcorrect : ∀ point ∈ (BaseMask.stairEvenAlt.raw den).sites,
      correction point = stairEvenAltRankCorrection den point)
    (hperiodic : ∀ step ∈ (reciprocalEvenDeck den).span, Function.Periodic correction step)
    (hpoint : (x, y) ∈ (BaseMask.stairEvenAlt.raw den).sites)
    (heven : (x + y) % 2 = 0) (hwhite : ¬ StairEvenAltEvenBlack den (x, y))
    (hl : ¬ StairEvenAltLeftHigh den (x, y)) (hr : StairEvenAltRightHigh den (x, y)) :
    6 * (x - 1) + correction (x - 1, y) < 6 * x + correction (x, y) ∨
    6 * (x + 1) + correction (x + 1, y) < 6 * x + correction (x, y) := by
  have ⟨hmin, hodd⟩ := hden
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_stairEvenAlt_raw_iff.mp hpoint
  dsimp only at hx hy hshape
  simp only [StairEvenAltEvenBlack] at hwhite
  rw [hcorrect _ hpoint]
  have hU := stairEvenAlt_kernel_mem_span hodd
  simp only [StairEvenAltRightHigh] at hr
  right
  by_cases hend : x = den
  · have hyOne : y = 1 := by omega
    have hright : ((x + 1, y) : Site) - (den, 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by
      alternate_staircase_mem
    rw [rankCorrection_sub_representative hcorrect hperiodic hU _ hright]
    alternate_staircase_rank
  · have hright : (x + 1, y) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
    rw [hcorrect _ hright]
    alternate_staircase_rank


set_option maxHeartbeats 400000 in
private theorem stairEvenAlt_rank_even_white_center {den x y : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {correction : Field} (hcorrect : ∀ point ∈ (BaseMask.stairEvenAlt.raw den).sites,
      correction point = stairEvenAltRankCorrection den point)
    (hperiodic : ∀ step ∈ (reciprocalEvenDeck den).span, Function.Periodic correction step)
    (hpoint : (x, y) ∈ (BaseMask.stairEvenAlt.raw den).sites)
    (heven : (x + y) % 2 = 0) (hwhite : ¬ StairEvenAltEvenBlack den (x, y))
    (hl : ¬ StairEvenAltLeftHigh den (x, y)) (hr : ¬ StairEvenAltRightHigh den (x, y)) :
    6 * (x - 1) + correction (x - 1, y) < 6 * x + correction (x, y) ∨
    6 * (x + 1) + correction (x + 1, y) < 6 * x + correction (x, y) := by
  have ⟨hmin, hodd⟩ := hden
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_stairEvenAlt_raw_iff.mp hpoint
  dsimp only at hx hy hshape
  simp only [StairEvenAltEvenBlack] at hwhite
  rw [hcorrect _ hpoint]
  have hU := stairEvenAlt_kernel_mem_span hodd
  simp only [StairEvenAltLeftHigh, StairEvenAltRightHigh] at hl hr
  left
  by_cases hend : x = 4 - 2 * den ∧ y = den - 1
  · have hleft : ((x - 1, y) : Site) + (den, 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by
      alternate_staircase_mem
    rw [rankCorrection_add_representative hcorrect hperiodic hU _ hleft]
    alternate_staircase_rank
  · have hleft : (x - 1, y) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
    rw [hcorrect _ hleft]
    rcases hshape with h | h | h | h | h <;> alternate_staircase_rank

private theorem stairEvenAlt_rank_even_white {den x y : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {correction : Field} (hcorrect : ∀ point ∈ (BaseMask.stairEvenAlt.raw den).sites,
      correction point = stairEvenAltRankCorrection den point)
    (hperiodic : ∀ step ∈ (reciprocalEvenDeck den).span, Function.Periodic correction step)
    (hpoint : (x, y) ∈ (BaseMask.stairEvenAlt.raw den).sites)
    (heven : (x + y) % 2 = 0) (hwhite : ¬ StairEvenAltEvenBlack den (x, y)) :
    6 * (x - 1) + correction (x - 1, y) < 6 * x + correction (x, y) ∨
    6 * (x + 1) + correction (x + 1, y) < 6 * x + correction (x, y) := by
  by_cases hl : StairEvenAltLeftHigh den (x, y)
  · exact stairEvenAlt_rank_even_white_left hden hcorrect hperiodic hpoint heven hwhite hl
  · by_cases hr : StairEvenAltRightHigh den (x, y)
    · exact stairEvenAlt_rank_even_white_right hden hcorrect hperiodic hpoint heven hwhite hl hr
    · exact stairEvenAlt_rank_even_white_center hden hcorrect hperiodic hpoint heven hwhite hl hr

private theorem stairEvenAlt_rankCorrection_eq_parity {den x y : ℤ}
    (hfirst : ¬ ((x = 1 - den ∧ y = 0) ∨ (x = 1 ∧ y = 1)))
    (hcorner : ¬ (x = 3 ∧ y = den))
    (hdiag : ¬ (x + y = 2 ∧ 2 ≤ y ∧ y ≤ den - 1))
    (hl : ¬ StairEvenAltLeftHigh den (x, y)) (hr : ¬ StairEvenAltRightHigh den (x, y)) :
    stairEvenAltRankCorrection den (x, y) = (x + y) % 2 := by
  simp only [stairEvenAltRankCorrection, if_neg hfirst, if_neg hcorner, if_neg hdiag, if_neg hl, if_neg hr]

private theorem stairEvenAlt_rank_odd_black_left {den x y : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {correction : Field} (hcorrect : ∀ point ∈ (BaseMask.stairEvenAlt.raw den).sites,
      correction point = stairEvenAltRankCorrection den point)
    (hpoint : (x, y) ∈ (BaseMask.stairEvenAlt.raw den).sites)
    (hoddSite : (x + y) % 2 ≠ 0) (hblack : ¬ StairEvenAltOddWhite den (x, y))
    (hl : StairEvenAltLeftHigh den (x, y)) :
    correction (x, y - 1) < correction (x, y) ∧ correction (x, y + 1) < correction (x, y) := by
  have ⟨hmin, hodd⟩ := hden
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_stairEvenAlt_raw_iff.mp hpoint
  dsimp only at hx hy hshape
  simp only [StairEvenAltOddWhite] at hblack
  have hbody : 0 ≤ y ∧ y ≤ den ∧ 2 - den ≤ x + y ∧ x + y ≤ den + 2 := by omega
  clear hshape
  have hdown : (x, y - 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
  have hup : (x, y + 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
  rw [hcorrect _ hpoint, hcorrect _ hdown, hcorrect _ hup]
  clear hcorrect hpoint hdown hup
  simp only [StairEvenAltLeftHigh] at hl
  constructor <;> alternate_staircase_rank


set_option maxHeartbeats 400000 in
private theorem stairEvenAlt_rank_odd_black_right {den x y : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {correction : Field} (hcorrect : ∀ point ∈ (BaseMask.stairEvenAlt.raw den).sites,
      correction point = stairEvenAltRankCorrection den point)
    (hpoint : (x, y) ∈ (BaseMask.stairEvenAlt.raw den).sites)
    (hoddSite : (x + y) % 2 ≠ 0) (hblack : ¬ StairEvenAltOddWhite den (x, y))
    (hl : ¬ StairEvenAltLeftHigh den (x, y)) (hr : StairEvenAltRightHigh den (x, y)) :
    correction (x, y - 1) < correction (x, y) ∧ correction (x, y + 1) < correction (x, y) := by
  have ⟨hmin, hodd⟩ := hden
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_stairEvenAlt_raw_iff.mp hpoint
  dsimp only at hx hy hshape
  simp only [StairEvenAltOddWhite] at hblack
  have hbody : 0 ≤ y ∧ y ≤ den ∧ 2 - den ≤ x + y ∧ x + y ≤ den + 2 := by omega
  clear hshape
  have hdown : (x, y - 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
  have hup : (x, y + 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
  rw [hcorrect _ hpoint, hcorrect _ hdown, hcorrect _ hup]
  clear hcorrect hpoint hdown hup
  simp only [StairEvenAltLeftHigh, StairEvenAltRightHigh] at hl hr
  constructor <;> alternate_staircase_rank


set_option maxHeartbeats 400000 in
private theorem stairEvenAlt_rank_odd_black_center {den x y : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {correction : Field} (hcorrect : ∀ point ∈ (BaseMask.stairEvenAlt.raw den).sites,
      correction point = stairEvenAltRankCorrection den point)
    (hpoint : (x, y) ∈ (BaseMask.stairEvenAlt.raw den).sites)
    (hoddSite : (x + y) % 2 ≠ 0) (hblack : ¬ StairEvenAltOddWhite den (x, y))
    (hl : ¬ StairEvenAltLeftHigh den (x, y)) (hr : ¬ StairEvenAltRightHigh den (x, y)) :
    correction (x, y - 1) < correction (x, y) ∧ correction (x, y + 1) < correction (x, y) := by
  have ⟨hmin, hodd⟩ := hden
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_stairEvenAlt_raw_iff.mp hpoint
  dsimp only at hx hy hshape
  simp only [StairEvenAltOddWhite] at hblack
  have hbody : 0 ≤ y ∧ y ≤ den ∧ 2 - den ≤ x + y ∧ x + y ≤ den + 2 := by omega
  clear hshape
  have hdown : (x, y - 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
  have hup : (x, y + 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
  rw [hcorrect _ hpoint, hcorrect _ hdown, hcorrect _ hup]
  clear hcorrect hpoint hdown hup
  simp only [StairEvenAltLeftHigh, StairEvenAltRightHigh] at hl hr
  have hcenter : stairEvenAltRankCorrection den (x, y) = (x + y) % 2 :=
    stairEvenAlt_rankCorrection_eq_parity (den := den) (x := x) (y := y)
      (by clear * - hmin hodd hx hy hoddSite; omega) (by clear * - hmin hodd hx hy hbody; omega) (by clear * - hmin hodd hx hy hoddSite; omega)
      (by simp only [StairEvenAltLeftHigh]; clear * - hmin hodd hx hy hl; omega)
      (by simp only [StairEvenAltRightHigh]; clear * - hmin hodd hx hy hr; omega)
  have hlower : stairEvenAltRankCorrection den (x, y - 1) = (x + (y - 1)) % 2 :=
    stairEvenAlt_rankCorrection_eq_parity (den := den) (x := x) (y := y - 1)
      (by clear * - hmin hodd hx hy hblack; omega) (by clear * - hmin hodd hx hy hbody; omega) (by clear * - hmin hodd hx hy hblack; omega)
      (by simp only [StairEvenAltLeftHigh]; clear * - hmin hodd hx hy hl hoddSite; omega)
      (by simp only [StairEvenAltRightHigh]; clear * - hmin hodd hx hy hbody hr; omega)
  have hupper : stairEvenAltRankCorrection den (x, y + 1) = (x + (y + 1)) % 2 :=
    stairEvenAlt_rankCorrection_eq_parity (den := den) (x := x) (y := y + 1)
      (by clear * - hmin hodd hx hy hblack; omega) (by clear * - hmin hodd hx hy hblack; omega) (by clear * - hmin hodd hx hy hblack; omega)
      (by simp only [StairEvenAltLeftHigh]; clear * - hmin hodd hx hy hbody hl; omega)
      (by simp only [StairEvenAltRightHigh]; clear * - hmin hodd hx hy hblack hr; omega)
  exact ⟨by clear * - hoddSite hcenter hlower hupper; omega, by clear * - hoddSite hcenter hlower hupper; omega⟩

private theorem stairEvenAlt_rank_odd_black {den x y : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {correction : Field} (hcorrect : ∀ point ∈ (BaseMask.stairEvenAlt.raw den).sites,
      correction point = stairEvenAltRankCorrection den point)
    (hpoint : (x, y) ∈ (BaseMask.stairEvenAlt.raw den).sites)
    (hoddSite : (x + y) % 2 ≠ 0) (hblack : ¬ StairEvenAltOddWhite den (x, y)) :
    correction (x, y - 1) < correction (x, y) ∧ correction (x, y + 1) < correction (x, y) := by
  by_cases hl : StairEvenAltLeftHigh den (x, y)
  · exact stairEvenAlt_rank_odd_black_left hden hcorrect hpoint hoddSite hblack hl
  · by_cases hr : StairEvenAltRightHigh den (x, y)
    · exact stairEvenAlt_rank_odd_black_right hden hcorrect hpoint hoddSite hblack hl hr
    · exact stairEvenAlt_rank_odd_black_center hden hcorrect hpoint hoddSite hblack hl hr

set_option maxHeartbeats 400000 in
private theorem stairEvenAlt_rank_odd_white {den x y : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {correction : Field} (hcorrect : ∀ point ∈ (BaseMask.stairEvenAlt.raw den).sites,
      correction point = stairEvenAltRankCorrection den point)
    (hperiodic : ∀ step ∈ (reciprocalEvenDeck den).span, Function.Periodic correction step)
    (hpoint : (x, y) ∈ (BaseMask.stairEvenAlt.raw den).sites)
    (hoddSite : (x + y) % 2 ≠ 0) (hwhite : StairEvenAltOddWhite den (x, y)) :
    correction (x, y - 1) < correction (x, y) ∨ correction (x, y + 1) < correction (x, y) := by
  have ⟨hmin, hodd⟩ := hden
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_stairEvenAlt_raw_iff.mp hpoint
  dsimp only at hx hy hshape
  simp only [StairEvenAltOddWhite] at hwhite
  rw [hcorrect _ hpoint]
  have hV := stairEvenAlt_transverse_mem_span hodd
  have hUV := stairEvenAlt_diagonal_mem_span hodd
  by_cases hl : StairEvenAltLeftHigh den (x, y)
  · simp only [StairEvenAltLeftHigh] at hl
    have hdiag : x + y = 1 ∧ 1 ≤ y := by omega
    left
    have hdown : (x, y - 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
    rw [hcorrect _ hdown]
    clear hshape hwhite
    alternate_staircase_rank
  · by_cases hr : StairEvenAltRightHigh den (x, y)
    · simp only [StairEvenAltRightHigh] at hr
      have hdiag : x + y = den + 2 ∧ 2 ≤ y ∧ y ≤ den - 1 := by omega
      left
      have hdown : (x, y - 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
      rw [hcorrect _ hdown]
      clear hshape hwhite
      alternate_staircase_rank
    · simp only [StairEvenAltLeftHigh, StairEvenAltRightHigh] at hl hr
      rcases hwhite with hbottom | htop | hbottom | htop | hlower | hupper | hinner | hinner
      · left
        have hdown : ((x, y - 1) : Site) + (1, den + 2) ∈ (BaseMask.stairEvenAlt.raw den).sites := by
          alternate_staircase_mem
        rw [rankCorrection_add_representative hcorrect hperiodic hUV _ hdown]
        alternate_staircase_rank
      · by_cases htip : x = 3
        · right
          have hup : ((x, y + 1) : Site) - (1, den + 2) ∈ (BaseMask.stairEvenAlt.raw den).sites := by
            alternate_staircase_mem
          rw [rankCorrection_sub_representative hcorrect hperiodic hUV _ hup]
          alternate_staircase_rank
        · left
          have hdown : (x, y - 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
          rw [hcorrect _ hdown]
          alternate_staircase_rank
      · left
        have hdown : ((x, y - 1) : Site) + (1 - den, den + 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by
          alternate_staircase_mem
        rw [rankCorrection_add_representative hcorrect hperiodic hV _ hdown]
        alternate_staircase_rank
      · by_cases htip : x = 3 - den
        · right
          have hup : ((x, y + 1) : Site) - (1 - den, den + 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by
            alternate_staircase_mem
          rw [rankCorrection_sub_representative hcorrect hperiodic hV _ hup]
          alternate_staircase_rank
        · left
          have hdown : (x, y - 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
          rw [hcorrect _ hdown]
          alternate_staircase_rank
      · right
        have hup : (x, y + 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
        rw [hcorrect _ hup]
        alternate_staircase_rank
      · omega
      · have hbottom : y = 0 ∧ x = 1 := by omega
        left
        have hdown : ((x, y - 1) : Site) + (1 - den, den + 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by
          alternate_staircase_mem
        rw [rankCorrection_add_representative hcorrect hperiodic hV _ hdown]
        alternate_staircase_rank
      · right
        by_cases htip : y = den
        · have hup : ((x, y + 1) : Site) - (1 - den, den + 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by
            alternate_staircase_mem
          rw [rankCorrection_sub_representative hcorrect hperiodic hV _ hup]
          alternate_staircase_rank
        · have hup : (x, y + 1) ∈ (BaseMask.stairEvenAlt.raw den).sites := by alternate_staircase_mem
          rw [hcorrect _ hup]
          alternate_staircase_rank

private theorem stairEvenAlt_rank_on_raw {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den)
    {standard correction : Field} (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den))
    (hcorrect : ∀ point ∈ (BaseMask.stairEvenAlt.raw den).sites, correction point = stairEvenAltRankCorrection den point)
    (hperiodic : ∀ step ∈ (reciprocalEvenDeck den).span, Function.Periodic correction step)
    (point : Site) (hpoint : point ∈ (BaseMask.stairEvenAlt.raw den).sites) :
    let rank : Field := fun site => 6 * site.1 + correction site
    let value := laplacian (stairEvenAltField den standard) point
    (value = -1 ∧ rank (incomingNeg point) < rank point ∧ rank (incomingPos point) < rank point) ∨
      (value = 0 ∧ (rank (incomingNeg point) < rank point ∨ rank (incomingPos point) < rank point)) := by
  obtain ⟨x, y⟩ := point
  have hlap := stairEvenAlt_laplacian_on_raw hden hagree hperiod (x, y) hpoint
  by_cases heven : EvenSite (x, y)
  · simp only [incomingNeg, incomingPos, if_pos heven] at hlap ⊢
    by_cases hblack : StairEvenAltEvenBlack den (x, y)
    · exact Or.inl ⟨by simpa only [if_pos hblack] using hlap,
        stairEvenAlt_rank_even_black hden hcorrect hperiodic hpoint heven hblack⟩
    · exact Or.inr ⟨by simpa only [if_neg hblack] using hlap,
        stairEvenAlt_rank_even_white hden hcorrect hperiodic hpoint heven hblack⟩
  · simp only [incomingNeg, incomingPos, if_neg heven] at hlap ⊢
    by_cases hwhite : StairEvenAltOddWhite den (x, y)
    · have hrank := stairEvenAlt_rank_odd_white hden hcorrect hperiodic hpoint heven hwhite
      exact Or.inr ⟨by simpa only [if_pos hwhite] using hlap, by
        simpa only [add_lt_add_iff_left] using hrank⟩
    · have hrank := stairEvenAlt_rank_odd_black hden hcorrect hpoint heven hwhite
      exact Or.inl ⟨by simpa only [if_neg hwhite] using hlap, by
        simpa only [add_lt_add_iff_left] using hrank⟩

/-- The source B3 rank works globally with the physical inputs of the literal height. -/
theorem stairEvenAlt_exists_burningRank {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den) {standard : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees standard 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 (stairEvenConstantV den)) :
    ∃ correction : Field,
      (∀ point ∈ (BaseMask.stairEvenAlt.raw den).sites, correction point = stairEvenAltRankCorrection den point) ∧
      (∀ step ∈ (reciprocalEvenDeck den).span, Function.Periodic correction step) ∧
      IsBurningRank (stairEvenAltField den standard) (fun point => 6 * point.1 + correction point) := by
  obtain ⟨correction, hcorrect, hperiodic⟩ := stairEvenAlt_exists_periodic_rankCorrection hden
  let fraction := Fraction.mk 1 den
  have hinterval : fraction.InUnitInterval := by
    have := hden.1
    exact ⟨by dsimp [fraction]; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp [fraction]; omega⟩
  refine ⟨correction, hcorrect, hperiodic, fun point => ?_⟩
  obtain ⟨site, hsite, hspan⟩ := stairEvenAlt_raw_cover hden point
  let step := point - site
  have hpoint : site + step = point := by dsimp [step]; rw [add_comm, sub_add_cancel]
  have heven : EvenSite step := ((fraction.mem_modifiedDeck_iff step).mp hspan).2
  rw [← hpoint, laplacian_periodic_of_generatorPeriods hinterval (stairEvenAltField_periods hperiod) hspan site,
    incomingNeg_add_of_even site step heven, incomingPos_add_of_even site step heven]
  simp only [hperiodic step hspan site, hperiodic step hspan (incomingNeg site),
    hperiodic step hspan (incomingPos site), Prod.fst_add]
  rcases stairEvenAlt_rank_on_raw hden hagree hperiod hcorrect hperiodic site hsite with
    ⟨h, hn, hp⟩ | ⟨h, hn | hp⟩
  · exact Or.inl ⟨h, by dsimp at hn; omega, by dsimp at hp; omega⟩
  · exact Or.inr ⟨h, Or.inl (by dsimp at hn; omega)⟩
  · exact Or.inr ⟨h, Or.inr (by dsimp at hp; omega)⟩

/-- The raw B3 initializer agrees with a recurrent physical field with the prescribed growth. -/
theorem stairEvenAlt_exists_recurrent_extension {den : ℤ} (hden : BaseMask.stairEvenAlt.Valid den) :
    ∃ field : Field, (BaseMask.stairEvenAlt.raw den).Agrees field 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den - 1) ∧
      HasQuadraticGrowth field (Fraction.mk 1 den).matrix ∧ Superharmonic field ∧ Recurrent field := by
  obtain ⟨standard, hagree, hperiod, _⟩ := stairEven_exists_extension hden
  have halt := stairEvenAltField_periods hperiod
  have hinterval : (Fraction.mk 1 den).InUnitInterval := by
    have := hden.1
    exact ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩
  obtain ⟨_, _, _, hrank⟩ := stairEvenAlt_exists_burningRank hden hagree hperiod
  exact ⟨stairEvenAltField den standard, stairEvenAltField_agrees hden hagree hperiod,
    halt, generator_periods_growth hinterval halt, hrank.superharmonic, hrank.recurrent⟩

end FLatticePaper.Construction
