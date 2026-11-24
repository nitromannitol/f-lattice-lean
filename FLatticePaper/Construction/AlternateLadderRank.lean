import FLatticePaper.Construction.AlternateLadderLaplacian
import FLatticePaper.Construction.AlternateLadderRankCorrection
import FLatticePaper.Construction.AlternateLadderRotation

namespace FLatticePaper.Construction

open Farey

local macro "alternate_ladder_rank" : tactic => `(tactic|
  (simp (disch := omega) only [ladderOddAltRankCorrection, BaseMask.LadderOddAltCorner,
      BaseMask.LadderOddAltDiagonal, LadderOddAltTop, LadderOddAltShelf, LadderOddAltBand,
      LadderOddAltLeftHigh, LadderOddAltRightHigh, LadderOddAltMiddle, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub, if_pos, if_neg]
   repeat' first | omega | (split <;> rename_i hclause <;>
     simp only [true_and, and_true, true_or, or_true, false_and, and_false, false_or, or_false,
       not_true_eq_false, not_false_eq_true] at hclause)))

local macro "alternate_ladder_mem" : tactic => `(tactic|
  (apply BaseMask.mem_ladderOddAlt_raw_iff.mpr
   simp only [BaseMask.LadderOddAltCorner, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
   omega))

private theorem kernel_mem_span {den : ℤ} (hd : den % 2 = 0) :
    (2 * den, 2) ∈ (reciprocalLadderDeck den).span := by
  rw [reciprocalLadderDeck_eq hd]
  exact ⟨1, 0, by apply Prod.ext <;> simp [PeriodDeck.combine]⟩

private theorem transverse_mem_span {den : ℤ} (hd : den % 2 = 0) :
    (1 - den, den + 1) ∈ (reciprocalLadderDeck den).span := by
  rw [reciprocalLadderDeck_eq hd]
  exact ⟨0, 1, by apply Prod.ext <;> simp [PeriodDeck.combine, add_comm 1 den]⟩

private theorem rankCorrection_add_representative {den : ℤ} {correction : Field}
    (hcorrect : ∀ point ∈ (BaseMask.ladderOddAlt.raw den).sites, correction point = ladderOddAltRankCorrection den point)
    (hper : ∀ step ∈ (reciprocalLadderDeck den).span, Function.Periodic correction step)
    {step : Site} (hstep : step ∈ (reciprocalLadderDeck den).span) (point : Site)
    (hmem : point + step ∈ (BaseMask.ladderOddAlt.raw den).sites) :
    correction point = ladderOddAltRankCorrection den (point + step) :=
  (hper step hstep point).symm.trans (hcorrect _ hmem)

private theorem rankCorrection_sub_representative {den : ℤ} {correction : Field}
    (hcorrect : ∀ point ∈ (BaseMask.ladderOddAlt.raw den).sites, correction point = ladderOddAltRankCorrection den point)
    (hper : ∀ step ∈ (reciprocalLadderDeck den).span, Function.Periodic correction step)
    {step : Site} (hstep : step ∈ (reciprocalLadderDeck den).span) (point : Site)
    (hmem : point - step ∈ (BaseMask.ladderOddAlt.raw den).sites) :
    correction point = ladderOddAltRankCorrection den (point - step) := by
  have h := hper step hstep (point - step)
  rw [sub_add_cancel] at h
  exact h.trans (hcorrect _ hmem)

set_option maxHeartbeats 400000 in
private theorem ladderOddAlt_rank_even_black {den x y : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    {correction : Field} (hcorrect : ∀ point ∈ (BaseMask.ladderOddAlt.raw den).sites,
      correction point = ladderOddAltRankCorrection den point)
    (hpoint : (x, y) ∈ (BaseMask.ladderOddAlt.raw den).sites)
    (heven : (x + y) % 2 = 0) (hblack : LadderOddAltEvenBlack den (x, y)) :
    6 * (x - 1) + correction (x - 1, y) < 6 * x + correction (x, y) ∧
      6 * (x + 1) + correction (x + 1, y) < 6 * x + correction (x, y) := by
  have ⟨hmin, hd⟩ := hden
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hpoint
  simp only [BaseMask.LadderOddAltCorner] at hshape
  simp only [LadderOddAltEvenBlack, BaseMask.LadderOddAltDiagonal] at hblack
  dsimp only at hx hy
  have hn : (x - 1, y) ∈ (BaseMask.ladderOddAlt.raw den).sites := by alternate_ladder_mem
  have hp : (x + 1, y) ∈ (BaseMask.ladderOddAlt.raw den).sites := by alternate_ladder_mem
  rw [hcorrect _ hpoint, hcorrect _ hn, hcorrect _ hp]
  clear hn hp hpoint hcorrect hshape
  rcases hblack with hleft | hright | hdiag
  · constructor <;> alternate_ladder_rank
  · by_cases hlast : y = den + 1 <;> constructor <;> alternate_ladder_rank
  · by_cases hend : x = den - 2 <;> constructor <;> alternate_ladder_rank

set_option maxHeartbeats 400000 in
/-- The default case of the even white B7 rank: the lower left neighbour is not in the raw mask's left boundary. -/
private theorem ladderOddAlt_even_white_default {den x y : ℤ} {correction : Field}
    (hden : BaseMask.ladderOddAlt.Valid den)
    (hcorrect : ∀ point ∈ (BaseMask.ladderOddAlt.raw den).sites,
      correction point = ladderOddAltRankCorrection den point)
    (hpoint : (x, y) ∈ (BaseMask.ladderOddAlt.raw den).sites)
    (heven : (x + y) % 2 = 0)
    (hs : ¬ (x = 1 - den ∧ y = den - 1))
    (hc : ¬ BaseMask.LadderOddAltCorner den (x, y))
    (htop : ¬ LadderOddAltTop den (x, y)) (hband : ¬ LadderOddAltBand den (x, y))
    (hleft : ¬ LadderOddAltLeftHigh den (x, y)) (hright : ¬ LadderOddAltRightHigh den (x, y))
    (hwhite : ¬ LadderOddAltEvenBlack den (x, y)) :
    6 * (x - 1) + correction (x - 1, y) < 6 * x + correction (x, y) := by
  have ⟨hmin, hd⟩ := hden
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hpoint
  dsimp only at hx hy
  have hbody := hshape.resolve_left hc
  clear hshape
  dsimp only at hbody
  rw [hcorrect _ hpoint]
  have hn : (x - 1, y) ∈ (BaseMask.ladderOddAlt.raw den).sites := not_not.mp (fun h => by
    rcases (ladderOddAlt_left_notMem_iff hden hpoint heven).mp h with h | h | h
    · exact hc (Or.inl h)
    · exact htop ⟨h.2, by omega, by omega⟩
    · exact hs h)
  rw [hcorrect _ hn]
  simp only [LadderOddAltTop, LadderOddAltBand,
    LadderOddAltLeftHigh, LadderOddAltRightHigh, BaseMask.LadderOddAltCorner,
    LadderOddAltEvenBlack, BaseMask.LadderOddAltDiagonal] at hwhite hc htop hband hleft hright
  by_cases hshelf : LadderOddAltShelf den (x, y)
  · simp only [LadderOddAltShelf] at hshelf
    alternate_ladder_rank
  by_cases hmid : LadderOddAltMiddle den (x, y)
  · simp only [LadderOddAltMiddle] at hmid
    alternate_ladder_rank
  simp only [LadderOddAltShelf, LadderOddAltMiddle] at hshelf hmid
  have hdefault : x < 0 ∨ y = -1 ∨ (x = 0 ∧ y = den) := by omega
  rcases hdefault with h | h | h <;> alternate_ladder_rank

set_option maxHeartbeats 400000 in
private theorem ladderOddAlt_rank_even_white {den x y : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    {correction : Field} (hcorrect : ∀ point ∈ (BaseMask.ladderOddAlt.raw den).sites,
      correction point = ladderOddAltRankCorrection den point)
    (hper : ∀ step ∈ (reciprocalLadderDeck den).span, Function.Periodic correction step)
    (hpoint : (x, y) ∈ (BaseMask.ladderOddAlt.raw den).sites)
    (heven : (x + y) % 2 = 0) (hwhite : ¬ LadderOddAltEvenBlack den (x, y)) :
    6 * (x - 1) + correction (x - 1, y) < 6 * x + correction (x, y) ∨
      6 * (x + 1) + correction (x + 1, y) < 6 * x + correction (x, y) := by
  have ⟨hmin, hd⟩ := hden
  have hU := kernel_mem_span hd
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hpoint
  dsimp only at hx hy
  rw [hcorrect _ hpoint]
  by_cases hc : BaseMask.LadderOddAltCorner den (x, y)
  · left
    rcases hc with h | h
    · have hn : ((x - 1, y) : Site) + (2 * den, 2) ∈ (BaseMask.ladderOddAlt.raw den).sites := by
        alternate_ladder_mem
      rw [rankCorrection_add_representative hcorrect hper hU _ hn]
      alternate_ladder_rank
    · have hn : (x - 1, y) ∈ (BaseMask.ladderOddAlt.raw den).sites := by alternate_ladder_mem
      rw [hcorrect _ hn]
      alternate_ladder_rank
  clear hshape
  by_cases htop : LadderOddAltTop den (x, y)
  · simp only [LadderOddAltTop] at htop
    right
    have hp : (x + 1, y) ∈ (BaseMask.ladderOddAlt.raw den).sites := by alternate_ladder_mem
    rw [hcorrect _ hp]
    alternate_ladder_rank
  by_cases hband : LadderOddAltBand den (x, y)
  · simp only [LadderOddAltBand] at hband
    right
    by_cases hend : x = 2 * den - 2
    · have hp : ((x + 1, y) : Site) - (2 * den, 2) ∈ (BaseMask.ladderOddAlt.raw den).sites := by
        alternate_ladder_mem
      rw [rankCorrection_sub_representative hcorrect hper hU _ hp]
      alternate_ladder_rank
    · have hp : (x + 1, y) ∈ (BaseMask.ladderOddAlt.raw den).sites := by alternate_ladder_mem
      rw [hcorrect _ hp]
      alternate_ladder_rank
  by_cases hleft : LadderOddAltLeftHigh den (x, y)
  · simp only [LadderOddAltLeftHigh] at hleft
    right
    have hp : (x + 1, y) ∈ (BaseMask.ladderOddAlt.raw den).sites := by alternate_ladder_mem
    rw [hcorrect _ hp]
    alternate_ladder_rank
  by_cases hright : LadderOddAltRightHigh den (x, y)
  · simp only [LadderOddAltRightHigh] at hright
    right
    have hp : (x + 1, y) ∈ (BaseMask.ladderOddAlt.raw den).sites := by alternate_ladder_mem
    rw [hcorrect _ hp]
    alternate_ladder_rank
  left
  by_cases hs : x = 1 - den ∧ y = den - 1
  · have hn : ((x - 1, y) : Site) + (2 * den, 2) ∈ (BaseMask.ladderOddAlt.raw den).sites := by
      alternate_ladder_mem
    rw [rankCorrection_add_representative hcorrect hper hU _ hn]
    alternate_ladder_rank
  · rw [← hcorrect _ hpoint]
    exact ladderOddAlt_even_white_default hden hcorrect hpoint heven hs hc htop hband hleft hright hwhite

private theorem ladderOddAlt_up_notMem_iff {den x y : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    (hsite : (x, y) ∈ (BaseMask.ladderOddAlt.raw den).sites) (hodd : ¬ EvenSite (x, y)) :
    (x, y + 1) ∉ (BaseMask.ladderOddAlt.raw den).sites ↔
      LadderOddAltLowerExit den (reflectLadderOddAlt den (x, y)) := by
  have href := (reflectLadderOddAlt_mem_iff den (x, y)).mpr hsite
  have hpar : ¬ EvenSite (reflectLadderOddAlt den (x, y)) :=
    fun h => hodd ((evenSite_reflectLadderOddAlt_iff den (x, y)).mp h)
  have hshift : reflectLadderOddAlt den (x, y + 1) = (den - 1 - x, den + 1 - y - 1) :=
    Prod.ext rfl (by dsimp [reflectLadderOddAlt]; omega)
  rw [← reflectLadderOddAlt_mem_iff den (x, y + 1), hshift]
  exact ladderOddAlt_down_notMem_iff hden href hpar

set_option maxHeartbeats 400000 in
/-- The rows of the odd black case of the B7 ladder. -/
private theorem ladderOddAlt_odd_black_rows {den x y : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    (hpoint : (x, y) ∈ (BaseMask.ladderOddAlt.raw den).sites) (hodd : ¬ EvenSite (x, y))
    (hblack : ¬ LadderOddAltOddWhite den (x, y)) : 0 ≤ y ∧ y ≤ den + 1 := by
  have ⟨hmin, hd⟩ := hden
  have hxy : (x + y) % 2 ≠ 0 := hodd
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hpoint
  dsimp only at hx hy
  have hbody := hshape.resolve_left (by clear hblack; simp only [BaseMask.LadderOddAltCorner]; omega)
  dsimp only at hbody
  have hb1 : ¬ LadderOddAltLowerExit den (x, y) := fun h => hblack (Or.inl h)
  have hb2 : ¬ LadderOddAltLowerExit den (reflectLadderOddAlt den (x, y)) :=
    fun h => hblack (Or.inr (Or.inl h))
  clear hblack hshape
  simp only [LadderOddAltLowerExit, reflectLadderOddAlt, Prod.fst_sub, Prod.snd_sub] at hb1 hb2
  omega

set_option maxHeartbeats 400000 in
/-- The ends of the left-high segment of the odd black case. -/
private theorem ladderOddAlt_odd_black_xEnds {den x y : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    (hpoint : (x, y) ∈ (BaseMask.ladderOddAlt.raw den).sites) (hodd : ¬ EvenSite (x, y))
    (hblack : ¬ LadderOddAltOddWhite den (x, y))
    (hl : LadderOddAltLeftHigh den (x, y)) (hout : x + y = den - 1) :
    x = 0 ∨ x = den - 1 := by
  have ⟨hmin, hd⟩ := hden
  have hxy : (x + y) % 2 ≠ 0 := hodd
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hpoint
  dsimp only at hx hy
  have hbody := hshape.resolve_left (by clear hblack; simp only [BaseMask.LadderOddAltCorner]; omega)
  dsimp only at hbody
  simp only [LadderOddAltOddWhite, LadderOddAltLowerExit, reflectLadderOddAlt, Prod.fst_sub,
    Prod.snd_sub] at hblack
  simp only [LadderOddAltLeftHigh] at hl
  omega

set_option maxHeartbeats 400000 in
/-- The row bound of the right-high segment of the odd black case. -/
private theorem ladderOddAlt_odd_black_row {den x y : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    (hpoint : (x, y) ∈ (BaseMask.ladderOddAlt.raw den).sites) (hodd : ¬ EvenSite (x, y))
    (hblack : ¬ LadderOddAltOddWhite den (x, y))
    (hs : ¬ LadderOddAltShelf den (x, y)) (hl : ¬ LadderOddAltLeftHigh den (x, y))
    (hr : LadderOddAltRightHigh den (x, y)) :
    2 ≤ y ∧ x ≤ 2 * den - 3 := by
  have ⟨hmin, hd⟩ := hden
  have hxy : (x + y) % 2 ≠ 0 := hodd
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hpoint
  dsimp only at hx hy
  have hbody := hshape.resolve_left (by clear hblack; simp only [BaseMask.LadderOddAltCorner]; omega)
  dsimp only at hbody
  simp only [LadderOddAltOddWhite, LadderOddAltLowerExit, reflectLadderOddAlt, Prod.fst_sub,
    Prod.snd_sub] at hblack
  simp only [LadderOddAltShelf] at hs
  simp only [LadderOddAltLeftHigh] at hl
  simp only [LadderOddAltRightHigh] at hr
  clear hbody
  omega

set_option maxHeartbeats 400000 in
/-- The spine of the right-high segment of the odd black case. -/
private theorem ladderOddAlt_odd_black_xSpine {den x y : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    (hpoint : (x, y) ∈ (BaseMask.ladderOddAlt.raw den).sites) (hodd : ¬ EvenSite (x, y))
    (_hblack : ¬ LadderOddAltOddWhite den (x, y))
    (_hrow : 2 ≤ y ∧ x ≤ 2 * den - 3) (hdRow : y = den)
    (hr : LadderOddAltRightHigh den (x, y)) (_hs : ¬ LadderOddAltShelf den (x, y))
    (_hl : ¬ LadderOddAltLeftHigh den (x, y)) :
    x = den - 1 := by
  have ⟨hmin, hd⟩ := hden
  have hxy : (x + y) % 2 ≠ 0 := hodd
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hpoint
  dsimp only at hx hy
  have hbody := hshape.resolve_left (by clear _hblack; simp only [BaseMask.LadderOddAltCorner]; omega)
  dsimp only at hbody
  simp only [LadderOddAltRightHigh] at hr
  omega

set_option maxHeartbeats 400000 in
/-- The far bound of the middle segment of the odd black case. -/
private theorem ladderOddAlt_odd_black_far {den x y : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    (hpoint : (x, y) ∈ (BaseMask.ladderOddAlt.raw den).sites) (hodd : ¬ EvenSite (x, y))
    (hblack : ¬ LadderOddAltOddWhite den (x, y))
    (hm : LadderOddAltMiddle den (x, y)) (hr : ¬ LadderOddAltRightHigh den (x, y))
    (hs : ¬ LadderOddAltShelf den (x, y)) (hl : ¬ LadderOddAltLeftHigh den (x, y)) :
    den + 3 ≤ x + y := by
  have ⟨hmin, hd⟩ := hden
  have hxy : (x + y) % 2 ≠ 0 := hodd
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hpoint
  dsimp only at hx hy
  have hbody := hshape.resolve_left (by clear hblack; simp only [BaseMask.LadderOddAltCorner]; omega)
  dsimp only at hbody
  simp only [LadderOddAltOddWhite, LadderOddAltLowerExit, reflectLadderOddAlt, Prod.fst_sub,
    Prod.snd_sub] at hblack
  simp only [LadderOddAltMiddle] at hm
  simp only [LadderOddAltShelf] at hs
  simp only [LadderOddAltLeftHigh] at hl
  simp only [LadderOddAltRightHigh] at hr
  omega

set_option maxHeartbeats 400000 in
/-- The default region of the odd black case of the B7 ladder: the left strip with the vertical bounds. -/
private theorem ladderOddAlt_odd_black_default {den x y : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    (hpoint : (x, y) ∈ (BaseMask.ladderOddAlt.raw den).sites) (hodd : ¬ EvenSite (x, y))
    (hblack : ¬ LadderOddAltOddWhite den (x, y))
    (hs : ¬ LadderOddAltShelf den (x, y)) (hl : ¬ LadderOddAltLeftHigh den (x, y))
    (hr : ¬ LadderOddAltRightHigh den (x, y)) (hm : ¬ LadderOddAltMiddle den (x, y)) :
    x < 0 ∧ 1 ≤ y ∧ y ≤ den - 1 := by
  have ⟨hmin, hd⟩ := hden
  have hxy : (x + y) % 2 ≠ 0 := hodd
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hpoint
  dsimp only at hx hy
  have hbody := hshape.resolve_left (by clear hblack; simp only [BaseMask.LadderOddAltCorner]; omega)
  dsimp only at hbody
  have hb1 : ¬ LadderOddAltLowerExit den (x, y) := fun h => hblack (Or.inl h)
  have hb2 : ¬ LadderOddAltLowerExit den (reflectLadderOddAlt den (x, y)) :=
    fun h => hblack (Or.inr (Or.inl h))
  have hb3 : ¬ (x = -1 ∧ y = 0) := fun h => hblack (Or.inr (Or.inr (Or.inl h)))
  have hb4 : ¬ (x = den ∧ y = den + 1) := fun h => hblack (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have hb5 : ¬ (1 ≤ x ∧ x ≤ den - 2 ∧ (x + y = den - 1 ∨ x + y = den + 1)) :=
    fun h => hblack (Or.inr (Or.inr (Or.inr (Or.inr h))))
  clear hblack hshape
  simp only [LadderOddAltLowerExit, reflectLadderOddAlt, Prod.fst_sub, Prod.snd_sub] at hb1 hb2
  simp only [LadderOddAltShelf] at hs
  simp only [LadderOddAltLeftHigh] at hl
  simp only [LadderOddAltRightHigh] at hr
  simp only [LadderOddAltMiddle] at hm
  have hcases : y = -1 ∨ y = 0 ∨ y = den + 2 ∨ y = den + 1 ∨ y = den ∨ (1 ≤ y ∧ y ≤ den - 1) := by
    clear hs hl hr hm hb1 hb2 hb3 hb4 hb5 hbody; omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | ⟨h1, h2⟩
  · clear hs hl hr hm hb2 hb3 hb4 hb5; omega
  · clear hs hr hm hb1 hb2 hb4 hb5; omega
  · clear hs hl hr hm hb1 hb3 hb4 hb5; omega
  · clear hl hr hm hb1 hb2 hb3 hb5; omega
  · clear hb1 hb3 hb4 hb5; omega
  · clear hb1 hb3 hb4 hb5; omega

set_option maxHeartbeats 400000 in
private theorem ladderOddAlt_rank_odd_black {den x y : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    {correction : Field} (hcorrect : ∀ point ∈ (BaseMask.ladderOddAlt.raw den).sites,
      correction point = ladderOddAltRankCorrection den point)
    (hpoint : (x, y) ∈ (BaseMask.ladderOddAlt.raw den).sites)
    (hodd : ¬ EvenSite (x, y)) (hblack : ¬ LadderOddAltOddWhite den (x, y)) :
    correction (x, y - 1) < correction (x, y) ∧ correction (x, y + 1) < correction (x, y) := by
  have ⟨hmin, hd⟩ := hden
  have hxy : (x + y) % 2 ≠ 0 := hodd
  have hn : (x, y - 1) ∈ (BaseMask.ladderOddAlt.raw den).sites := not_not.mp fun h =>
    hblack (Or.inl ((ladderOddAlt_down_notMem_iff hden hpoint hxy).mp h))
  have hp : (x, y + 1) ∈ (BaseMask.ladderOddAlt.raw den).sites := not_not.mp fun h =>
    hblack (Or.inr (Or.inl ((ladderOddAlt_up_notMem_iff hden hpoint hodd).mp h)))
  obtain ⟨hx, hy, -⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hpoint
  dsimp only at hx hy
  have hrows := ladderOddAlt_odd_black_rows hden hpoint hodd hblack
  rw [hcorrect _ hpoint, hcorrect _ hn, hcorrect _ hp]
  clear hcorrect hn hp
  by_cases hs : LadderOddAltShelf den (x, y)
  · simp only [LadderOddAltShelf] at hs
    clear hblack
    by_cases hx0 : x = 0 <;> constructor <;> alternate_ladder_rank
  by_cases hl : LadderOddAltLeftHigh den (x, y)
  · by_cases hout : x + y = den - 1
    · have hxEnds := ladderOddAlt_odd_black_xEnds hden hpoint hodd hblack hl hout
      simp only [LadderOddAltLeftHigh] at hl
      clear hblack
      rcases hxEnds with h | h <;> constructor <;> alternate_ladder_rank
    · simp only [LadderOddAltLeftHigh] at hl
      clear hblack
      by_cases hy0 : y = 0 <;> constructor <;> alternate_ladder_rank
  by_cases hr : LadderOddAltRightHigh den (x, y)
  · have hrow := ladderOddAlt_odd_black_row hden hpoint hodd hblack hs hl hr
    by_cases hdRow : y = den
    · have hxSpine := ladderOddAlt_odd_black_xSpine hden hpoint hodd hblack hrow hdRow hr hs hl
      simp only [LadderOddAltRightHigh] at hr
      clear hblack
      constructor <;> alternate_ladder_rank
    · simp only [LadderOddAltRightHigh] at hr
      clear hblack
      by_cases hlast : x + y = 2 * den - 1 <;> constructor <;> alternate_ladder_rank
  by_cases hm : LadderOddAltMiddle den (x, y)
  · have hfar := ladderOddAlt_odd_black_far hden hpoint hodd hblack hm hr hs hl
    simp only [LadderOddAltMiddle] at hm
    clear hblack
    by_cases hlast : y = den <;> constructor <;> alternate_ladder_rank
  have hdefault := ladderOddAlt_odd_black_default hden hpoint hodd hblack hs hl hr hm
  simp only [LadderOddAltShelf, LadderOddAltLeftHigh, LadderOddAltRightHigh, LadderOddAltMiddle] at hs hl hr hm
  clear hblack
  constructor <;> alternate_ladder_rank

set_option maxHeartbeats 400000 in
private theorem ladderOddAlt_rank_odd_white {den x y : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    {correction : Field} (hcorrect : ∀ point ∈ (BaseMask.ladderOddAlt.raw den).sites,
      correction point = ladderOddAltRankCorrection den point)
    (hper : ∀ step ∈ (reciprocalLadderDeck den).span, Function.Periodic correction step)
    (hpoint : (x, y) ∈ (BaseMask.ladderOddAlt.raw den).sites)
    (hodd : ¬ EvenSite (x, y)) (hwhite : LadderOddAltOddWhite den (x, y)) :
    correction (x, y - 1) < correction (x, y) ∨ correction (x, y + 1) < correction (x, y) := by
  have ⟨hmin, hd⟩ := hden
  have hxy : (x + y) % 2 ≠ 0 := hodd
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_ladderOddAlt_raw_iff.mp hpoint
  dsimp only at hx hy
  simp only [BaseMask.LadderOddAltCorner] at hshape
  have hU := kernel_mem_span hd
  have hV := transverse_mem_span hd
  rw [hcorrect _ hpoint]
  by_cases hlo : LadderOddAltLowerExit den (x, y)
  · simp only [LadderOddAltLowerExit] at hlo
    rcases hlo with hbottom | hdiag | hshelf
    · left
      have hn : ((x, y - 1) : Site) + (1 - den, den + 1) ∈ (BaseMask.ladderOddAlt.raw den).sites := by
        alternate_ladder_mem
      rw [rankCorrection_add_representative hcorrect hper hV _ hn]
      clear hshape
      alternate_ladder_rank
    · right
      have hp : (x, y + 1) ∈ (BaseMask.ladderOddAlt.raw den).sites := by alternate_ladder_mem
      rw [hcorrect _ hp]
      clear hshape
      alternate_ladder_rank
    · right
      have hp : (x, y + 1) ∈ (BaseMask.ladderOddAlt.raw den).sites := by alternate_ladder_mem
      rw [hcorrect _ hp]
      clear hshape
      by_cases hend : x = 2 * den - 2 <;> alternate_ladder_rank
  by_cases hup : LadderOddAltLowerExit den (reflectLadderOddAlt den (x, y))
  · simp only [LadderOddAltLowerExit, reflectLadderOddAlt, Prod.fst_sub, Prod.snd_sub] at hup
    rcases hup with htop | hdiag | hshelf
    · right
      have hp : ((x, y + 1) : Site) - (1 - den, den + 1) ∈ (BaseMask.ladderOddAlt.raw den).sites := by
        alternate_ladder_mem
      rw [rankCorrection_sub_representative hcorrect hper hV _ hp]
      clear hshape
      by_cases hend : x = den - 1 <;> alternate_ladder_rank
    · right
      have hp : ((x, y + 1) : Site) - (2 * den, 2) ∈ (BaseMask.ladderOddAlt.raw den).sites := by
        alternate_ladder_mem
      rw [rankCorrection_sub_representative hcorrect hper hU _ hp]
      clear hshape
      alternate_ladder_rank
    · left
      have hn : (x, y - 1) ∈ (BaseMask.ladderOddAlt.raw den).sites := by alternate_ladder_mem
      rw [hcorrect _ hn]
      clear hshape
      alternate_ladder_rank
  simp only [LadderOddAltOddWhite, hlo, hup, false_or] at hwhite
  rcases hwhite with ha | he | ⟨hx₀, hx₁, hdiag | hdiag⟩
  · right
    have hp : (x, y + 1) ∈ (BaseMask.ladderOddAlt.raw den).sites := by alternate_ladder_mem
    rw [hcorrect _ hp]
    alternate_ladder_rank
  · right
    have hp : (x, y + 1) ∈ (BaseMask.ladderOddAlt.raw den).sites := by
      refine BaseMask.mem_ladderOddAlt_raw_iff.mpr ⟨?_, ?_, Or.inl (Or.inr ?_)⟩ <;> omega
    rw [hcorrect _ hp]
    alternate_ladder_rank
  · left
    have hn : (x, y - 1) ∈ (BaseMask.ladderOddAlt.raw den).sites := by alternate_ladder_mem
    rw [hcorrect _ hn]
    clear hshape
    alternate_ladder_rank
  · right
    have hp : (x, y + 1) ∈ (BaseMask.ladderOddAlt.raw den).sites := by alternate_ladder_mem
    rw [hcorrect _ hp]
    clear hshape
    by_cases hend : y = den <;> alternate_ladder_rank

private theorem ladderOddAlt_rank_on_raw {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den)
    {field correction : Field} (hagree : (BaseMask.ladderOddAlt.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field (-1) (ladderOddAltConstantV den))
    (hcorrect : ∀ point ∈ (BaseMask.ladderOddAlt.raw den).sites, correction point = ladderOddAltRankCorrection den point)
    (hper : ∀ step ∈ (reciprocalLadderDeck den).span, Function.Periodic correction step)
    (point : Site) (hpoint : point ∈ (BaseMask.ladderOddAlt.raw den).sites) :
    let rank : Field := fun site => 6 * site.1 + correction site
    let value := laplacian field point
    (value = -1 ∧ rank (incomingNeg point) < rank point ∧ rank (incomingPos point) < rank point) ∨
      (value = 0 ∧ (rank (incomingNeg point) < rank point ∨ rank (incomingPos point) < rank point)) := by
  obtain ⟨x, y⟩ := point
  by_cases heven : EvenSite (x, y)
  · have hlap := ladderOddAlt_laplacian_on_even_raw hden hagree hperiod (x, y) hpoint heven
    simp only [incomingNeg, incomingPos, if_pos heven]
    by_cases hblack : LadderOddAltEvenBlack den (x, y)
    · exact Or.inl ⟨by simpa only [if_pos hblack] using hlap,
        ladderOddAlt_rank_even_black hden hcorrect hpoint heven hblack⟩
    · exact Or.inr ⟨by simpa only [if_neg hblack] using hlap,
        ladderOddAlt_rank_even_white hden hcorrect hper hpoint heven hblack⟩
  · have hlap := ladderOddAlt_laplacian_on_odd_raw hden hagree hperiod (x, y) hpoint heven
    simp only [incomingNeg, incomingPos, if_neg heven]
    by_cases hwhite : LadderOddAltOddWhite den (x, y)
    · have hrank := ladderOddAlt_rank_odd_white hden hcorrect hper hpoint heven hwhite
      exact Or.inr ⟨by simpa only [if_pos hwhite] using hlap, by
        simpa only [add_lt_add_iff_left] using hrank⟩
    · have hrank := ladderOddAlt_rank_odd_black hden hcorrect hpoint heven hwhite
      exact Or.inl ⟨by simpa only [if_neg hwhite] using hlap, by
        simpa only [add_lt_add_iff_left] using hrank⟩

/-- The source's B7 correction gives the required decreases on the physical plane. -/
theorem ladderOddAlt_exists_burningRank {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den) {field : Field}
    (hagree : (BaseMask.ladderOddAlt.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field (-1) (ladderOddAltConstantV den)) :
    ∃ correction : Field,
      (∀ point ∈ (BaseMask.ladderOddAlt.raw den).sites, correction point = ladderOddAltRankCorrection den point) ∧
      (∀ step ∈ (reciprocalLadderDeck den).span, Function.Periodic correction step) ∧
      IsBurningRank field (fun point => 6 * point.1 + correction point) := by
  obtain ⟨correction, hcorrect, hper⟩ := ladderOddAlt_exists_periodic_rankCorrection hden
  let fraction := Fraction.mk 1 den
  have hinterval : fraction.InUnitInterval := by
    have := hden.1
    exact ⟨by dsimp [fraction]; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp [fraction]; omega⟩
  refine ⟨correction, hcorrect, hper, fun point => ?_⟩
  obtain ⟨site, hsite, hspan⟩ := ladderOddAlt_raw_cover hden point
  let step := point - site
  have hpoint : site + step = point := by dsimp [step]; rw [add_comm, sub_add_cancel]
  have heven : EvenSite step := ((fraction.mem_modifiedDeck_iff step).mp hspan).2
  rw [← hpoint, laplacian_periodic_of_generatorPeriods hinterval hperiod hspan site,
    incomingNeg_add_of_even site step heven, incomingPos_add_of_even site step heven]
  simp only [hper step hspan site, hper step hspan (incomingNeg site),
    hper step hspan (incomingPos site), Prod.fst_add]
  rcases ladderOddAlt_rank_on_raw hden hagree hperiod hcorrect hper site hsite with
    ⟨h, hn, hp⟩ | ⟨h, hn | hp⟩
  · exact Or.inl ⟨h, by dsimp at hn; omega, by dsimp at hp; omega⟩
  · exact Or.inr ⟨h, Or.inl (by dsimp at hn; omega)⟩
  · exact Or.inr ⟨h, Or.inr (by dsimp at hp; omega)⟩

theorem ladderOddAlt_exists_recurrent_extension {den : ℤ} (hden : BaseMask.ladderOddAlt.Valid den) :
    ∃ field : Field, (BaseMask.ladderOddAlt.raw den).Agrees field 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 den) field (-1) (ladderOddAltConstantV den) ∧
      HasQuadraticGrowth field (Fraction.mk 1 den).matrix ∧ Superharmonic field ∧ Recurrent field := by
  obtain ⟨field, hagree, hperiod, hgrowth⟩ := ladderOddAlt_exists_extension hden
  obtain ⟨_, _, _, hrank⟩ := ladderOddAlt_exists_burningRank hden hagree hperiod
  exact ⟨field, hagree, hperiod, hgrowth, hrank.superharmonic, hrank.recurrent⟩

theorem ladderEvenAlt_exists_recurrent_extension {den : ℤ} (hden : BaseMask.ladderEvenAlt.Valid den) :
    ∃ field : Field,
      ((BaseMask.ladderEvenAlt.tile den hden).llCenter (BaseMask.ladderEvenAlt.tile_nonempty den hden)).Agrees field 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 den).rotate field 0 (ladderEvenAltConstantV den) ∧
      HasQuadraticGrowth field (Fraction.mk 1 den).rotate.matrix ∧ Superharmonic field ∧ Recurrent field := by
  obtain ⟨field, hagree, hperiod, _, hsuper, hrec⟩ := ladderOddAlt_exists_recurrent_extension hden
  have hrot := rotateLadderAltField_periods hden.2 hperiod
  exact ⟨rotateLadderAltField den field, BaseMask.ladderEvenAlt_agrees_rotateLadderAltField hden hagree,
    hrot, generator_periods_growth (ladder_rotate_inUnitInterval hden.1 hden.2) hrot,
    rotateLadderAltField_recurrent hrec hsuper⟩

theorem evaluateNative_threes_odd_alternate_recurrent (extra : ℕ) :
    let word := (BaseRun.threes extra).word
    let den : ℤ := 2 * (extra : ℤ) + 3 + 1
    let fraction := (parentsAt word).current .odd
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative word = .ok registers ∧
      registers.alternate.currentOdd.val.Agrees (fun site => field (site + (-1, -1))) 0 ∧
      HasGeneratorPeriods fraction field (-1) (ladderOddAltConstantV den) ∧
      HasQuadraticGrowth field fraction.matrix ∧ Superharmonic field ∧ Recurrent field := by
  dsimp only
  rw [threes_current_odd]
  have hvalid : BaseMask.ladderOddAlt.Valid (2 * (extra : ℤ) + 3 + 1) := by
    change 4 ≤ 2 * (extra : ℤ) + 3 + 1 ∧ (2 * (extra : ℤ) + 3 + 1) % 2 = 0
    omega
  obtain ⟨field, hagree, hperiod, hgrowth, hsuper, hrec⟩ := ladderOddAlt_exists_recurrent_extension hvalid
  exact ⟨(BaseRun.threes extra).registers.llCenter, field, evaluateNative_base _,
    BaseMask.ladderOddAlt_llCenter_agrees hvalid hagree, hperiod, hgrowth, hsuper, hrec⟩

theorem evaluateNative_twos_even_alternate_recurrent (extra : ℕ) :
    let word := (BaseRun.twos extra).word
    let den : ℤ := 2 * (extra : ℤ) + 3 + 1
    let fraction := (parentsAt word).current .even
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative word = .ok registers ∧ registers.alternate.currentEven.val.Agrees field 0 ∧
      HasGeneratorPeriods fraction field 0 (ladderEvenAltConstantV den) ∧
      HasQuadraticGrowth field fraction.matrix ∧ Superharmonic field ∧ Recurrent field := by
  dsimp only
  rw [twos_current_even]
  have hvalid : BaseMask.ladderEvenAlt.Valid (2 * (extra : ℤ) + 3 + 1) := by
    change 4 ≤ 2 * (extra : ℤ) + 3 + 1 ∧ (2 * (extra : ℤ) + 3 + 1) % 2 = 0
    omega
  obtain ⟨field, hagree, hperiod, hgrowth, hsuper, hrec⟩ := ladderEvenAlt_exists_recurrent_extension hvalid
  exact ⟨(BaseRun.twos extra).registers.llCenter, field, evaluateNative_base _,
    hagree, hperiod, hgrowth, hsuper, hrec⟩

end FLatticePaper.Construction
