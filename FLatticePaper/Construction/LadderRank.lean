import FLatticePaper.Construction.LadderLaplacian
import FLatticePaper.Construction.LadderRankCorrection
import FLatticePaper.Construction.LadderRotation

namespace FLatticePaper.Construction

open Farey

local macro "ladder_rank" : tactic => `(tactic|
  (simp (disch := omega) only [ladderOddRankCorrection, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub, if_pos, if_neg]
   repeat' first | omega | (split <;> rename_i hclause <;>
     simp only [true_and, and_true, true_or, or_true, false_and, and_false, false_or, or_false,
       not_true_eq_false, not_false_eq_true] at hclause)))

local macro "ladder_mem" : tactic => `(tactic|
  (apply BaseMask.mem_ladderOdd_raw_iff.mpr
   simp only [BaseMask.LadderOddCorner, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
   omega))

private theorem ladderOdd_kernel_mem_span {den : ℤ} (hd : den % 2 = 0) :
    (2 * den, 2) ∈ (reciprocalLadderDeck den).span := by
  rw [reciprocalLadderDeck_eq hd]
  exact ⟨1, 0, by apply Prod.ext <;> simp [PeriodDeck.combine]⟩

private theorem ladderOdd_transverse_mem_span {den : ℤ} (hd : den % 2 = 0) :
    (1 - den, den + 1) ∈ (reciprocalLadderDeck den).span := by
  rw [reciprocalLadderDeck_eq hd]
  exact ⟨0, 1, by apply Prod.ext <;> simp [PeriodDeck.combine, add_comm 1 den]⟩

private theorem ladderOdd_rankCorrection_add_representative {den : ℤ} {correction : Field}
    (hcorrect : ∀ point ∈ (BaseMask.ladderOdd.raw den).sites, correction point = ladderOddRankCorrection den point)
    (hper : ∀ step ∈ (reciprocalLadderDeck den).span, Function.Periodic correction step)
    {step : Site} (hstep : step ∈ (reciprocalLadderDeck den).span) (point : Site)
    (hmem : point + step ∈ (BaseMask.ladderOdd.raw den).sites) :
    correction point = ladderOddRankCorrection den (point + step) :=
  (hper step hstep point).symm.trans (hcorrect _ hmem)

private theorem ladderOdd_rankCorrection_sub_representative {den : ℤ} {correction : Field}
    (hcorrect : ∀ point ∈ (BaseMask.ladderOdd.raw den).sites, correction point = ladderOddRankCorrection den point)
    (hper : ∀ step ∈ (reciprocalLadderDeck den).span, Function.Periodic correction step)
    {step : Site} (hstep : step ∈ (reciprocalLadderDeck den).span) (point : Site)
    (hmem : point - step ∈ (BaseMask.ladderOdd.raw den).sites) :
    correction point = ladderOddRankCorrection den (point - step) := by
  have h := hper step hstep (point - step)
  rw [sub_add_cancel] at h
  exact h.trans (hcorrect _ hmem)

set_option maxHeartbeats 850000 in
private theorem ladderOdd_rank_even_black {den x y : ℤ} (hden : BaseMask.ladderOdd.Valid den)
    {correction : Field} (hcorrect : ∀ point ∈ (BaseMask.ladderOdd.raw den).sites,
      correction point = ladderOddRankCorrection den point)
    (hpoint : (x, y) ∈ (BaseMask.ladderOdd.raw den).sites)
    (heven : (x + y) % 2 = 0) (hblack : LadderOddEvenBlack den (x, y)) :
    6 * (x - 1) + correction (x - 1, y) < 6 * x + correction (x, y) ∧
      6 * (x + 1) + correction (x + 1, y) < 6 * x + correction (x, y) := by
  have ⟨hmin, hd⟩ := hden
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_ladderOdd_raw_iff.mp hpoint
  simp only [BaseMask.LadderOddCorner] at hshape
  dsimp only at hx hy
  simp only [LadderOddEvenBlack] at hblack
  have hn : (x - 1, y) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_mem
  have hp : (x + 1, y) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_mem
  rw [hcorrect _ hpoint, hcorrect _ hn, hcorrect _ hp]
  clear hshape
  rcases hblack with h1 | h2 | h3
  · constructor <;> ladder_rank
  · by_cases hlast : y = den + 1 <;> constructor <;> ladder_rank
  · by_cases hcol : x = den <;> constructor <;> ladder_rank

set_option maxHeartbeats 1000000 in
private theorem ladderOdd_rank_odd_black {den x y : ℤ} (hden : BaseMask.ladderOdd.Valid den)
    {correction : Field} (hcorrect : ∀ point ∈ (BaseMask.ladderOdd.raw den).sites,
      correction point = ladderOddRankCorrection den point)
    (hpoint : (x, y) ∈ (BaseMask.ladderOdd.raw den).sites)
    (hodd : ¬ EvenSite (x, y)) (hblack : ¬ LadderOddOddWhite den (x, y)) :
    correction (x, y - 1) < correction (x, y) ∧ correction (x, y + 1) < correction (x, y) := by
  have ⟨hmin, hd⟩ := hden
  have hxy : (x + y) % 2 ≠ 0 := hodd
  have hn : (x, y - 1) ∈ (BaseMask.ladderOdd.raw den).sites := not_not.mp fun h =>
    hblack (Or.inl ((ladderOdd_down_notMem_iff hden hpoint hxy).mp h))
  have hp : (x, y + 1) ∈ (BaseMask.ladderOdd.raw den).sites := not_not.mp fun h =>
    hblack (Or.inr (Or.inl ((ladderOdd_up_notMem_iff hden hpoint hodd).mp h)))
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_ladderOdd_raw_iff.mp hpoint
  dsimp only at hx hy
  simp only [BaseMask.LadderOddCorner] at hshape
  simp only [LadderOddOddWhite, LadderOddLowerBoundary, reflectLadderOdd, Prod.fst_sub, Prod.snd_sub] at hblack
  have hrange : 1 ≤ y ∧ y ≤ den + 1 ∧ 1 ≤ x + y ∧ x + y ≤ 2 * den + 3 := by omega
  rw [hcorrect _ hpoint, hcorrect _ hn, hcorrect _ hp]
  clear hshape hcorrect hn hp hpoint
  by_cases hleft : x ≤ 0
  · have hrow : 2 ≤ y := by omega
    clear hblack
    constructor <;> ladder_rank
  · by_cases hsum : x + y ≤ den + 1
    · by_cases hshelf : x + y = den + 1
      · have hend : x = 1 ∧ y = den := by omega
        clear hblack
        constructor <;> ladder_rank
      · clear hblack
        constructor <;> ladder_rank
    · by_cases hmid : x ≤ den
      · have hfar : den + 5 ≤ x + y := by omega
        clear hblack
        constructor <;> ladder_rank
      · have hright : den + 1 ≤ x ∧ x ≤ 2 * den - 1 ∧
            den + 3 ≤ x + y ∧ x + y ≤ 2 * den + 1 ∧ 2 ≤ y ∧ y ≤ den := by omega
        clear hblack
        by_cases hrow : y = 2
        · by_cases hdiag : x = den + 1 <;> constructor <;> ladder_rank
        · by_cases hsumTop : x + y = 2 * den + 1 <;> constructor <;> ladder_rank

set_option maxHeartbeats 1200000 in
private theorem ladderOdd_rank_even_white {den x y : ℤ} (hden : BaseMask.ladderOdd.Valid den)
    {correction : Field} (hcorrect : ∀ point ∈ (BaseMask.ladderOdd.raw den).sites,
      correction point = ladderOddRankCorrection den point)
    (hper : ∀ step ∈ (reciprocalLadderDeck den).span, Function.Periodic correction step)
    (hpoint : (x, y) ∈ (BaseMask.ladderOdd.raw den).sites)
    (heven : (x + y) % 2 = 0) (hwhite : ¬ LadderOddEvenBlack den (x, y)) :
    6 * (x - 1) + correction (x - 1, y) < 6 * x + correction (x, y) ∨
      6 * (x + 1) + correction (x + 1, y) < 6 * x + correction (x, y) := by
  have ⟨hmin, hd⟩ := hden
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_ladderOdd_raw_iff.mp hpoint
  dsimp only at hx hy
  simp only [BaseMask.LadderOddCorner] at hshape
  simp only [LadderOddEvenBlack] at hwhite
  rw [hcorrect _ hpoint]
  by_cases hleft : (x = 0 ∧ y = 0) ∨ (x = 2 - den ∧ y = den)
  · left
    have hn : ((x - 1, y) : Site) + (2 * den, 2) ∈ (BaseMask.ladderOdd.raw den).sites := by
      rcases hleft with h | h <;> ladder_mem
    rw [ladderOdd_rankCorrection_add_representative hcorrect hper (ladderOdd_kernel_mem_span hd) _ hn]
    rcases hleft with h | h <;> ladder_rank
  by_cases hright : (2 ≤ x ∧ 1 ≤ y ∧ x + y ≤ den) ∨
      (den + 2 ≤ x ∧ 2 ≤ y ∧ x + y ≤ 2 * den) ∨
      (x + y = 2 * den + 2 ∧ den + 2 ≤ x ∧ 3 ≤ y)
  · right
    have hp : (x + 1, y) ∈ (BaseMask.ladderOdd.raw den).sites := by
      rcases hright with h | h | h <;> ladder_mem
    rw [hcorrect _ hp]
    rcases hright with h | h | h <;> ladder_rank
  left
  have hn : (x - 1, y) ∈ (BaseMask.ladderOdd.raw den).sites :=
    not_not.mp (fun h => hleft ((ladderOdd_left_notMem_iff hden hpoint heven).mp h))
  rw [hcorrect _ hn]
  by_cases hcorner : (x = 2 * den ∧ y = 2) ∨ (x = den + 2 ∧ y = den + 2)
  · rcases hcorner with h | h <;> ladder_rank
  have hbody : 1 ≤ x + y ∧ x + y ≤ 2 * den + 3 ∧
      ¬ ((y = 0 ∧ den ≤ x) ∨ (y = den + 2 ∧ x ≤ 2)) := by omega
  clear hshape
  by_cases hleftCol : x ≤ 0
  · ladder_rank
  · by_cases hbottom : y = 0
    · ladder_rank
    · by_cases htop : y = den + 2
      · have hxTop : 4 ≤ x ∧ x ≤ den := by omega
        ladder_rank
      · by_cases hshelf : y = 1 ∧ den + 3 ≤ x
        · ladder_rank
        · have hremain : (x = 1 ∧ y = den + 1) ∨ (x = den + 1 ∧ y = 1) ∨
              (x ≤ den ∧ y ≤ den + 1 ∧ den + 4 ≤ x + y) := by omega
          rcases hremain with h | h | h <;> ladder_rank

set_option maxHeartbeats 1200000 in
private theorem ladderOdd_rank_odd_white {den x y : ℤ} (hden : BaseMask.ladderOdd.Valid den)
    {correction : Field} (hcorrect : ∀ point ∈ (BaseMask.ladderOdd.raw den).sites,
      correction point = ladderOddRankCorrection den point)
    (hper : ∀ step ∈ (reciprocalLadderDeck den).span, Function.Periodic correction step)
    (hpoint : (x, y) ∈ (BaseMask.ladderOdd.raw den).sites)
    (hodd : ¬ EvenSite (x, y)) (hwhite : LadderOddOddWhite den (x, y)) :
    correction (x, y - 1) < correction (x, y) ∨ correction (x, y + 1) < correction (x, y) := by
  have ⟨hmin, hd⟩ := hden
  have hxy : (x + y) % 2 ≠ 0 := hodd
  obtain ⟨hx, hy, hshape⟩ := BaseMask.mem_ladderOdd_raw_iff.mp hpoint
  dsimp only at hx hy
  simp only [BaseMask.LadderOddCorner] at hshape
  have hU := ladderOdd_kernel_mem_span hd
  have hV := ladderOdd_transverse_mem_span hd
  rw [hcorrect _ hpoint]
  by_cases hlo : LadderOddLowerBoundary den (x, y)
  · simp only [LadderOddLowerBoundary] at hlo
    rcases hlo with hdiag | hbottom | hshelf
    · right
      have hp : (x, y + 1) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_mem
      rw [hcorrect _ hp]
      clear hshape
      ladder_rank
    · left
      have hn : ((x, y - 1) : Site) + (1 - den, den + 1) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_mem
      rw [ladderOdd_rankCorrection_add_representative hcorrect hper hV _ hn]
      clear hshape
      ladder_rank
    · by_cases hend : x = 2 * den
      · right
        have hp : (x, y + 1) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_mem
        rw [hcorrect _ hp]
        ladder_rank
      · left
        have hn : ((x, y - 1) : Site) + (1 - den, den + 1) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_mem
        rw [ladderOdd_rankCorrection_add_representative hcorrect hper hV _ hn]
        clear hshape
        by_cases hstart : x = den <;> ladder_rank
  by_cases hup : LadderOddLowerBoundary den (reflectLadderOdd den (x, y))
  · simp only [LadderOddLowerBoundary, reflectLadderOdd, Prod.fst_sub, Prod.snd_sub] at hup
    rcases hup with hdiag | htop | hshelf
    · right
      have hp : ((x, y + 1) : Site) - (2 * den, 2) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_mem
      rw [ladderOdd_rankCorrection_sub_representative hcorrect hper hU _ hp]
      clear hshape
      ladder_rank
    · by_cases hend : x = den + 1
      · right
        have hp : ((x, y + 1) : Site) - (1 - den, den + 1) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_mem
        rw [ladderOdd_rankCorrection_sub_representative hcorrect hper hV _ hp]
        ladder_rank
      · left
        have hn : (x, y - 1) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_mem
        rw [hcorrect _ hn]
        clear hshape
        ladder_rank
    · by_cases hend : x = 2
      · right
        have hp : ((x, y + 1) : Site) - (1 - den, den + 1) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_mem
        rw [ladderOdd_rankCorrection_sub_representative hcorrect hper hV _ hp]
        ladder_rank
      · left
        have hn : (x, y - 1) ∈ (BaseMask.ladderOdd.raw den).sites := by ladder_mem
        rw [hcorrect _ hn]
        clear hshape
        ladder_rank
  have hn : (x, y - 1) ∈ (BaseMask.ladderOdd.raw den).sites :=
    not_not.mp fun h => hlo ((ladderOdd_down_notMem_iff hden hpoint hxy).mp h)
  have hp : (x, y + 1) ∈ (BaseMask.ladderOdd.raw den).sites :=
    not_not.mp fun h => hup ((ladderOdd_up_notMem_iff hden hpoint hodd).mp h)
  simp only [LadderOddOddWhite, hlo, hup, false_or] at hwhite
  simp only [LadderOddLowerBoundary, reflectLadderOdd, Prod.fst_sub, Prod.snd_sub] at hlo hup
  rcases hwhite with hdiag | hdiag | hcorner | hcorner
  · left
    have hrange : 2 ≤ y ∧ 2 ≤ x ∧ x ≤ den - 1 := by omega
    rw [hcorrect _ hn]
    clear hshape
    ladder_rank
  · right
    have hrange : 3 ≤ x ∧ x ≤ den ∧ y ≤ den := by omega
    rw [hcorrect _ hp]
    clear hshape
    ladder_rank
  · right
    rw [hcorrect _ hp]
    ladder_rank
  · right
    rw [hcorrect _ hp]
    ladder_rank

private theorem ladderOdd_rank_on_raw {den : ℤ} (hden : BaseMask.ladderOdd.Valid den)
    {field correction : Field} (hagree : (BaseMask.ladderOdd.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den))
    (hcorrect : ∀ point ∈ (BaseMask.ladderOdd.raw den).sites, correction point = ladderOddRankCorrection den point)
    (hper : ∀ step ∈ (reciprocalLadderDeck den).span, Function.Periodic correction step)
    (point : Site) (hpoint : point ∈ (BaseMask.ladderOdd.raw den).sites) :
    let rank : Field := fun site => 6 * site.1 + correction site
    let value := laplacian field point
    (value = -1 ∧ rank (incomingNeg point) < rank point ∧ rank (incomingPos point) < rank point) ∨
      (value = 0 ∧ (rank (incomingNeg point) < rank point ∨ rank (incomingPos point) < rank point)) := by
  obtain ⟨x, y⟩ := point
  by_cases heven : EvenSite (x, y)
  · have hlap := ladderOdd_laplacian_on_even_raw hden hagree hperiod hpoint heven
    simp only [incomingNeg, incomingPos, if_pos heven]
    by_cases hblack : LadderOddEvenBlack den (x, y)
    · exact Or.inl ⟨by simpa only [if_pos hblack] using hlap,
        ladderOdd_rank_even_black hden hcorrect hpoint heven hblack⟩
    · exact Or.inr ⟨by simpa only [if_neg hblack] using hlap,
        ladderOdd_rank_even_white hden hcorrect hper hpoint heven hblack⟩
  · have hlap := ladderOdd_laplacian_on_odd_raw hden hagree hperiod hpoint heven
    simp only [incomingNeg, incomingPos, if_neg heven]
    by_cases hwhite : LadderOddOddWhite den (x, y)
    · have hrank := ladderOdd_rank_odd_white hden hcorrect hper hpoint heven hwhite
      exact Or.inr ⟨by simpa only [if_pos hwhite] using hlap, by
        simpa only [add_lt_add_iff_left] using hrank⟩
    · have hrank := ladderOdd_rank_odd_black hden hcorrect hpoint heven hwhite
      exact Or.inl ⟨by simpa only [if_neg hwhite] using hlap, by
        simpa only [add_lt_add_iff_left] using hrank⟩

/-- The literal B5 rank decreases on its required physical inputs throughout the plane. -/
theorem ladderOdd_exists_burningRank {den : ℤ} (hden : BaseMask.ladderOdd.Valid den) {field : Field}
    (hagree : (BaseMask.ladderOdd.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den)) :
    ∃ correction : Field,
      (∀ point ∈ (BaseMask.ladderOdd.raw den).sites, correction point = ladderOddRankCorrection den point) ∧
      (∀ step ∈ (reciprocalLadderDeck den).span, Function.Periodic correction step) ∧
      IsBurningRank field (fun point => 6 * point.1 + correction point) := by
  obtain ⟨correction, hcorrect, hper⟩ := ladderOdd_exists_periodic_rankCorrection hden
  let fraction := Fraction.mk 1 den
  have hinterval : fraction.InUnitInterval := by
    have := hden.1
    exact ⟨by dsimp [fraction]; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp [fraction]; omega⟩
  refine ⟨correction, hcorrect, hper, fun point => ?_⟩
  obtain ⟨site, hsite, hspan⟩ := ladderOdd_raw_cover hden point
  let step := point - site
  have hpoint : site + step = point := by dsimp [step]; rw [add_comm, sub_add_cancel]
  have heven : EvenSite step := ((fraction.mem_modifiedDeck_iff step).mp hspan).2
  rw [← hpoint, laplacian_periodic_of_generatorPeriods hinterval hperiod hspan site,
    incomingNeg_add_of_even site step heven, incomingPos_add_of_even site step heven]
  simp only [hper step hspan site, hper step hspan (incomingNeg site),
    hper step hspan (incomingPos site), Prod.fst_add]
  rcases ladderOdd_rank_on_raw hden hagree hperiod hcorrect hper site hsite with
    ⟨h, hn, hp⟩ | ⟨h, hn | hp⟩
  · exact Or.inl ⟨h, by dsimp at hn; omega, by dsimp at hp; omega⟩
  · exact Or.inr ⟨h, Or.inl (by dsimp at hn; omega)⟩
  · exact Or.inr ⟨h, Or.inr (by dsimp at hp; omega)⟩

theorem ladderOdd_exists_recurrent_extension {den : ℤ} (hden : BaseMask.ladderOdd.Valid den) :
    ∃ field : Field, (BaseMask.ladderOdd.raw den).Agrees field 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den) ∧
      HasQuadraticGrowth field (Fraction.mk 1 den).matrix ∧ Superharmonic field ∧ Recurrent field := by
  obtain ⟨field, hagree, hperiod, hgrowth⟩ := ladderOdd_exists_extension hden
  obtain ⟨_, _, _, hrank⟩ := ladderOdd_exists_burningRank hden hagree hperiod
  exact ⟨field, hagree, hperiod, hgrowth, hrank.superharmonic, hrank.recurrent⟩

theorem ladderEven_exists_recurrent_extension {den : ℤ} (hden : BaseMask.ladderEven.Valid den) :
    ∃ field : Field,
      ((BaseMask.ladderEven.tile den hden).llCenter (BaseMask.ladderEven.tile_nonempty den hden)).Agrees field 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 den).rotate field 0 (ladderEvenConstantV den) ∧
      HasQuadraticGrowth field (Fraction.mk 1 den).rotate.matrix ∧ Superharmonic field ∧ Recurrent field := by
  obtain ⟨field, hagree, hperiod, _, hsuper, hrec⟩ := ladderOdd_exists_recurrent_extension hden
  have hrot := rotateLadderField_periods hden.2 hperiod
  exact ⟨rotateLadderField den field, BaseMask.ladderEven_agrees_rotateLadderField hden hagree,
    hrot, generator_periods_growth (ladder_rotate_inUnitInterval hden.1 hden.2) hrot,
    rotateLadderField_recurrent hrec hsuper⟩

theorem evaluateNative_threes_odd_standard_recurrent (extra : ℕ) :
    let word := (BaseRun.threes extra).word
    let den : ℤ := 2 * (extra : ℤ) + 3 + 1
    let fraction := (parentsAt word).current .odd
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative word = .ok registers ∧ registers.standard.currentOdd.val.Agrees field 0 ∧
      HasGeneratorPeriods fraction field 0 (stairEvenConstantV den) ∧
      HasQuadraticGrowth field fraction.matrix ∧ Superharmonic field ∧ Recurrent field := by
  dsimp only
  rw [threes_current_odd]
  have hvalid : BaseMask.ladderOdd.Valid (2 * (extra : ℤ) + 3 + 1) := by
    change 4 ≤ 2 * (extra : ℤ) + 3 + 1 ∧ (2 * (extra : ℤ) + 3 + 1) % 2 = 0
    omega
  obtain ⟨field, hagree, hperiod, hgrowth, hsuper, hrec⟩ := ladderOdd_exists_recurrent_extension hvalid
  exact ⟨(BaseRun.threes extra).registers.llCenter, field, evaluateNative_base _,
    BaseMask.ladderOdd_llCenter_agrees hvalid hagree, hperiod, hgrowth, hsuper, hrec⟩

theorem evaluateNative_twos_even_standard_recurrent (extra : ℕ) :
    let word := (BaseRun.twos extra).word
    let den : ℤ := 2 * (extra : ℤ) + 3 + 1
    let fraction := (parentsAt word).current .even
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative word = .ok registers ∧ registers.standard.currentEven.val.Agrees field 0 ∧
      HasGeneratorPeriods fraction field 0 (ladderEvenConstantV den) ∧
      HasQuadraticGrowth field fraction.matrix ∧ Superharmonic field ∧ Recurrent field := by
  dsimp only
  rw [twos_current_even]
  have hvalid : BaseMask.ladderEven.Valid (2 * (extra : ℤ) + 3 + 1) := by
    change 4 ≤ 2 * (extra : ℤ) + 3 + 1 ∧ (2 * (extra : ℤ) + 3 + 1) % 2 = 0
    omega
  obtain ⟨field, hagree, hperiod, hgrowth, hsuper, hrec⟩ := ladderEven_exists_recurrent_extension hvalid
  exact ⟨(BaseRun.twos extra).registers.llCenter, field, evaluateNative_base _, hagree, hperiod, hgrowth, hsuper, hrec⟩

end FLatticePaper.Construction
