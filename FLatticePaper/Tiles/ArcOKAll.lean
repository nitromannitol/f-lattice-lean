import FLatticePaper.Tiles.RegisterInduction
import FLatticePaper.Tiles.SeamCoverFinal
import FLatticePaper.Tiles.WalkLines

/-! Task Q25, the arc data `ArcOK` of the odd and even four-arc loops, for every word.

`ArcOK (oddBottom s) (oddRight s)` and `ArcOK (evenBottom s) (evenRight s)` hold for every word `s`. The first walk is `gH` of a ceiling word:
its letters are `one` and `i`, and it starts and ends with `one`. The second walk is the `mulI` image of such a walk: its letters are `i` and
`negOne`, and it starts and ends with `i`. The inequalities come from the letter counts of `SeamCoverFinal` (`count_gH_ceil`). -/

namespace FLatticePaper.Tiles.ArcOKAll

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
  FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SeamFinal FLatticePaper.Tiles.CeilWords
  FLatticePaper.Tiles.SubWalkOddBlocks FLatticePaper.Tiles.SubCeilOdd FLatticePaper.Tiles.WordCounts
  FLatticePaper.Tiles.SeamCover FLatticePaper.Tiles.SiteHullOdd FLatticePaper.Tiles.SiteHullEven
  FLatticePaper.Tiles.SubOddCopy FLatticePaper.Tiles.SubEvenCopy FLatticePaper.Tiles.StandardHalfTurn
  FLatticePaper.Tiles.SeamSub FLatticePaper.Tiles.SeamFieldsLowSymm FLatticePaper.Tiles.SeamCoverFinal
  FLatticePaper.Tiles.RegisterInduction

/-- The first block of `gH x` is `one` (block 0 is never of the NE kind, as `tY ε 0 = 0`). -/
theorem gH_head_one (x : BinaryWord) (hx : 2 ≤ x.length) : (gH x).head? = some Unit4.one := by
  obtain ⟨m, hm⟩ : ∃ m, x.length - 1 = m + 1 := ⟨x.length - 2, by omega⟩
  have hb0 : (blockWord x 0).head? = some Unit4.one := by
    rw [blockWord_eq x 0 (by omega)]
    split_ifs with h1 h2
    · simp
    · exfalso
      have h := h2.2
      rw [tY_zero] at h
      norm_num at h
    · simp
  rw [gH_walk x (by omega), hm, List.range_succ_eq_map, List.flatMap_cons]
  simp [List.head?_append, hb0]

/-- The walk `gH x` ends with `one`. -/
theorem gH_last_one (x : BinaryWord) (hx : 1 ≤ x.length) : (gH x).getLast? = some Unit4.one := by
  rw [gH_walk x hx]
  simp

/-- The arc data from the letters, the first and last letters and the two count inequalities. -/
theorem arcOK_of (w1 w2 : F2Word) (hw1 : ∀ z ∈ w1, z = Unit4.one ∨ z = Unit4.i)
    (hw2 : ∀ z ∈ w2, z = Unit4.i ∨ z = Unit4.negOne)
    (hh1 : w1.head? = some Unit4.one) (hh2 : w2.head? = some Unit4.i)
    (hl2 : w2.getLast? = some Unit4.i)
    (hs : (List.count Unit4.i w1 : ℤ) < (List.count Unit4.i w2 : ℤ))
    (hx : 0 < (List.count Unit4.one w1 : ℤ) - (List.count Unit4.negOne w2 : ℤ)) :
    ArcOK w1 w2 := by
  have hn1 : ∀ z ∈ w1, z ≠ Unit4.negI := by
    intro z hz h
    subst h
    rcases hw1 _ hz with h' | h' <;> cases h'
  have hn2 : ∀ z ∈ w2, z ≠ Unit4.negI := by
    intro z hz h
    subst h
    rcases hw2 _ hz with h' | h' <;> cases h'
  have hc1 : List.count Unit4.negOne w1 = 0 := by
    rw [List.count_eq_zero]
    intro h
    rcases hw1 _ h with h' | h' <;> cases h'
  have hc2 : List.count Unit4.one w2 = 0 := by
    rw [List.count_eq_zero]
    intro h
    rcases hw2 _ h with h' | h' <;> cases h'
  unfold ArcOK
  refine ⟨hw1, hw2, ?_, ?_, ?_, ?_, hl2⟩
  · rw [FLatticePaper.Tiles.WalkLines.sum_snd w1 hn1, FLatticePaper.Tiles.WalkLines.sum_snd w2 hn2]
    exact hs
  · rw [FLatticePaper.Tiles.WalkLines.sum_fst w1 hn1, FLatticePaper.Tiles.WalkLines.sum_fst w2 hn2, hc1, hc2]
    push_cast
    linarith
  · rintro ⟨_, h⟩
    rw [hh2] at h
    cases h
  · rintro ⟨h, _⟩
    rw [hh1] at h
    cases h

/-- **The odd arc data, for every word.** -/
theorem arcOK_odd_all (s : Word) : ArcOK (oddBottom s) (oddRight s) := by
  have hpos : 0 < (curO s).num := (curO_pos_lt s).1
  have hlt : (curO s).num < (curO s).den := (curO_pos_lt s).2
  have hodd : ((curO s).num + (curO s).den) % 2 = 1 := curO_odd s
  have hmu : SiteInduction.muOf (curO s) = 2 := by
    unfold SiteInduction.muOf
    rw [if_pos hodd]
  have hb1 : oddBottom s = gH (quadAt [] s).childP := RegisterLink.oddBottom_eq_gH s
  have hb2 : oddRight s = (gH (quadAt [] (swapW s)).childQ).map Unit4.mulI := by
    unfold oddRight
    rw [RegisterLink.evenBottom_eq_gH]
    rfl
  have hcp : CeilWords.CeilWord (quadAt [] s).childP (2 * (curO s).num) ((curO s).den + (curO s).num) :=
    (CeilWords.quadInv_all s).1
  have hlen1 : 2 ≤ (quadAt [] s).childP.length := by
    have := hcp.1
    omega
  obtain ⟨hI1, hO1⟩ := count_gH_ceil (quadAt [] s).childP (2 * (curO s).num) ((curO s).den + (curO s).num) hcp
    (by omega) (by omega)
  have hcq' : CeilWords.CeilWord (quadAt [] (swapW s)).childQ ((curO s).den - (curO s).num) (curO s).den := by
    have h := (CeilWords.quadInv_all (swapW s)).2.1
    have e : (parentsAt (swapW s)).current .even =
        ⟨(curO s).den - (curO s).num, (curO s).den + (curO s).num⟩ := by
      rw [curE_swapW]
      unfold Fraction.rotate
      rw [if_pos hodd]
    rw [e] at h
    have e2 : sEven ⟨(curO s).den - (curO s).num, (curO s).den + (curO s).num⟩ =
        ((curO s).den - (curO s).num, (curO s).den) := by
      unfold sEven
      ext
      · simp
      · simp
        omega
    rw [e2] at h
    exact h
  have hlen2 : 2 ≤ (quadAt [] (swapW s)).childQ.length := by
    have := hcq'.1
    omega
  obtain ⟨hI2, hO2⟩ := count_gH_ceil (quadAt [] (swapW s)).childQ ((curO s).den - (curO s).num) (curO s).den hcq'
    (by omega) (by omega)
  have hw1 : ∀ z ∈ oddBottom s, z = Unit4.one ∨ z = Unit4.i := by
    rw [hb1]
    exact FLatticePaper.Tiles.SeamCoverFinal.gH_letters _ hlen1
  have hw2 : ∀ z ∈ oddRight s, z = Unit4.i ∨ z = Unit4.negOne := by
    rw [hb2]
    exact FLatticePaper.Tiles.SeamCoverFinal.mulI_letters _
      (FLatticePaper.Tiles.SeamCoverFinal.gH_letters _ hlen2)
  have hh1 : (oddBottom s).head? = some Unit4.one := by
    rw [hb1]
    exact gH_head_one _ hlen1
  have hh2 : (oddRight s).head? = some Unit4.i := by
    simp [hb2, List.head?_map, gH_head_one _ hlen2, Unit4.mulI]
  have hl2 : (oddRight s).getLast? = some Unit4.i := by
    simp [hb2, List.getLast?_map, gH_last_one (quadAt [] (swapW s)).childQ (by omega), Unit4.mulI]
  have hA : (List.count Unit4.one (oddBottom s) : ℤ) = SiteInduction.muOf (curO s) * (curO s).den := by
    rw [hb1, hmu, hO1]
    ring
  have h2 : (List.count Unit4.negOne (oddRight s) : ℤ) = (curO s).den - (curO s).num - 1 := by
    rw [hb2, FLatticePaper.Tiles.SeamCoverFinal.count_map_mulI_negOne]
    exact hI2
  have hs : (List.count Unit4.i (oddBottom s) : ℤ) < (List.count Unit4.i (oddRight s) : ℤ) := by
    rw [hb1, hb2, FLatticePaper.Tiles.SeamCoverFinal.count_map_mulI_i, hI1, hO2]
    omega
  have hx : 0 < (List.count Unit4.one (oddBottom s) : ℤ) - (List.count Unit4.negOne (oddRight s) : ℤ) := by
    rw [hA, h2, hmu]
    omega
  exact arcOK_of (oddBottom s) (oddRight s) hw1 hw2 hh1 hh2 hl2 hs hx

/-- **The even arc data, for every word.** -/
theorem arcOK_even_all (s : Word) : ArcOK (evenBottom s) (evenRight s) := by
  have hpos : 0 < (curE s).num := (curE_pos_lt s).1
  have hlt : (curE s).num < (curE s).den := (curE_pos_lt s).2
  have hev : ((curE s).num + (curE s).den) % 2 = 0 := (parentsAt_valid s).current_even_parity
  have hmu : SiteInduction.muOf (curE s) = 1 := by
    unfold SiteInduction.muOf
    rw [if_neg (by omega)]
  have hb1 : evenBottom s = gH (quadAt [] s).childQ := RegisterLink.evenBottom_eq_gH s
  have hb2 : evenRight s = (gH (quadAt [] (swapW s)).childP).map Unit4.mulI := by
    unfold evenRight
    rw [RegisterLink.oddBottom_eq_gH]
    rfl
  have hcq : CeilWords.CeilWord (quadAt [] s).childQ (curE s).num (((curE s).den + (curE s).num) / 2) :=
    (CeilWords.quadInv_all s).2.1
  have hlen1 : 2 ≤ (quadAt [] s).childQ.length := by
    have := hcq.1
    omega
  obtain ⟨hI1, hO1⟩ := count_gH_ceil (quadAt [] s).childQ (curE s).num (((curE s).den + (curE s).num) / 2) hcq
    (by omega) (by omega)
  have hrot : curE s = (curO (swapW s)).rotate := by
    have := curE_swapW (swapW s)
    rw [swapW_swapW] at this
    exact this
  have hgodd : ((curO (swapW s)).num + (curO (swapW s)).den) % 2 = 1 := curO_odd (swapW s)
  have hr : curE s = ⟨(curO (swapW s)).den - (curO (swapW s)).num, (curO (swapW s)).den + (curO (swapW s)).num⟩ := by
    rw [hrot]
    unfold Fraction.rotate
    rw [if_pos hgodd]
  have hcp : CeilWords.CeilWord (quadAt [] (swapW s)).childP ((curE s).den - (curE s).num) (curE s).den := by
    have h := (CeilWords.quadInv_all (swapW s)).1
    have e : sOdd (curO (swapW s)) = ((curE s).den - (curE s).num, (curE s).den) := by
      have hn : (curE s).num = (curO (swapW s)).den - (curO (swapW s)).num := by rw [hr]
      have hd : (curE s).den = (curO (swapW s)).den + (curO (swapW s)).num := by rw [hr]
      unfold sOdd
      ext <;> simp <;> omega
    rw [e] at h
    exact h
  have hlen2 : 2 ≤ (quadAt [] (swapW s)).childP.length := by
    have := hcp.1
    omega
  obtain ⟨hI2, hO2⟩ := count_gH_ceil (quadAt [] (swapW s)).childP ((curE s).den - (curE s).num) (curE s).den hcp
    (by omega) (by omega)
  have hw1 : ∀ z ∈ evenBottom s, z = Unit4.one ∨ z = Unit4.i := by
    rw [hb1]
    exact FLatticePaper.Tiles.SeamCoverFinal.gH_letters _ hlen1
  have hw2 : ∀ z ∈ evenRight s, z = Unit4.i ∨ z = Unit4.negOne := by
    rw [hb2]
    exact FLatticePaper.Tiles.SeamCoverFinal.mulI_letters _
      (FLatticePaper.Tiles.SeamCoverFinal.gH_letters _ hlen2)
  have hh1 : (evenBottom s).head? = some Unit4.one := by
    rw [hb1]
    exact gH_head_one _ hlen1
  have hh2 : (evenRight s).head? = some Unit4.i := by
    simp [hb2, List.head?_map, gH_head_one _ hlen2, Unit4.mulI]
  have hl2 : (evenRight s).getLast? = some Unit4.i := by
    simp [hb2, List.getLast?_map, gH_last_one (quadAt [] (swapW s)).childP (by omega), Unit4.mulI]
  have hA : (List.count Unit4.one (evenBottom s) : ℤ) = SiteInduction.muOf (curE s) * (curE s).den := by
    rw [hb1, hmu, hO1]
    omega
  have h2 : (List.count Unit4.negOne (evenRight s) : ℤ) = (curE s).den - (curE s).num - 1 := by
    rw [hb2, FLatticePaper.Tiles.SeamCoverFinal.count_map_mulI_negOne]
    exact hI2
  have hs : (List.count Unit4.i (evenBottom s) : ℤ) < (List.count Unit4.i (evenRight s) : ℤ) := by
    rw [hb1, hb2, FLatticePaper.Tiles.SeamCoverFinal.count_map_mulI_i, hI1, hO2]
    omega
  have hx : 0 < (List.count Unit4.one (evenBottom s) : ℤ) - (List.count Unit4.negOne (evenRight s) : ℤ) := by
    rw [hA, h2, hmu]
    omega
  exact arcOK_of (evenBottom s) (evenRight s) hw1 hw2 hh1 hh2 hl2 hs hx

end FLatticePaper.Tiles.ArcOKAll
