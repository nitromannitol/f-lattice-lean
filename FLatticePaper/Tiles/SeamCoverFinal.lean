import FLatticePaper.Tiles.SeamCover
import FLatticePaper.Tiles.SeamSub
import FLatticePaper.Tiles.SeamFieldsLowSymm
import FLatticePaper.Tiles.SeamFinal
import FLatticePaper.Tiles.RegisterLink
import FLatticePaper.Tiles.SubOddCopy
import FLatticePaper.Tiles.SubEvenCopy
import FLatticePaper.Tiles.SiteHullOdd
import FLatticePaper.Tiles.SiteHullEven
import FLatticePaper.Tiles.WordCounts
import FLatticePaper.Tiles.StandardHalfTurn

/-! Task Q25 (completeness of the seam): the fields `CoverNodupOdd` and `CoverNodupEven` for every word, from `cover_of_walk`.

The bottom walk of the odd child is `gH` of its `childP` (ceiling of slope `2n/(d+n)`), and its right walk is `mulI` of `gH` of the `childQ` of
the swapped word (ceiling of slope `(d−n)/d`). The even child is treated the same way with `childQ` (slope `n/((d+n)/2)`) and the `childP`
of the swapped word (slope `(d−n)/d`). The letter counts come from `count_gH_ceil`; the sub and symmetry fields are `subOdd_all`, `subEven_all`
and `symm_odd_field`, `symm_even_field`. -/

namespace FLatticePaper.Tiles.SeamCoverFinal

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
  FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SeamFinal FLatticePaper.Tiles.CeilWords
  FLatticePaper.Tiles.SubWalkOddBlocks FLatticePaper.Tiles.WordCounts FLatticePaper.Tiles.SeamCover
  FLatticePaper.Tiles.SiteHullOdd FLatticePaper.Tiles.SiteHullEven FLatticePaper.Tiles.SubOddCopy
  FLatticePaper.Tiles.SubEvenCopy FLatticePaper.Tiles.StandardHalfTurn FLatticePaper.Tiles.SeamSub
  FLatticePaper.Tiles.SeamFieldsLowSymm

/-- The letters of `gH x` of a word of length at least two are `one` and `i`. -/
theorem gH_letters (x : BinaryWord) (hx : 2 ≤ x.length) : ∀ z ∈ gH x, z = Unit4.one ∨ z = Unit4.i := by
  intro z hz
  rw [gH_walk x (by omega)] at hz
  rcases List.mem_append.1 hz with h | h
  · obtain ⟨j, hj, hzj⟩ := List.mem_flatMap.1 h
    rw [List.mem_range] at hj
    rw [blockWord_eq x j (by omega)] at hzj
    split_ifs at hzj <;> simp at hzj <;> rcases hzj with rfl | rfl <;> simp
  · simp at h
    exact Or.inl h

theorem mulI_inj : Function.Injective Unit4.mulI := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (exfalso; simp [Unit4.mulI] at h)

theorem count_map_mulI_negOne (l : F2Word) :
    List.count Unit4.negOne (l.map Unit4.mulI) = List.count Unit4.i l := by
  have := List.count_map_of_injective l Unit4.mulI mulI_inj Unit4.i
  simpa [Unit4.mulI] using this

theorem count_map_mulI_i (l : F2Word) :
    List.count Unit4.i (l.map Unit4.mulI) = List.count Unit4.one l := by
  have := List.count_map_of_injective l Unit4.mulI mulI_inj Unit4.one
  simpa [Unit4.mulI] using this

theorem mulI_letters (l : F2Word) (hl : ∀ z ∈ l, z = Unit4.one ∨ z = Unit4.i) :
    ∀ z ∈ l.map Unit4.mulI, z = Unit4.i ∨ z = Unit4.negOne := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
  rcases hl y hy with rfl | rfl <;> simp [Unit4.mulI]

/-- **The odd seam: the boundary cover and nodup of the odd child, for every word.** -/
theorem coverNodupOdd_all (v : Word) : CoverNodupOdd v := by
  have hpos : 0 < (curO v).num := (curO_pos_lt v).1
  have hlt : (curO v).num < (curO v).den := (curO_pos_lt v).2
  have hodd : ((curO v).num + (curO v).den) % 2 = 1 := curO_odd v
  have hP : ∀ z : GInt, z ∈ oddTile v ↔ InH (curO v) z := mem_oddTile_iff v
  have hmu : SiteInduction.muOf (curO v) = 2 := by
    unfold SiteInduction.muOf
    rw [if_pos hodd]
  have hb1 : oddBottom v = gH (quadAt [] v).childP := RegisterLink.oddBottom_eq_gH v
  have hb2 : oddRight v = (gH (quadAt [] (swapW v)).childQ).map Unit4.mulI := by
    unfold oddRight
    rw [RegisterLink.evenBottom_eq_gH]
    rfl
  have hcp : CeilWords.CeilWord (quadAt [] v).childP (2 * (curO v).num) ((curO v).den + (curO v).num) :=
    (CeilWords.quadInv_all v).1
  have hlen1 : 2 ≤ (quadAt [] v).childP.length := by
    have := hcp.1
    omega
  obtain ⟨hI1, hO1⟩ := count_gH_ceil (quadAt [] v).childP (2 * (curO v).num) ((curO v).den + (curO v).num) hcp
    (by omega) (by omega)
  have hcq' : CeilWords.CeilWord (quadAt [] (swapW v)).childQ ((curO v).den - (curO v).num) (curO v).den := by
    have h := (CeilWords.quadInv_all (swapW v)).2.1
    have e : (parentsAt (swapW v)).current .even =
        ⟨(curO v).den - (curO v).num, (curO v).den + (curO v).num⟩ := by
      rw [curE_swapW]
      unfold Fraction.rotate
      rw [if_pos hodd]
    rw [e] at h
    have e2 : sEven ⟨(curO v).den - (curO v).num, (curO v).den + (curO v).num⟩ =
        ((curO v).den - (curO v).num, (curO v).den) := by
      unfold sEven
      ext
      · simp
      · simp
        omega
    rw [e2] at h
    exact h
  have hlen2 : 2 ≤ (quadAt [] (swapW v)).childQ.length := by
    have := hcq'.1
    omega
  obtain ⟨hI2, hO2⟩ := count_gH_ceil (quadAt [] (swapW v)).childQ ((curO v).den - (curO v).num) (curO v).den hcq'
    (by omega) (by omega)
  have hw1 : ∀ z ∈ oddBottom v, z = Unit4.one ∨ z = Unit4.i := by
    rw [hb1]
    exact gH_letters _ hlen1
  have hw2 : ∀ z ∈ oddRight v, z = Unit4.i ∨ z = Unit4.negOne := by
    rw [hb2]
    exact mulI_letters _ (gH_letters _ hlen2)
  have h1 : (List.count Unit4.one (oddBottom v) : ℤ) = SiteInduction.muOf (curO v) * (curO v).den := by
    rw [hb1, hmu, hO1]
    ring
  have h2 : (List.count Unit4.negOne (oddRight v) : ℤ) = (curO v).den - (curO v).num - 1 := by
    rw [hb2, count_map_mulI_negOne]
    exact hI2
  have h3 : (List.count Unit4.i (oddBottom v) : ℤ) + List.count Unit4.i (oddRight v) =
      SiteInduction.muOf (curO v) * (curO v).num - 1 + ((curO v).den + (curO v).num) := by
    rw [hb1, hb2, count_map_mulI_i, hmu, hI1, hO2]
    ring
  have hcov := cover_of_walk (curO v) hpos hlt (oddTile v) hP (oddBottom v) (oddRight v) hw1 hw2
    (SeamSub.subOdd_all v) (SeamFieldsLowSymm.symm_odd_field v) h1 h2 h3
  exact ⟨hcov.1, hcov.2⟩

/-- **The even seam: the boundary cover and nodup of the even child, for every word.** -/
theorem coverNodupEven_all (v : Word) : CoverNodupEven v := by
  have hpos : 0 < (curE v).num := (curE_pos_lt v).1
  have hlt : (curE v).num < (curE v).den := (curE_pos_lt v).2
  have hev : ((curE v).num + (curE v).den) % 2 = 0 := (parentsAt_valid v).current_even_parity
  have hP : ∀ z : GInt, z ∈ evenTile v ↔ InH (curE v) z := mem_evenTile_iff v
  have hmu : SiteInduction.muOf (curE v) = 1 := by
    unfold SiteInduction.muOf
    rw [if_neg (by omega)]
  have hb1 : evenBottom v = gH (quadAt [] v).childQ := RegisterLink.evenBottom_eq_gH v
  have hb2 : evenRight v = (gH (quadAt [] (swapW v)).childP).map Unit4.mulI := by
    unfold evenRight
    rw [RegisterLink.oddBottom_eq_gH]
    rfl
  have hcq : CeilWords.CeilWord (quadAt [] v).childQ (curE v).num (((curE v).den + (curE v).num) / 2) :=
    (CeilWords.quadInv_all v).2.1
  have hlen1 : 2 ≤ (quadAt [] v).childQ.length := by
    have := hcq.1
    omega
  obtain ⟨hI1, hO1⟩ := count_gH_ceil (quadAt [] v).childQ (curE v).num (((curE v).den + (curE v).num) / 2) hcq
    (by omega) (by omega)
  have hrot : curE v = (curO (swapW v)).rotate := by
    have := curE_swapW (swapW v)
    rw [swapW_swapW] at this
    exact this
  have hgodd : ((curO (swapW v)).num + (curO (swapW v)).den) % 2 = 1 := curO_odd (swapW v)
  have hr : curE v = ⟨(curO (swapW v)).den - (curO (swapW v)).num, (curO (swapW v)).den + (curO (swapW v)).num⟩ := by
    rw [hrot]
    unfold Fraction.rotate
    rw [if_pos hgodd]
  have hcp : CeilWords.CeilWord (quadAt [] (swapW v)).childP ((curE v).den - (curE v).num) (curE v).den := by
    have h := (CeilWords.quadInv_all (swapW v)).1
    have e : sOdd (curO (swapW v)) = ((curE v).den - (curE v).num, (curE v).den) := by
      have hn : (curE v).num = (curO (swapW v)).den - (curO (swapW v)).num := by rw [hr]
      have hd : (curE v).den = (curO (swapW v)).den + (curO (swapW v)).num := by rw [hr]
      unfold sOdd
      ext <;> simp <;> omega
    rw [e] at h
    exact h
  have hlen2 : 2 ≤ (quadAt [] (swapW v)).childP.length := by
    have := hcp.1
    omega
  obtain ⟨hI2, hO2⟩ := count_gH_ceil (quadAt [] (swapW v)).childP ((curE v).den - (curE v).num) (curE v).den hcp
    (by omega) (by omega)
  have hw1 : ∀ z ∈ evenBottom v, z = Unit4.one ∨ z = Unit4.i := by
    rw [hb1]
    exact gH_letters _ hlen1
  have hw2 : ∀ z ∈ evenRight v, z = Unit4.i ∨ z = Unit4.negOne := by
    rw [hb2]
    exact mulI_letters _ (gH_letters _ hlen2)
  have h1 : (List.count Unit4.one (evenBottom v) : ℤ) = SiteInduction.muOf (curE v) * (curE v).den := by
    rw [hb1, hmu, hO1]
    omega
  have h2 : (List.count Unit4.negOne (evenRight v) : ℤ) = (curE v).den - (curE v).num - 1 := by
    rw [hb2, count_map_mulI_negOne]
    exact hI2
  have h3 : (List.count Unit4.i (evenBottom v) : ℤ) + List.count Unit4.i (evenRight v) =
      SiteInduction.muOf (curE v) * (curE v).num - 1 + ((curE v).den + (curE v).num) := by
    rw [hb1, hb2, count_map_mulI_i, hmu, hI1, hO2]
    omega
  have hcov := cover_of_walk (curE v) hpos hlt (evenTile v) hP (evenBottom v) (evenRight v) hw1 hw2
    (SeamSub.subEven_all v) (SeamFieldsLowSymm.symm_even_field v) h1 h2 h3
  exact ⟨hcov.1, hcov.2⟩

end FLatticePaper.Tiles.SeamCoverFinal
