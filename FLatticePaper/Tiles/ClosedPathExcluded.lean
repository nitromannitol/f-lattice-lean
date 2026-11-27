import FLatticePaper.Tiles.ClosedPathStandard
import FLatticePaper.Tiles.SubOddCopy
import FLatticePaper.Tiles.SubEvenCopy
import FLatticePaper.Tiles.SeamCover
import FLatticePaper.Tiles.CellRegisters

/-! # Condition (C): the mixed pairs of copies that never meet, in the odd-first orientation

Every site of a standard tile with vectors `X = v_{n/d,1}`, `Y = v_{n/d,2}` and lower-left vertex `0` has real coordinate between
that of `Y + 1` and that of `X`, and imaginary coordinate between `0` and that of `X + Y - i` (the text's bound in the proof of
`lemma:weak_alternate_odometer_properties`). Here this is `site_box_odd` and `site_box_even`, from the box of the cell tile
(`SeamCover.box_of_mem`) and the fact that every site is a corner of a cell (`CellRegisters.tileH1_of_hcc`).

The excluded pairs are those of Step 3 of `lemma:standard_tile_properties` (surgical edition at 7a40613): for the even child
`T(q_0)`, `T(q_1)^+ ∩ T(p_1)^{-,2} = T(q_1)^- ∩ T(p_1)^{+,1} = ∅` in both orientations (here the copies `4, 3` and `5, 0` of
`ExclEven`); for the odd child `T(p_0)`, by rotation, `(T(p_1)^+, T(q_1)^{+,1})`, `(T(p_1)^-, T(q_1)^{-,2})` for `W_1` even and
`(T(p_1)^+, T(q_1)^{+,2})`, `(T(p_1)^-, T(q_1)^{-,1})` for `W_1` odd (the copies `0, 2`, `1, 5` and `0, 3`, `1, 4` of `ExclOdd`).
The text proves them from the boundary words of the parents; here they are proved from boxes and diagonal bounds.

In the odd-first orientation (`W_1` odd) the two excluded mixed pairs of each child are separated by one coordinate of these
boxes: the real coordinate for the odd child (`(P^+, Q^{+,2})`, `(P^-, Q^{-,1})`), the imaginary one for the even child
(`(P^{+,1}, Q^-)`, `(P^{-,2}, Q^+)`). In the even-first orientation the boxes do not separate them in general; that case is
`ClosedPathDiagonal` (the diagonals `x + y` and `x - y`). -/

namespace FLatticePaper.Tiles.ClosedPathExcluded

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.MixedPieces FLatticePaper.Tiles.ClosedPathAssembly
open FLatticePaper.Tiles.ClosedPathStandard FLatticePaper.Tiles.StandardClause
open FLatticePaper.Tiles.Standard (oddTile evenTile)

/-! ### The box of the sites of a standard tile -/

/-- **The box of the odd standard tile**: `n - d + 1 ≤ x ≤ 2d` and `0 ≤ y ≤ 3n + d - 1` for the odd fraction `n/d` of `u`. -/
theorem site_box_odd (u : Word) (z : ℤ × ℤ) (hz : z ∈ oddTile u) :
    (fracOdd u).num - (fracOdd u).den + 1 ≤ z.1 ∧ z.1 ≤ 2 * (fracOdd u).den ∧ 0 ≤ z.2 ∧
      z.2 ≤ 3 * (fracOdd u).num + (fracOdd u).den - 1 := by
  obtain ⟨s, hs, hc⟩ := CellRegisters.tileH1_of_hcc (oddTile u) (Standard.oddTile_hcc u) z hz
  have hpl := SiteHullOdd.curO_pos_lt u
  have hb := SeamCover.box_of_mem (curO u) hpl.1 hpl.2 (oddTile u) (SubOddCopy.mem_oddTile_iff u) s
    (Finset.mem_coe.1 hs)
  have hmu : SiteInduction.muOf (SiteInduction.curO u) = 2 := by
    have h : ((SiteInduction.curO u).num + (SiteInduction.curO u).den) % 2 = 1 := SiteHullOdd.curO_odd u
    simp [SiteInduction.muOf, h]
  rw [hmu] at hb
  have hcu : curO u = fracOdd u := rfl
  rw [hcu] at hb
  obtain ⟨b1, b2, b3, b4⟩ := hb
  unfold CellDerivation.HasCorner at hc
  rcases hc with rfl | rfl | rfl | rfl <;> (try simp only [Prod.fst_add, Prod.snd_add]) <;> omega

/-- **The box of the even standard tile**: `n - d + 1 ≤ x ≤ d` and `0 ≤ y ≤ 2n + d - 1` for the even fraction `n/d` of `u`. -/
theorem site_box_even (u : Word) (z : ℤ × ℤ) (hz : z ∈ evenTile u) :
    (fracEven u).num - (fracEven u).den + 1 ≤ z.1 ∧ z.1 ≤ (fracEven u).den ∧ 0 ≤ z.2 ∧
      z.2 ≤ 2 * (fracEven u).num + (fracEven u).den - 1 := by
  obtain ⟨s, hs, hc⟩ := CellRegisters.tileH1_of_hcc (evenTile u) (Standard.evenTile_hcc u) z hz
  have hpl := SiteHullEven.curE_pos_lt u
  have hb := SeamCover.box_of_mem (curE u) hpl.1 hpl.2 (evenTile u) (SubEvenCopy.mem_evenTile_iff u) s
    (Finset.mem_coe.1 hs)
  have hmu : SiteInduction.muOf (SiteInduction.curE u) = 1 := by
    have h := SiteHullEven.curE_num_add_den_even u
    simp [SiteInduction.muOf, h]
  rw [hmu] at hb
  have hcu : curE u = fracEven u := rfl
  rw [hcu] at hb
  obtain ⟨b1, b2, b3, b4⟩ := hb
  unfold CellDerivation.HasCorner at hc
  rcases hc with rfl | rfl | rfl | rfl <;> (try simp only [Prod.fst_add, Prod.snd_add]) <;> omega

theorem box_shift_odd (u : Word) (v z : ℤ × ℤ) (hz : z ∈ shiftS (tOddSet u) v) :
    (fracOdd u).num - (fracOdd u).den + 1 ≤ z.1 - v.1 ∧ z.1 - v.1 ≤ 2 * (fracOdd u).den ∧ 0 ≤ z.2 - v.2 ∧
      z.2 - v.2 ≤ 3 * (fracOdd u).num + (fracOdd u).den - 1 := by
  have h := site_box_odd u (z - v) (Finset.mem_coe.1 (sub_mem_of_shift _ _ _ hz))
  simpa using h

theorem box_shift_even (u : Word) (v z : ℤ × ℤ) (hz : z ∈ shiftS (tEvenSet u) v) :
    (fracEven u).num - (fracEven u).den + 1 ≤ z.1 - v.1 ∧ z.1 - v.1 ≤ (fracEven u).den ∧ 0 ≤ z.2 - v.2 ∧
      z.2 - v.2 ≤ 2 * (fracEven u).num + (fracEven u).den - 1 := by
  have h := site_box_even u (z - v) (Finset.mem_coe.1 (sub_mem_of_shift _ _ _ hz))
  simpa using h

/-! ### The excluded pairs in the odd-first orientation -/

/-- **The excluded pairs of the odd child, `W_1` odd**: `P^+` (at `0`) lies left of `Q^{+,2}` (at `A + U`), and `P^-` (at
`2U + V`) right of `Q^{-,1}` (at `B`). -/
theorem exclOdd_oddFirst (w u1 u2 : Word) (hph : phase w = 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2) :
    (∀ z, z ∈ dOdd w u1 u2 0 → z ∈ dOdd w u1 u2 3 → False) ∧ (∀ z, z ∈ dOdd w u1 u2 1 → z ∈ dOdd w u1 u2 4 → False) := by
  have hP := oddP_of w hph
  have hQ := oddQ_of w hph
  have hqpos := SiteHullEven.curE_pos_lt u2
  have hcu : curE u2 = fracEven u2 := rfl
  rw [hcu, ← hq] at hqpos
  constructor
  · intro z h0 h3
    simp only [dOdd, pieceSet, hP, hQ] at h0 h3
    simp at h0 h3
    have b0 := box_shift_odd u1 _ z h0
    have b3 := box_shift_even u2 _ z h3
    rw [← hp] at b0
    rw [← hq] at b3
    simp only [texV1Odd, texV1Even, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at b0 b3
    omega
  · intro z h1 h4
    simp only [dOdd, pieceSet, hP, hQ] at h1 h4
    simp at h1 h4
    have b1 := box_shift_odd u1 _ z h1
    have b4 := box_shift_even u2 _ z h4
    rw [← hp] at b1
    rw [← hq] at b4
    simp only [texV1Even, texV2, Prod.fst_add, Prod.snd_add] at b1 b4
    omega

/-- **The excluded pairs of the even child, `W_1` odd**: `P^{+,1}` (at `0`) lies below `Q^-` (at `2B`), and `P^{-,2}` (at
`U + V + B`) above `Q^+` (at `A`). -/
theorem exclEven_oddFirst (w u1 u2 : Word) (hph : phase w = 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2) : ExclEven w u1 u2 := by
  have hP := evenP_of w hph
  have hQ := evenQ_of w hph
  have hppos := SiteHullOdd.curO_pos_lt u1
  have hcu : curO u1 = fracOdd u1 := rfl
  rw [hcu, ← hp] at hppos
  constructor
  · intro z h0 h5
    simp only [dEven, pieceSet, hP, hQ] at h0 h5
    simp at h0 h5
    have b0 := box_shift_odd u1 _ z h0
    have b5 := box_shift_even u2 _ z h5
    rw [← hp] at b0
    rw [← hq] at b5
    simp only [texV2, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at b0 b5
    omega
  · intro z h3 h4
    simp only [dEven, pieceSet, hP, hQ] at h3 h4
    simp at h3 h4
    have b3 := box_shift_odd u1 _ z h3
    have b4 := box_shift_even u2 _ z h4
    rw [← hp] at b3
    rw [← hq] at b4
    simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add] at b3 b4
    omega

/-- `ExclOdd` from the even-first case, which stays an input. -/
theorem exclOdd_of (w u1 u2 : Word) (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (hef : phase w ≠ 1 → (∀ z, z ∈ dOdd w u1 u2 0 → z ∈ dOdd w u1 u2 2 → False) ∧
      (∀ z, z ∈ dOdd w u1 u2 1 → z ∈ dOdd w u1 u2 5 → False)) : ExclOdd w u1 u2 := by
  unfold ExclOdd
  split_ifs with hph
  · exact exclOdd_oddFirst w u1 u2 hph hp hq
  · exact hef hph

/-- `ExclEven` from the even-first case, which stays an input. -/
theorem exclEven_of (w u1 u2 : Word) (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (hef : phase w ≠ 1 → ExclEven w u1 u2) : ExclEven w u1 u2 := by
  by_cases hph : phase w = 1
  · exact exclEven_oddFirst w u1 u2 hph hp hq
  · exact hef hph

end FLatticePaper.Tiles.ClosedPathExcluded
