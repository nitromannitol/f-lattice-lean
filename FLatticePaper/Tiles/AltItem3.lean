import FLatticePaper.Tiles.AltPieces
import FLatticePaper.Tiles.StdPseudoAnchoredSets
import FLatticePaper.Tiles.BaseInvariant
import FLatticePaper.Tiles.VBase
import FLatticePaper.Tiles.StackedTable
import FLatticePaper.Tiles.VLinVertical

/-! # Item (3) of `lemma:alternate_tile_properties`: the strings that start at `c(T̂) + s`

Surgical edition 3243bef, `lemma:alternate_tile_properties` (3) and Step 2 of its proof: the even alternate child `T̂(q₀)` is a
`w_h(q₀)`-pseudo-square whose forward horizontal string starts at `c(T̂)`, and the odd alternate child `T̂(p₀)` is a
`w_v(p₀)`-pseudo-square whose reversed vertical string starts at `c(T̂) + s` (`s = 0` in the even-first orientation,
`s = -v_{q₁,1} + v_{p₁,2}` otherwise). In the frame of `SurgicalAltTiles` `c(T̂) = 0`.

The proof of the text glues the strings of two standard subtiles (its table in Step 2): the forward horizontal word of `q₀` is
`w_h(q₁) w_h(p₁)` (even-first) or `w_h(p₁) w_h(q₁)` (odd-first), each block starting with `q` and ending with `p`, so the string of
the second block is the translate of its own string by the junction offset (`HorizontalGlue.mem_junction`), and each block lies
in its copy (`T(q₁)^{+,1}` and `T(p₁)^+`, resp. `T(p₁)^+` and `T(q₁)^{+,1}`). The reversed vertical string of `p₀` is glued in
the same way from `T(q₁)^+` and `T(p₁)^{-,1}` (even-first) or `T(p₁)^{+,2}` and `T(q₁)^-` (odd-first)
(`VGlue.mem_vjunction`). The strings of the parents lie in the parent tiles by the horizontal and vertical invariants of the
standard tiles (`HorizontalStep.Inv`, `VStep.VInv`). -/

namespace FLatticePaper.Tiles.AltItem3

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile swapW)
open FLatticePaper.Tiles.SurgicalAlt (coeffOff altP0Coeff altQ0Coeff)
open FLatticePaper.Tiles.SurgicalDict (altShifts)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.AltRotStep (offP0 offQ0 shP shQ oddStd evenStd)
open FLatticePaper.Tiles.AltPieces
open FLatticePaper.Tiles.SiteStrings (stringSites hWordOf vWordOf)
open FLatticePaper.Tiles.HorizontalGlue (HC jn)
open FLatticePaper.Tiles.VJunction (vert VS0 jv)
open FLatticePaper.Tiles.VGlue (HV)

/-! ### Membership in the alternate children through their standard copies -/

theorem mem_altEven_of_P (base : Word → Tile × Tile) {w : Word} (hw : ¬ IsBase w) {a z : Site}
    (ha : a ∈ evenPOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even) (hz : z ∈ shift (stateAt w).tOdd a) :
    z ∈ altEvenTile base w := by
  obtain ⟨x, -, he⟩ := altEvenTile_eq base hw
  rw [he, Finset.mem_union, mem_evenStd_iff]
  exact Or.inl (Or.inl ⟨a, ha, hz⟩)

theorem mem_altEven_of_Q (base : Word → Tile × Tile) {w : Word} (hw : ¬ IsBase w) {b z : Site}
    (hb : b ∈ evenQOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even) (hz : z ∈ shift (stateAt w).tEven b) :
    z ∈ altEvenTile base w := by
  obtain ⟨x, -, he⟩ := altEvenTile_eq base hw
  rw [he, Finset.mem_union, mem_evenStd_iff]
  exact Or.inl (Or.inr ⟨b, hb, hz⟩)

theorem mem_altOdd_of_P (base : Word → Tile × Tile) {w : Word} (hw : ¬ IsBase w) {a z : Site}
    (ha : a ∈ oddPOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even) (hz : z ∈ shift (stateAt w).tOdd a) :
    z ∈ altOddTile base w := by
  obtain ⟨x, -, he⟩ := altOddTile_eq base hw
  rw [he, Finset.mem_union, mem_oddStd_iff]
  exact Or.inl (Or.inl ⟨a, ha, hz⟩)

theorem mem_altOdd_of_Q (base : Word → Tile × Tile) {w : Word} (hw : ¬ IsBase w) {b z : Site}
    (hb : b ∈ oddQOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even) (hz : z ∈ shift (stateAt w).tEven b) :
    z ∈ altOddTile base w := by
  obtain ⟨x, -, he⟩ := altOddTile_eq base hw
  rw [he, Finset.mem_union, mem_oddStd_iff]
  exact Or.inl (Or.inr ⟨b, hb, hz⟩)

/-! ### The parents' strings in the registers -/

/-- The horizontal invariant of every word: the forward strings of the four words of the quadruple lie in the tiles. -/
theorem inv_all (w : Word) : HorizontalStep.Inv w :=
  HorizontalInduction.inv_all BaseInvariant.inv_nil
    (fun n hn => by
      obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
      exact BaseInvariant.inv_three j)
    (fun n hn => by
      obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
      exact BaseInvariant.inv_two j) w

theorem inner_odd {w : Word} (hw : ¬ IsBase w) : ParentInterior.Inner01 (parentsAt w).odd := by
  obtain ⟨h1, h2, -⟩ := parents_facts hw
  exact ⟨h1, h2⟩

theorem inner_even {w : Word} (hw : ¬ IsBase w) : ParentInterior.Inner01 (parentsAt w).even := by
  obtain ⟨-, -, h3, h4, -⟩ := parents_facts hw
  exact ⟨h3, h4⟩

theorem phase_eq_count (w : Word) : phase w = w.count Digit.one % 2 := rfl

/-! ### The forward horizontal string of `T̂(q₀)` at `c(T̂) = 0` -/

theorem sub_off_zero_dsQ1Plus (p q : Fraction) (z : Site) : z - offQ0 false p q .dsQ1Plus = z := by
  ext <;> simp [offQ0, coeffOff, altQ0Coeff]

theorem sub_off_zero_p1Plus (p q : Fraction) (z : Site) : z - offQ0 true p q .p1Plus = z := by
  ext <;> simp [offQ0, coeffOff, altQ0Coeff]

/-- **The forward horizontal string of the even alternate child lies in the tile**: the string of `w_h(q₀)` started at
`c(T̂) = 0`. -/
theorem fwdH_even (base : Word → Tile × Tile) {w : Word} (hw : ¬ IsBase w) :
    HC (hWordOf w true) (altEvenTile base w) := by
  intro z hz
  have QI := CeilWords.quadInv_all w
  obtain ⟨⟨P', hP', hPl⟩, hjP⟩ := HorizontalStep.block_odd_blk _ _ QI.2.2.1 (inner_odd hw)
  obtain ⟨⟨Q', hQ', hQl⟩, hjQ⟩ := HorizontalStep.block_even_blk _ _ QI.2.2.2 (inner_even hw)
    (parentsAt_valid w).even_parity
  obtain ⟨-, -, hIP, hIQ⟩ := inv_all w
  have hc := (StackedTable.quad_childs w).2
  unfold hWordOf at hz
  rw [if_pos rfl, hc] at hz
  unfold childWords at hz
  by_cases h : w.count Digit.one % 2 = 0
  · have ho : (phase w == 1) = false := by simp [phase_eq_count, h]
    rw [if_pos h] at hz
    rw [hP', hQ'] at hz
    rw [hQ'] at hQl hjQ hIQ
    rw [hP'] at hIP
    rcases (HorizontalGlue.mem_junction Q' P' hQl z).1 hz with h1 | ⟨y, hy, rfl⟩
    · refine mem_altEven_of_Q base hw (b := offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) ?_ ?_
      · rw [ho]; simp [evenQOffs]
      · rw [mem_shift, sub_off_zero_dsQ1Plus]; exact hIQ z h1
    · refine mem_altEven_of_P base hw (a := offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) ?_ ?_
      · rw [ho]; simp [evenPOffs]
      · rw [mem_shift, hjQ]
        have : y + texV1Even (parentsAt w).even - offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus = y := by
          ext <;> simp [offQ0, coeffOff, altQ0Coeff, texV1Even]
        rw [this]; exact hIP y hy
  · have ho : (phase w == 1) = true := by simp [phase_eq_count]; omega
    rw [if_neg h] at hz
    rw [hP', hQ'] at hz
    rw [hP'] at hPl hjP hIP
    rw [hQ'] at hIQ
    rcases (HorizontalGlue.mem_junction P' Q' hPl z).1 hz with h1 | ⟨y, hy, rfl⟩
    · refine mem_altEven_of_P base hw (a := offQ0 true (parentsAt w).odd (parentsAt w).even .p1Plus) ?_ ?_
      · rw [ho]; simp [evenPOffs]
      · rw [mem_shift, sub_off_zero_p1Plus]; exact hIP z h1
    · refine mem_altEven_of_Q base hw (b := offQ0 true (parentsAt w).odd (parentsAt w).even .dsQ1Plus) ?_ ?_
      · rw [ho]; simp [evenQOffs]
      · rw [mem_shift, hjP]
        have : y + texV1Odd (parentsAt w).odd - offQ0 true (parentsAt w).odd (parentsAt w).even .dsQ1Plus = y := by
          ext <;> simp [offQ0, coeffOff, altQ0Coeff, texV1Odd]
        rw [this]; exact hIQ y hy

/-! ### The reversed vertical string of `T̂(p₀)` at `c(T̂) + s` -/

theorem count_one_swapW (w : Word) : (swapW w).count Digit.one = w.count Digit.one := by
  unfold swapW
  induction w with
  | nil => rfl
  | cons d w ih =>
    cases d <;> simp [ih, Digit.swapTwoThree]

/-- The vertical sites of the reversed vertical word of the odd alternate child, at the origin. -/
theorem odd_vrev_word (w : Word) : (vWordOf w false).reverse = vert (FLatticePaper.Tiles.quadAt [] (swapW w)).childQ := by
  simp [vWordOf, vert]

/-- **The reversed vertical string of the odd alternate child lies in the tile**, translated by `s` (`altOffsetS w`): every
vertical site `z` of `rev(w_v(p₀))` at the origin gives `z + s ∈ T̂(p₀)`. -/
theorem revV_odd (base : Word → Tile × Tile) {w : Word} (hw : ¬ IsBase w) :
    ∀ z ∈ VS0 (vWordOf w false).reverse, z + SurgicalAlt.altOffsetS w ∈ altOddTile base w := by
  intro z hz
  rw [odd_vrev_word] at hz
  have hsw : ¬ IsBase (swapW w) := Standard.nonbase_swap hw
  have QI := CeilWords.quadInv_all (swapW w)
  have hvS := parentsAt_valid (swapW w)
  obtain ⟨hPl, hjP⟩ := VStep.vblk_odd _ _ QI.2.2.1 (inner_odd hsw) hvS.odd_parity
  obtain ⟨hQl, hjQ⟩ := VStep.vblk_even _ _ QI.2.2.2 (inner_even hsw) hvS.even_parity
  rw [VStep.rot_parent_odd_swap] at hjP
  rw [VStep.rot_parent_even_swap] at hjQ
  obtain ⟨Y, hY⟩ := VJunction.vertical_head _ hPl
  obtain ⟨Z, hZ⟩ := VJunction.vertical_head _ hQl
  obtain ⟨-, -, hVP, hVQ⟩ := VBase.vinv_all w
  have hc := (StackedTable.quad_childs (swapW w)).2
  rw [hc] at hz
  unfold childWords at hz
  rw [count_one_swapW] at hz
  by_cases h : w.count Digit.one % 2 = 0
  · have ho : (phase w == 1) = false := by simp [phase_eq_count, h]
    have hs : SurgicalAlt.altOffsetS w = (0, 0) := by simp [SurgicalAlt.altOffsetS, ho]
    rw [if_pos h, VJunction.vert_append, hY, hZ] at hz
    rw [hY] at hjP hVP
    rw [hZ] at hVQ
    rw [hs, show z + ((0 : ℤ), (0 : ℤ)) = z by ext <;> simp]
    rcases (VGlue.mem_vjunction _ _ ⟨Y, rfl⟩ ⟨Z, rfl⟩ z).1 hz with h1 | ⟨y, hy, rfl⟩
    · refine mem_altOdd_of_Q base hw (b := offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) ?_ ?_
      · rw [ho]; simp [oddQOffs]
      · rw [mem_shift]
        have : z - offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus = z := by
          ext <;> simp [offP0, coeffOff, altP0Coeff]
        rw [this]; exact hVP z h1
    · refine mem_altOdd_of_P base hw (a := offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) ?_ ?_
      · rw [ho]; simp [oddPOffs]
      · rw [mem_shift, hjP]
        have : y + texV2 (parentsAt w).even - offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus = y := by
          ext <;> simp [offP0, coeffOff, altP0Coeff, texV2]
        rw [this]; exact hVQ y hy
  · have ho : (phase w == 1) = true := by simp [phase_eq_count]; omega
    rw [if_neg h, VJunction.vert_append, hY, hZ] at hz
    rw [hZ] at hjQ hVQ
    rw [hY] at hVP
    rcases (VGlue.mem_vjunction _ _ ⟨Z, rfl⟩ ⟨Y, rfl⟩ z).1 hz with h1 | ⟨y, hy, rfl⟩
    · refine mem_altOdd_of_P base hw (a := shP true (parentsAt w).odd (parentsAt w).even +
          offP0 true (parentsAt w).odd (parentsAt w).even .dsP1Plus) ?_ ?_
      · rw [ho]; simp [oddPOffs]
      · rw [mem_shift]
        have : z + SurgicalAlt.altOffsetS w - (shP true (parentsAt w).odd (parentsAt w).even +
            offP0 true (parentsAt w).odd (parentsAt w).even .dsP1Plus) = z := by
          simp only [SurgicalAlt.altOffsetS, ho, if_true]
          ext <;> simp [shP, offP0, coeffOff, altP0Coeff, altShifts]
        rw [this]; exact hVQ z h1
    · refine mem_altOdd_of_Q base hw (b := offP0 true (parentsAt w).odd (parentsAt w).even .q1Minus) ?_ ?_
      · rw [ho]; simp [oddQOffs]
      · rw [mem_shift, hjQ]
        have : y + texV2 (parentsAt w).odd + SurgicalAlt.altOffsetS w -
            offP0 true (parentsAt w).odd (parentsAt w).even .q1Minus = y := by
          simp only [SurgicalAlt.altOffsetS, ho, if_true]
          ext <;> simp [offP0, coeffOff, altP0Coeff, texV2] <;> ring
        rw [this]; exact hVP y hy

/-! ### The two strings in the placed form of `def:partial_tile_boundary_strings` -/

theorem mem_placedSites_map (ts : List (ZTile × GInt)) (e x : GInt) :
    x ∈ placedSites (ts.map fun p => (p.1, p.2 + e)) ↔ x - e ∈ placedSites ts := by
  simp only [placedSites, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨t, ⟨t', ht', rfl⟩, b, hb, rfl⟩
    exact ⟨t', ht', b, hb, by simp only; abel⟩
  · rintro ⟨t, ht, b, hb, hx⟩
    refine ⟨(t.1, t.2 + e), ⟨t, ht, rfl⟩, b, hb, ?_⟩
    simp only
    rw [← add_assoc, hx, sub_add_cancel]

theorem placed_vRev_iff_VS0 (u : BinaryWord) (x : GInt) : x ∈ placedSites (vRevStringAt u (0, 0)) ↔ x ∈ VS0 u := by
  rw [StdPseudoAnchoredSets.placed_vRevStringAt_iff, List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have := (MarksIn.stringSites_true_iff u y).1 hy
    simpa using this
  · intro hx
    refine ⟨(x.1 + 1, x.2 + 1), (MarksIn.stringSites_true_iff u _).2 (by simpa using hx), ?_⟩
    ext <;> simp

/-- **Item (3), even child, the forward horizontal string**: the string of `w_h(q₀)` started at `c(T̂) = 0` lies in `T̂(q₀)`. -/
theorem item3_fwdH (base : Word → Tile × Tile) {w : Word} (hw : ¬ IsBase w) :
    InsideTile {x | x ∈ altEvenTile base w} (hStringAt (hWordOf w true) (0, 0)) := by
  intro x hx
  rw [StdPseudoAnchoredSets.placed_hStringAt_iff] at hx
  exact fwdH_even base hw x hx

/-- **Item (3), odd child, the reversed vertical string**: the string of `rev(w_v(p₀))` started at `c(T̂) + s` lies in
`T̂(p₀)`. -/
theorem item3_revV (base : Word → Tile × Tile) {w : Word} (hw : ¬ IsBase w) :
    InsideTile {x | x ∈ altOddTile base w} (vRevStringAt (vWordOf w false).reverse (SurgicalAlt.altOffsetS w)) := by
  intro x hx
  have e : SurgicalAlt.altOffsetS w = (0, 0) + SurgicalAlt.altOffsetS w := by ext <;> simp
  rw [e, vRevStringAt_add, mem_placedSites_map, placed_vRev_iff_VS0] at hx
  have := revV_odd base hw _ hx
  rwa [sub_add_cancel] at this

end FLatticePaper.Tiles.AltItem3
