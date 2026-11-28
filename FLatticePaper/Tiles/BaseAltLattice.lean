import FLatticePaper.Tiles.BaseWeakLattice

/-! # The lattice compatibilities of the alternate base odometers (`AltLatticeOddV2`, `AltLatticeEvenV2` at base words)

The alternate base values `paperStairAltValue`, `paperLadderAltValue`, `paperNearStairAltValue`, `paperNearLadderAltValue` are the
values of the periodic fields of the alternate rows of `prop:base_cases` (`UniqueRecurrentExtension`, `UniqueNearOneExtension`).
Each family is the lattice lemma of `BaseWeakLattice` for the standard family, with the alternate field: the odometer reads the
field at its shift `s`, and `latticeSelf_of_periods` gives `LatticeSelfCompatible` along the transverse vector `texV2 F` with
affine factor `offsetA F.num F.den true`, for the fraction `F` of the current register of the base word. -/

namespace FLatticePaper.Tiles.BaseAltLattice

open FLatticePaper.Farey
open FLatticePaper.Construction
open FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.BaseTileProps
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.DeckCoverage
open FLatticePaper.Tiles.SurgicalWeak
open FLatticePaper.Tiles.BaseWeakLattice

/-- The even alternate stair `paperStairAltTile (2k+3)`, read at the shift `0`: the even alternate of `3^k` (and of `[]` at `k = 0`). -/
theorem altLattice_stair (k : ℕ) (E : PartialOdometer)
    (hdom : ∀ x : GInt, x ∈ E.dom ↔ x ∈ paperStairAltTile (2 * (k : ℤ) + 3))
    (hval : ∀ x ∈ E.dom, E.val x = paperStairAltValue (2 * (k : ℤ) + 3) x) :
    LatticeSelfCompatible E (texV2 (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction)) (offsetA 1 (2 * (k : ℤ) + 3) true) := by
  obtain ⟨cU, cV, g, hagree, hper, -⟩ := (prop_base_cases_reciprocal_stair k).2.2.1.2.2
  have hv : ∀ x ∈ E.dom, E.val x = g (x + ((0 : ℤ), (0 : ℤ))) := by
    intro x hx
    rw [show x + ((0 : ℤ), (0 : ℤ)) = x by ext <;> simp, hval x hx]
    exact (hagree x ((hdom x).1 hx)).symm
  have key := latticeSelf_of_periods E (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction) g (0, 0) cU cV hper hv
  rw [modifiedDeck_transverse] at key
  exact key.2

/-- The odd alternate ladder `paperLadderAltTile (2k+2)` for `k ≥ 1`, read at the shift `(-1,-1)`: the odd alternate of `3^k`. -/
theorem altLattice_ladder (k : ℕ) (hk : 1 ≤ k) (O : PartialOdometer)
    (hdom : ∀ x : GInt, x ∈ O.dom ↔ x + ((-1 : ℤ), (-1 : ℤ)) ∈ paperLadderAltTile (2 * (k : ℤ) + 2))
    (hval : ∀ x ∈ O.dom, O.val x = paperLadderAltValue (2 * (k : ℤ) + 2) (x + ((-1 : ℤ), (-1 : ℤ)))) :
    LatticeSelfCompatible O (texV2 (⟨1, 2 * (k : ℤ) + 2⟩ : Fraction)) (offsetA 1 (2 * (k : ℤ) + 2) true) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
  have e : (2 * ((m + 1 : ℕ) : ℤ) + 2) = 2 * (m : ℤ) + 4 := by push_cast; ring
  rw [e] at hdom hval ⊢
  obtain ⟨cU, cV, g, hagree, hper, -⟩ := (prop_base_cases_doubled_stair m).2.2.1.2.2
  have hv : ∀ x ∈ O.dom, O.val x = g (x + ((-1 : ℤ), (-1 : ℤ))) := by
    intro x hx
    rw [hval x hx]
    exact (hagree _ ((hdom x).1 hx)).symm
  have key := latticeSelf_of_periods O (⟨1, 2 * (m : ℤ) + 4⟩ : Fraction) g (-1, -1) cU cV hper hv
  rw [modifiedDeck_transverse] at key
  exact key.2

/-- The odd alternate near stair `paperNearStairAltTile (2k+3)`, read at the shift `(0,1)`: the odd alternate of `[]` (at `k = 0`) and
of `2^k`. -/
theorem altLattice_nearStair (k : ℕ) (O : PartialOdometer)
    (hdom : ∀ x : GInt, x ∈ O.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (k : ℤ) + 3))
    (hval : ∀ x ∈ O.dom, O.val x = paperNearStairAltValue (2 * (k : ℤ) + 3) (x + ((0 : ℤ), (1 : ℤ)))) :
    LatticeSelfCompatible O (texV2 (⟨(k : ℤ) + 1, (k : ℤ) + 2⟩ : Fraction))
      (offsetA ((k : ℤ) + 1) ((k : ℤ) + 2) true) := by
  obtain ⟨cU, cV, g, hagree, hper, -⟩ := (prop_base_cases_near_stair k).2.2.1.2.2
  rw [rotate_stair_fraction k] at hper
  have hv : ∀ x ∈ O.dom, O.val x = g (x + ((0 : ℤ), (1 : ℤ))) := by
    intro x hx
    rw [hval x hx]
    exact (hagree _ ((hdom x).1 hx)).symm
  have key := latticeSelf_of_periods O (⟨(k : ℤ) + 1, (k : ℤ) + 2⟩ : Fraction) g (0, 1) cU cV hper hv
  rw [modifiedDeck_transverse] at key
  exact key.2

/-- The even alternate near ladder `paperNearLadderAltTile (2k+2)` for `k ≥ 1`, read at the shift `(0,1)`: the even alternate of `2^k`. -/
theorem altLattice_nearLadder (k : ℕ) (hk : 1 ≤ k) (E : PartialOdometer)
    (hdom : ∀ x : GInt, x ∈ E.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (k : ℤ) + 2))
    (hval : ∀ x ∈ E.dom, E.val x = paperNearLadderAltValue (2 * (k : ℤ) + 2) (x + ((0 : ℤ), (1 : ℤ)))) :
    LatticeSelfCompatible E (texV2 (⟨2 * (k : ℤ) + 1, 2 * (k : ℤ) + 3⟩ : Fraction))
      (offsetA (2 * (k : ℤ) + 1) (2 * (k : ℤ) + 3) true) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
  have hd' : (2 * ((m + 1 : ℕ) : ℤ) + 2) = 2 * (m : ℤ) + 4 := by push_cast; ring
  rw [hd'] at hdom hval
  obtain ⟨cU, cV, g, hagree, hper, -⟩ := (prop_base_cases_near_doubled_stair m).2.2.1.2.2
  rw [rotate_ladder_fraction m] at hper
  have e3 : (2 * ((m + 1 : ℕ) : ℤ) + 1) = 2 * (m : ℤ) + 3 := by push_cast; ring
  have e4 : (2 * ((m + 1 : ℕ) : ℤ) + 3) = 2 * (m : ℤ) + 5 := by push_cast; ring
  rw [e3, e4]
  have hv : ∀ x ∈ E.dom, E.val x = g (x + ((0 : ℤ), (1 : ℤ))) := by
    intro x hx
    rw [hval x hx]
    exact (hagree _ ((hdom x).1 hx)).symm
  have key := latticeSelf_of_periods E (⟨2 * (m : ℤ) + 3, 2 * (m : ℤ) + 5⟩ : Fraction) g (0, 1) cU cV hper hv
  rw [modifiedDeck_transverse] at key
  exact key.2

end FLatticePaper.Tiles.BaseAltLattice
