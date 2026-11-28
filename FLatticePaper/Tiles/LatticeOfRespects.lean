import FLatticePaper.Tiles.VerticalH2
import FLatticePaper.Tiles.ClosedWalkEven
import FLatticePaper.Tiles.JointFamily

/-! # Item (c) of `lemma:weak_standard_odometer_properties` from item (a)

Step 2 of the proof of `lemma:weak_standard_odometer_properties` copies the proof of (b), (c) of
`lemma:standard_tile_properties`: the surrounding of a standard tile consists of stacked zero-one boundary strings, and two
odometers that respect the strings of a stacked string are compatible (`lemma:stacked_zero_one_string`). So an odometer on a
standard tile that respects its boundary strings is compatible with its lattice adjacent translates.

In Lean this is the closed-walk constancy along both lattice vectors (`vertical_kappa_of`, `horizontal_kappa_of`,
`vertical_kappa_even_of`, `horizontal_kappa_even_of`), which use nothing but the respects of the one odometer, with the covering
of the overlaps by the strings discharged (`VerticalH2`, `OverlapSides`, the overlap form of item (c) of
`lemma:standard_tile_properties`).

* `latticeSelfCompatible_odd`, `latticeSelfCompatible_even`: an odometer with `RespectsAnchored` on the standard tile of `w`
  is `LatticeSelfCompatible` along `v_{n/d,1}` (affine factor `0`) and `v_{n/d,2}` (affine factor `a_{n/d,2}`).
* `weakProps_of_respects`: hence `JointFamily.WeakProps` (item (c)) for odometers on the two standard children of `w` that
  respect their boundary strings; this is `WeakStepAssembly.GlueLatticeInput` wherever `GlueRespectsInput` holds. -/

namespace FLatticePaper.Tiles.LatticeOfRespects

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.StandardClause
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.Standard (oddTile evenTile)
open FLatticePaper.Tiles.JointFamily (LatticeSelfCompatible WeakProps)

/-- **Item (c) for an odometer on the odd standard tile of `w` that respects its boundary strings.** -/
theorem latticeSelfCompatible_odd (w : Word) (o : PartialOdometer) (hd : o.dom = oddTile w)
    (hR : SurgicalWeak.RespectsAnchored (oddTile w) (hWordOf w false) (vWordOf w false) o.val) :
    LatticeSelfCompatible o (texV1Odd ((parentsAt w).current .odd)) 0 ∧
      LatticeSelfCompatible o (texV2 ((parentsAt w).current .odd))
        (offsetA ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den true) := by
  obtain ⟨κv, hv⟩ := vertical_kappa_of w (oddTile w) o.val hR (VerticalH2.vertical_H2X_odd w)
    (VerticalH2.vertical_H2Y_odd w)
  obtain ⟨κh, hh⟩ := horizontal_kappa_of w (oddTile w) o.val hR (OverlapSides.horizontal_H2X_odd w)
    (OverlapSides.horizontal_H2Y_odd w)
  refine ⟨⟨κv, fun x hx hxv => ?_⟩, ⟨-κh, fun x hx hxv => ?_⟩⟩
  · rw [hd] at hx hxv
    have h := hv (x + texV1Odd (fracOdd w)) (Finset.mem_coe.2 hxv) (by simpa using hx)
    rw [add_sub_cancel_right] at h
    have h0 : dotS 0 x = 0 := by simp [dotS]
    rw [h0, sub_zero]
    exact h
  · rw [hd] at hx hxv
    have h := hh x (Finset.mem_coe.2 hx) (by rw [sub_neg_eq_add]; exact Finset.mem_coe.2 hxv)
    rw [sub_neg_eq_add] at h
    simp only [dotS, offsetA]
    have e : ((parentsAt w).current .odd) = fracOdd w := rfl
    rw [e]
    linarith

/-- **Item (c) for an odometer on the even standard tile of `w` that respects its boundary strings.** -/
theorem latticeSelfCompatible_even (w : Word) (o : PartialOdometer) (hd : o.dom = evenTile w)
    (hR : SurgicalWeak.RespectsAnchored (evenTile w) (hWordOf w true) (vWordOf w true) o.val) :
    LatticeSelfCompatible o (texV1Even ((parentsAt w).current .even)) 0 ∧
      LatticeSelfCompatible o (texV2 ((parentsAt w).current .even))
        (offsetA ((parentsAt w).current .even).num ((parentsAt w).current .even).den true) := by
  obtain ⟨κv, hv⟩ := vertical_kappa_even_of w (evenTile w) o.val hR (VerticalH2.vertical_H2X_even w)
    (VerticalH2.vertical_H2Y_even w)
  obtain ⟨κh, hh⟩ := horizontal_kappa_even_of w (evenTile w) o.val hR (OverlapSides.horizontal_H2X_even w)
    (OverlapSides.horizontal_H2Y_even w)
  refine ⟨⟨κv, fun x hx hxv => ?_⟩, ⟨-κh, fun x hx hxv => ?_⟩⟩
  · rw [hd] at hx hxv
    have h := hv (x + texV1Even (fracEven w)) (Finset.mem_coe.2 hxv) (by simpa using hx)
    rw [add_sub_cancel_right] at h
    have h0 : dotS 0 x = 0 := by simp [dotS]
    rw [h0, sub_zero]
    exact h
  · rw [hd] at hx hxv
    have h := hh x (Finset.mem_coe.2 hx) (by rw [sub_neg_eq_add]; exact Finset.mem_coe.2 hxv)
    rw [sub_neg_eq_add] at h
    simp only [dotS, offsetA]
    have e : ((parentsAt w).current .even) = fracEven w := rfl
    rw [e]
    linarith

/-- **`WeakProps` (item (c)) from item (a)**: odometers on the two standard children of `w` that respect their boundary
strings are compatible with their lattice adjacent translates. -/
theorem weakProps_of_respects (w : Word) (go ge : Site → ℤ)
    (hRo : SurgicalWeak.RespectsAnchored (oddTile w) (hWordOf w false) (vWordOf w false) go)
    (hRe : SurgicalWeak.RespectsAnchored (evenTile w) (hWordOf w true) (vWordOf w true) ge) :
    WeakProps w ⟨oddTile w, go⟩ ⟨evenTile w, ge⟩ := by
  obtain ⟨h1, h2⟩ := latticeSelfCompatible_odd w ⟨oddTile w, go⟩ rfl hRo
  obtain ⟨h3, h4⟩ := latticeSelfCompatible_even w ⟨evenTile w, ge⟩ rfl hRe
  exact ⟨h1, h2, h3, h4⟩

end FLatticePaper.Tiles.LatticeOfRespects
