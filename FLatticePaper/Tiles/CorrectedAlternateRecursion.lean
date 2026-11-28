import FLatticePaper.Tiles.CorrectedAlternateRotation
import FLatticePaper.Tiles.CorrectedMixedSources

/-! Reduction of all alternate parents to first-exit comparisons and the two ordinary register diagrams. -/

namespace FLatticePaper.Tiles.CorrectedAlternateRecursion

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard
open CorrectedEvenPlacement CorrectedPlacementFrames CorrectedAlternatePolygons
open CorrectedDomainLattice CorrectedRegisterWords CorrectedWordCoverage

/-- The first non-base alternate after a pure predecessor at either retained exit. -/
def FirstExits := ∀ (w : Word) (one even : Bool), IsBase w → ¬IsBase (w++[exit one]) →
  MixedAt (w++[exit one]) even

/-- The mixed determinant comparison on a non-base preceding word at every physical site. -/
def RegisterComparisons := ∀ (x : Digit) (xs : Word), ¬IsBase (x::xs) → ∀ (one even : Bool) (z : Site),
  let P := parentsAt (x::xs)
  let p := P.current .odd
  let prev := -P.odd.det P.even
  let r := register P one 1 (chart p (representative z))
  let shape := CorrectedMixedDiagram.mixed r one prev even
  Covers (fun i => CorrectedRegisterFaces.exact ((shape i).probe r (CorrectedCellsBands.oddSite z) (firstSector x)))
    true (if one || even then 8 else 6)

private theorem at_length (base : FirstExits) (registers : RegisterComparisons) (n : ℕ) :
    ∀ w : Word, w.length=n → ¬IsBase w → ∀ even : Bool, MixedAt w even := by
  induction n using Nat.strong_induction_on with
  | h n shorter =>
    have next (v : Word) (one even : Bool) (lt : v.length<n) (hn : ¬IsBase (v++[exit one])) :
        MixedAt (v++[exit one]) even := by
      by_cases pure : IsBase v
      · exact base v one even pure hn
      · apply CorrectedMixedSources.mixed_at v one even hn
        · intro _; exact shorter v.length lt v rfl pure (!even)
        · intro z
          cases v with
          | nil => exact False.elim (pure (Or.inl rfl))
          | cons x xs =>
            exact (CorrectedMixedPlacement.physical x xs pure one even z).mp (registers x xs pure one even z)
    intro w len hn even
    induction w using List.reverseRecOn with
    | nil => exact False.elim (hn (Or.inl rfl))
    | append_singleton v s _ =>
      have lt : v.length<n := by simp only [List.length_append,List.length_singleton] at len; omega
      cases s with
      | one => exact next v true even lt hn
      | two => exact next v false even lt hn
      | three =>
        apply CorrectedAlternateRotation.after_three
        apply next (swapW v) false (!even) (by rwa [JointRot.length_swapW])
        have sw : swapW (v++[.three])=swapW v++[exit false] := by rw [JointRot.swapW_append]; rfl
        rw [←sw]; exact Standard.nonbase_swap hn

/-- All non-base alternates have the two prescribed polygons when the base and register
comparisons hold. The three exit uses the rotated two exit at the same child length. -/
theorem all_words (first : FirstExits) (registers : RegisterComparisons) (w : Word) (hn : ¬IsBase w) (even : Bool) :
    MixedAt w even := at_length first registers w.length w rfl hn even

end FLatticePaper.Tiles.CorrectedAlternateRecursion
