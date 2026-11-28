import FLatticePaper.Tiles.CorrectedPositiveTwoFamily
import FLatticePaper.Tiles.MixedRegisterTwoReverse

/-! The odd alternate on a two exit and the even alternate on a three exit need only the six standard parents. -/

namespace FLatticePaper.Tiles.CorrectedSixCopyAlternates

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard
open JointFamily LCorrecProps CorrectedEvenPlacement CorrectedPlacementFrames
open CorrectedAlternatePolygons

theorem nonbase_append (w v : Word) (hw : ¬IsBase w) : ¬IsBase (w++v) := by
  rintro (nil|three|two)
  · exact hw (Or.inl (List.append_eq_nil_iff.mp nil).1)
  · exact hw (Or.inr (Or.inl (fun d m => three d (List.mem_append_left _ m))))
  · exact hw (Or.inr (Or.inr (fun d m => two d (List.mem_append_left _ m))))

private theorem reverse (x : Digit) (xs : Word) (hw : ¬IsBase (x::xs))
    (sign : (parentsAt (x::xs)).odd.det (parentsAt (x::xs)).even= -1) : MixedAt ((x::xs)++[.two]) false := by
  have hn := nonbase_append (x::xs) [exit false] hw
  apply CorrectedMixedSources.mixed_at (x::xs) false false hn (by intro bad; cases bad)
  intro z
  apply (CorrectedMixedPlacement.physical x xs hw false false z).mp
  rw [sign]
  exact MixedRegisterTwoReverse.word x xs hw false z sign

/-- The odd alternate on every two exit of a non-base word, with no comparison of the preceding alternate. -/
theorem after_two (w : Word) (hw : ¬IsBase w) : MixedAt (w++[.two]) false := by
  rcases (parentsAt_valid w).unit_det with pos|neg
  · exact CorrectedPositiveTwoFamily.alternate w pos
  · cases w with
    | nil => exact False.elim (hw (Or.inl rfl))
    | cons x xs => exact reverse x xs hw neg

/-- The even alternate target at every three exit of a non-base word is its two printed polygons. -/
theorem after_three (v : Word) (hv : ¬IsBase v) : MixedAt (v++[.three]) true :=
  CorrectedAlternateRotation.after_three v true (after_two (swapW v) (nonbase_swap hv))

end FLatticePaper.Tiles.CorrectedSixCopyAlternates
