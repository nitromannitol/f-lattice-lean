import FLatticePaper.Plane.Induction.TwosMinusTile
import FLatticePaper.Plane.Induction.TwosFlatPlus

/-! The sign `-1` flatness of the twos field: the flatness of every selected input of equal potential, from the tile claim of
`TwosMinusTile` through the reduction `flat_of_tile` with the kernel drift `-1` and the transverse drift `-2`. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- The sign `-1` flatness: a selected input of equal potential has rank below its centre. -/
theorem twos_flat_minus (k : ℕ) {c i : Site}
    (hT : TwosSel (2 * (k : ℤ) + 4) (-1) (standardField (List.replicate (k + 1) Digit.two)) c i)
    (hΦ : twosPhi k (-1) i = twosPhi k (-1) c) :
    rhoTwos (2 * (k : ℤ) + 4) (-1) i < rhoTwos (2 * (k : ℤ) + 4) (-1) c := by
  obtain ⟨S, hagree, hperiod, -⟩ := ladderOdd_exists_extension (ladderOdd_valid_twos k)
  exact flat_of_tile k (-1) (-1) (-2)
    (fun z => by have h := twosPhi_kernel_minus k z; linarith)
    (fun z => by have h := twosPhi_transverse_minus k z; linarith)
    (twos_hTile_minus k hagree hperiod) hT hΦ

end FLatticePaper.TwosEPolicy
