import FLatticePaper.Plane.Induction.TwosHTile
import FLatticePaper.Plane.Induction.TwosFlatReduce

/-! Twos flatness, the flatness input `hflatP` of sign `+1` in full: every selected edge with equal chain potential strictly
lowers `rhoTwos`, from the tile claim `twos_hTile_plus` by the reduction `flat_of_tile`. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- The flatness input of sign `+1`, for every centre. -/
theorem twos_flat_plus (k : ℕ) {c i : Site}
    (hT : TwosSel (2 * (k : ℤ) + 4) 1 (standardField (List.replicate (k + 1) Digit.two)) c i)
    (hΦ : twosPhi k 1 i = twosPhi k 1 c) :
    rhoTwos (2 * (k : ℤ) + 4) 1 i < rhoTwos (2 * (k : ℤ) + 4) 1 c := by
  obtain ⟨S, hagree, hperiod, -⟩ := ladderOdd_exists_extension (ladderOdd_valid_twos k)
  exact flat_of_tile k 1 (-1) 2
    (fun z => by have h := twosPhi_kernel_plus k z; linarith)
    (fun z => by have h := twosPhi_transverse_plus k z; linarith)
    (twos_hTile_plus k hagree hperiod) hT hΦ

end FLatticePaper.TwosEPolicy
