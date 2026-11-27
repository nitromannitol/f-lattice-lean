import FLatticePaper.Plane.Induction.FreePolicy
import FLatticePaper.Plane.Induction.ComparisonEmpty

/-! # The satisfying selection of the games step: the reduction to the unit squares (Q42 part (1))

`HasSatSelection F` asks for a selection that picks an input at every white site and satisfies every unit-square clause. The canonical
selection `FreePolicy.freeSel frame F 1` picks an input at every white site as soon as the forced outputs exist (`ForcedExists`, which
`FreePolicy.forcedExists_of` gives from `W1Forced` and the packet). Hence the satisfying selection reduces to the square clauses of
`freeSel` alone. -/

namespace FLatticePaper.FreeSelSat

open FLatticePaper FLatticePaper.Induction FLatticePaper.FreePolicy FLatticePaper.SquareClauses

/-- **The reduction.** If the forced outputs exist and the canonical free selection satisfies every unit-square clause, then `F` has a
satisfying selection. -/
theorem hasSat_of_freeSel_squares (frame : ChildFrame) (F : Field) (hex : ForcedExists frame F)
    (hsq : ∀ a b : ℤ, SquareClauseSat F (freeSel frame F 1) a b) : HasSatSelection F :=
  ⟨freeSel frame F 1, fun _ hc => freeSel_input frame F 1 (Or.inl rfl) hex hc, hsq⟩

end FLatticePaper.FreeSelSat
