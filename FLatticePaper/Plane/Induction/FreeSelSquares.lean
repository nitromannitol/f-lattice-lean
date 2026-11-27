import FLatticePaper.Plane.Induction.FreeSelSat
import FLatticePaper.Plane.Induction.ProtectedWeb

/-! # The square clauses of the canonical free selection (Q42 part (1))

Case 1: a unit square with exactly one free corner. The Protected Web lemma gives a nonfree white corner `u` with a free input `w`
outside the square. The canonical selection at `u` is the forced output `forcedSel F u`, and `ProtectedWeb.forced_conj` says that the
free input `w` of `u` equals that forced output. So the selection at `u` leaves the square, and the clause holds. -/

namespace FLatticePaper.FreeSelSquares

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreePolicy FLatticePaper.SquareClauses FLatticePaper.ProtectedWeb
  FLatticePaper.AndOrRank FLatticePaper.FreeClosure

/-- **Case 1.** A unit square with exactly one free corner `y` satisfies its square clause for the canonical free selection. -/
theorem squareClause_of_one_free {frame : ChildFrame} {F : Field} (hW : WebHyp frame F) (hex : ForcedExists frame F)
    {a b : ℤ} {y : Site} (hy : y ∈ squareCorners a b) (hfy : freeClosure frame y)
    (hothers : ∀ c ∈ squareCorners a b, c ≠ y → ¬ freeClosure frame c) :
    SquareClauseSat F (freeSel frame F 1) a b := by
  intro hall
  obtain ⟨u, huQ, hune, hlapu, w, hw_eq, hwQ, hwfc⟩ := web_general hW hy hfy hothers
  have hnfu : ¬ freeClosure frame u := hothers u huQ hune
  have hk := hall u huQ
  have hne : laplacian F u ≠ -1 := by
    rw [hlapu]
    norm_num
  unfold keptInside at hk
  rw [if_neg hne] at hk
  have hfo : ForcedEdge F (fun _ _ => False) u (forcedSel F u) :=
    forcedSel_spec (hex u hnfu hlapu)
  have hsel : freeSel frame F 1 u = forcedSel F u :=
    (freePolicy_out_iff hlapu hnfu).mp (freeSel_spec frame F 1 hlapu)
  have hweq : w = forcedSel F u := (forced_conj hW u (forcedSel F u) hfo).2 w hw_eq hwfc
  rw [hsel, ← hweq] at hk
  exact hwQ hk

end FLatticePaper.FreeSelSquares
