import FLatticePaper.Plane.Induction.ReturnTable
import FLatticePaper.Plane.Induction.AndOrRank
import FLatticePaper.Plane.Induction.FanCompat

/-! # A nonfree white selects a free white input (AUDIT_FREE_THREE_STEP_RETURNS §1, "Nonfree/free adjacency")

A forced white `c` with forcing square `Q` (the unit rule `ForcedEdge.unit`) rejects its outside input `o`. Its other input lies inside `Q`.
If that inside input `o'` were a white free site, it would be a corner of `Q` with `laplacian = 0` and `≠ c`, so the unit rule forces it
(`hforced`): `ForcedEdge o' (inside o')`, hence `o'` is non-free (`forcedNF_of_witness`), a contradiction. So the forced input is the free
input: a forced white `c` with a free white input `o` selects `o`. The argument uses only the unit rule and `hforcedNF`. -/

namespace FLatticePaper.FreeAdjacency

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.ReturnTable
open FLatticePaper.FanCompat

theorem incomingNeg_ne (x : Site) : incomingNeg x ≠ x := by
  unfold incomingNeg
  split_ifs with h
  · intro e
    have e1 := congrArg Prod.fst e
    simp at e1
  · intro e
    have e2 := congrArg Prod.snd e
    simp at e2

theorem incomingPos_ne (x : Site) : incomingPos x ≠ x := by
  unfold incomingPos
  split_ifs with h
  · intro e
    have e1 := congrArg Prod.fst e
    simp at e1
  · intro e
    have e2 := congrArg Prod.snd e
    simp at e2

/-- **A strict forced white selects its free white input.** A strict forced white has a strict-interior derivation (`strictForced`); its
corners are strict, hence non-free, so a free white input is not a corner. The forced input is then the outside input of the square. -/
theorem forced_input_of_free_strict {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (P : FLatticePaper.W1Witness.OldPolicyWitness frame G seed η) (hs : ∀ y i, ¬ seed y i)
    {c i o : Site} (hcS : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den c) (hF : ForcedEdge G seed c i)
    (ho : o = incomingNeg c ∨ o = incomingPos c) (hfree : o ∈ frame.freeH ∪ frame.freeV) :
    o = i := by
  have hFin := P.strictForced c i hcS hF (hs c i)
  cases hFin with
  | seed hsd => exact absurd hsd (hs _ _)
  | @unit a b _ o' inside hR hx _ ho' hout hin _ =>
    by_cases hmem : o ∈ squareCorners a b
    · have hNF := FLatticePaper.Induction.strictInterior_nonfree frame (hR o hmem)
      have hzero : (0 : Site) ∈ frame.child.modifiedDeck.span :=
        ⟨0, 0, by ext <;> simp [FLatticePaper.Farey.PeriodDeck.combine]⟩
      exact (hNF 0 hzero (by rw [add_zero]; exact hfree)).elim
    · have hiff := square_one_input a b hx
      rcases ho with h1 | h1 <;> rcases ho' with h2 | h2
      · rw [h1, h2]
      · exfalso
        exact hmem (by rw [h1]; exact hiff.mpr (by rw [← h2]; exact hout))
      · exfalso
        exact hout (by rw [h2]; exact hiff.mpr (by rw [← h1]; exact hmem))
      · rw [h1, h2]

end FLatticePaper.FreeAdjacency
