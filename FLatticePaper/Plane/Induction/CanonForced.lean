import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.SquareClauses
import FLatticePaper.Plane.Induction.W1Witness

/-! # The canonical white rule `hcanon` from a unit derivation (the reduction of the region argument)

The canonical policy `C` selects one input at each white and satisfies every unit square clause (`C.sel_input`, `C.squares`,
`C.white_policy`). By `SquareClauses.forced_sound`, every forced edge of unit propagation (`ForcedEdge`, with the empty seed) is the
selection `C.sel`. Hence the canonical rule `W.retained X1 X2` at a white `X1` with black `X2` follows from the unit derivation
`ForcedEdge G (fun _ _ => False) X1 X2` alone. The region argument of the even-V square is therefore the existence of this derivation,
which the chain of unit squares supplies at each root. -/

namespace FLatticePaper.CanonForced

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses

/-- **A unit derivation is the canonical selection.** A forced edge of the empty seed at a white `c` is an arrow of the canonical
policy. -/
theorem canon_of_forced {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η) {c o : Site}
    (hc : laplacian G c = 0) (h : ForcedEdge G (fun _ _ => False) c o) : C.policy c o := by
  have hsel : C.sel c = o :=
    forced_sound G (fun _ _ => False) C.sel C.sel_input (fun c' i h' => h'.elim) C.squares c o h
  exact (C.white_policy c hc o).mpr hsel.symm

/-- **The canonical white rule for a witness**, from the unit derivation. -/
theorem canon_of_forced_W {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (C : CanonicalSignedPolicy frame G η) (W : FLatticePaper.W1Witness.OldPolicyWitness frame G seed η) (hW : W.retained = C.policy)
    {c o : Site} (hc : laplacian G c = 0) (h : ForcedEdge G (fun _ _ => False) c o) : W.retained c o := by
  rw [hW]
  exact canon_of_forced C hc h

/-- **`hcanon` of the even V square, from the unit derivations at the even roots.** The named input `hderiv` is the unit derivation
`X1 → X2` at each even free white V root; with it the canonical rule holds at every such root. -/
theorem hcanon_of_deriv {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η δ : ℤ}
    (C : CanonicalSignedPolicy frame G η) (W : FLatticePaper.W1Witness.OldPolicyWitness frame G seed η) (hW : W.retained = C.policy)
    (hderiv : ∀ z ∈ frame.freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      (η = -1 ∨ z ≠ frame.vLast) → laplacian G z = 0 →
      ForcedEdge G (fun _ _ => False) (z.1 + δ, z.2) (z.1 + δ, z.2 - δ)) :
    ∀ z ∈ frame.freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      (η = -1 ∨ z ≠ frame.vLast) → laplacian G z = 0 →
      laplacian G (z.1 + δ, z.2) = 0 → laplacian G (z.1 + δ, z.2 - δ) = -1 →
      W.retained (z.1 + δ, z.2) (z.1 + δ, z.2 - δ) := by
  intro z hz hev hF hsc hw h1 _
  exact canon_of_forced_W C W hW h1 (hderiv z hz hev hF hsc hw)

end FLatticePaper.CanonForced
