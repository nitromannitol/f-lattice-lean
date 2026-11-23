import FLatticePaper.Plane.Induction.OldPolicy
import FLatticePaper.Plane.Induction.W1Constructor

/-! Task 72 (nonfree roots): the root condition of `nonfree_drop_excluded` from the W1 forcing of the earlier word.

A nonfree root is a strict-interior white (the W1 statement `W1Forced n d G` forces every strict-interior white by unseeded unit
propagation). Its retained edge is then the forced edge: `OldPolicyData.forcedWhiteUnique` says the only retained input at a white
with an unseeded forced edge `z → o` is `o`. So the root is black, or its retained edge is an unseeded forced edge. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- **The nonfree root condition.** For a retained edge `z → z'` of the old policy with `z` strict-interior, `W1Forced` gives the
unseeded forced edge at `z`, and the uniqueness of the retained input identifies it with `z'`. -/
theorem nonfree_root_forced {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : OldPolicyData frame G seed) {n d : ℤ} (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    (hW1 : FLatticePaper.W1.W1Forced n d G) {z z' : Site} (hSI : FLatticePaper.W1.StrictInterior n d z)
    (hr : P.retained z z') :
    laplacian G z = -1 ∨ FLatticePaper.SquareClauses.ForcedEdge G (fun _ _ => False) z z' := by
  rcases hbin z with hb | hw
  · exact Or.inl hb
  · right
    obtain ⟨o, ho⟩ := hW1 z hSI hw
    have hfo := FLatticePaper.W1.forcedEdgeIn_forced ho
    have e := P.forcedWhiteUnique z z' hr hw o hfo
    rw [e] at hfo
    exact hfo

end FLatticePaper.Induction
