import FLatticePaper.Plane.Induction.OldPolicy
import FLatticePaper.Plane.Induction.W1Constructor
import FLatticePaper.Plane.Induction.S3FreeBoundary

/-! Task 62 (2): the witness data of the earlier canonical policy, as a structure extending `OldPolicyData` (w3's file is not edited).

`OldPolicyWitness frame G seed η` adds to the policy the strict-interior witnesses of its forced whites: for every forced white `c`
with its forced input `i` (not a seed), the forcing of `(c, i)` is a derivation `ForcedEdgeIn` whose squares lie in the strict interior
of the earlier child (`StrictInterior`). This is the earlier W1 forcing (the induction hypothesis of §4: "the actual earlier unit
witness"), in the form that the child's aligned-collar squares use. `witnessSquare` extracts from such a derivation the unit square of
its first step, with its rejected input outside it and its other white corners forced into it. -/

namespace FLatticePaper.W1Witness

open Farey FLatticePaper FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.Induction FLatticePaper.W1

/-- The earlier canonical policy with its strict-interior witnesses and private squares at the forced whites. -/
structure OldPolicyWitness (frame : ChildFrame) (G : Field) (seed : Site → Site → Prop) (η : ℤ)
    extends OldPolicyData frame G seed η where
  /-- A forced non-seed white of the earlier field lying in the strict interior is forced by a derivation whose squares lie in the strict
  interior. Restricted to strict sites: a forced white outside the strict interior has no such derivation. -/
  strictForced : ∀ c i, StrictInterior frame.child.num frame.child.den c → ForcedEdge G seed c i → ¬ seed c i →
    ForcedEdgeIn G (StrictInterior frame.child.num frame.child.den) seed c i
  /-- The free-input fact (checked numerically on the unseeded forcing of the conjugate fields of words of length at most four, not
  proved): a forced white whose input `o` is a free white point (laplacian `0`) forces exactly that input. -/
  freeInputForced : ∀ c i o, ForcedEdge G seed c i → laplacian G c = 0 → (o = incomingNeg c ∨ o = incomingPos c) →
    o ∈ frame.freeH ∪ frame.freeV → laplacian G o = 0 → o = i
  /-- PRIVATE witness squares (the parent's W1 data, inherited; archive ALL_WHITE_THREE_STEP_RETURNS §A and AUDIT §1): the witness square
  of a forced non-seed white `c` contains `c`, and every other corner `c'` is joined to `c` by a chain of retained lattice edges, each
  step a retained input of the site before it (`c'` keeps … keeps `c`). The rejected input of `c` is the square corner `u` with
  `u → v → w → c`, so the ranks decrease from the corners to the root: `R c < R c'` (`W1Phase`). -/
  privateSquare : ∀ c i, ForcedEdge G seed c i → ¬ seed c i → laplacian G c = 0 →
    ∃ a b : ℤ, c ∈ squareCorners a b ∧
      ∀ c' ∈ squareCorners a b, c' ≠ c → Relation.TransGen (fun x y => retained x y ∧ Edge y x) c' c

/-- The first unit step of a derivation: a square containing `c` in `R`, its rejected input `o` outside it, and every other white
corner forced into it (by a derivation at its own pointer inside the square). -/
theorem witnessSquare {F : Field} {R : Site → Prop} {seed : Site → Site → Prop} {c o : Site}
    (h : ForcedEdgeIn F R seed c o) (hns : ¬ seed c o) :
    ∃ a b : ℤ, c ∈ squareCorners a b ∧ o ∉ squareCorners a b ∧ (∀ c' ∈ squareCorners a b, R c') ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = -1 ∨
        (laplacian F c' = 0 ∧ ∃ i', ForcedEdgeIn F R seed c' i' ∧ i' ∈ squareCorners a b)) := by
  cases h with
  | seed hs => exact absurd hs hns
  | @unit a b _ _ inside hR hc hw ho hout hin hforced =>
    refine ⟨a, b, hc, hout, hR, fun c' hc' hne => ?_⟩
    rcases hin c' hc' hne with h1 | ⟨h1, h2, _⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h1, inside c', hforced c' hc' hne h1, h2⟩

end FLatticePaper.W1Witness
