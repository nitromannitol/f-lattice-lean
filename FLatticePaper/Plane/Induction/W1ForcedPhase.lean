import FLatticePaper.Plane.Induction.W1Phase
import FLatticePaper.Plane.Induction.W1Constructor
import FLatticePaper.Plane.Induction.W1Pointers

/-! # Task 88: W1Forced from the return structure (the lead's (3))

`W1Forced n d F`: every strict-interior white is forced by unit propagation from no seeds, inside the strict interior. The forcing lemma
`forcing_of_phase_policy` gives this from three things: a finite strict interior, the pointer `out c` of each strict white (an input, by the
definition of `pointerOf`), and the strict-interior square data of each strict white. With the trivial phase `ψ ≡ 0` (every site a tie) the
phase conditions reduce to the single retained relation `R` with the strictly decreasing rank `RR`.

`w1Forced_of_strict_squares` is the assembly. The square data `hsq` (a unit square in the strict interior, with the pointer of `c` outside
it, every other corner black or with its pointer inside, and the white corners retained-connected to `c`) and the finiteness `hfin` are the
named inputs. -/

namespace FLatticePaper.W1ForcedPhase

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.W1 FLatticePaper.W1Phase

/-- The pointer of a relation is an input of its centre. -/
theorem pointerOf_input (Q : Site → Site → Prop) (c : Site) :
    FLatticePaper.W1Pointers.pointerOf Q c = incomingNeg c ∨ FLatticePaper.W1Pointers.pointerOf Q c = incomingPos c := by
  unfold FLatticePaper.W1Pointers.pointerOf
  classical
  split_ifs <;> simp

/-- **W1Forced from the return structure** (task 88). -/
theorem w1Forced_of_strict_squares (n d : ℤ) (F : Field) (R : Site → Site → Prop) (RR : Site → ℤ)
    (hR : ∀ c i, R c i → RR i < RR c)
    (hfin : {c : Site | StrictInterior n d c}.Finite)
    (hsq : ∀ c, StrictInterior n d c → laplacian F c = 0 → ∃ a b : ℤ,
      c ∈ squareCorners a b ∧ (∀ c' ∈ squareCorners a b, StrictInterior n d c') ∧
      FLatticePaper.W1Pointers.pointerOf R c ∉ squareCorners a b ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = -1 ∨
        (laplacian F c' = 0 ∧ FLatticePaper.W1Pointers.pointerOf R c' ∈ squareCorners a b)) ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = 0 → Relation.TransGen R c' c)) :
    W1Forced n d F := by
  intro z hz hw
  refine ⟨FLatticePaper.W1Pointers.pointerOf R z, ?_⟩
  refine forcing_of_phase_policy n d F (fun c => FLatticePaper.W1Pointers.pointerOf R c) (fun _ => (0 : ℤ)) R R RR RR
    (fun c i h => hR c i h) (fun c i h => hR c i h) hfin ?_ ?_ z hz hw
  · intro c _ _
    exact pointerOf_input R c
  · intro c hc hw'
    obtain ⟨a, b, h1, h2, h3, h4, h5⟩ := hsq c hc hw'
    refine ⟨a, b, h1, h2, h3, fun c' hc' hne => ?_, fun c' hc' hne hw'' => ?_⟩
    · rcases h4 c' hc' hne with hb | ⟨hw0, hpin⟩
      · exact Or.inl hb
      · exact Or.inr ⟨hw0, hpin, pointerOf_input R c'⟩
    · have hph : phasePolicy (fun _ => (0 : ℤ)) R R c = R := by
        simp [phasePolicy]
      refine ⟨⟨fun _ => rfl, fun h => absurd rfl h⟩, ?_⟩
      rw [hph]
      exact h5 c' hc' hne hw''

/-- **W1Forced for a ranked policy** (task 88): the policy `P` (its retained relation with its strictly decreasing rank) gives `W1Forced`,
given the finiteness and the strict-interior square data of `P.retained`. -/
theorem w1Forced_of_ranked {η : ℤ} {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : OldPolicyRanked frame G seed η)
    (hfin : {c : Site | StrictInterior frame.child.num frame.child.den c}.Finite)
    (hsq : ∀ c, StrictInterior frame.child.num frame.child.den c → laplacian G c = 0 → ∃ a b : ℤ,
      c ∈ squareCorners a b ∧ (∀ c' ∈ squareCorners a b, StrictInterior frame.child.num frame.child.den c') ∧
      FLatticePaper.W1Pointers.pointerOf P.retained c ∉ squareCorners a b ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian G c' = -1 ∨
        (laplacian G c' = 0 ∧ FLatticePaper.W1Pointers.pointerOf P.retained c' ∈ squareCorners a b)) ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian G c' = 0 → Relation.TransGen P.retained c' c)) :
    W1Forced frame.child.num frame.child.den G :=
  w1Forced_of_strict_squares frame.child.num frame.child.den G P.retained P.rank
    (fun c i h => P.rank_decr c i h) hfin hsq

end FLatticePaper.W1ForcedPhase
