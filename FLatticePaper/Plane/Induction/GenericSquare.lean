import FLatticePaper.Plane.Induction.EndpointRows
import FLatticePaper.Plane.Induction.SignedPolicy

/-! # The generic square: a parent square from its three arrows, each discharged by the corner's class

A unit square at a white root `z` has the rejected input `q0` of `z` and the chain `q0 → q1 → q2 → z` of retained edges
(`ParentSquareOut`). Each corner of the chain gives its arrow by its class:

* black (`lap = −1`): the quota keeps both inputs (`RetainQuota`), so the arrow to the chain successor is automatic;
* white (`lap = 0`): the arrow is a hypothesis (the class supplies it): a free white corner by its prescription
  (`arrow_of_free`), a white non-free corner by its forced input, a translate of a free site by the deck transport of its
  prescription (`arrow_of_transport`).

`psq_of_arrows` is the generic square: from the square combinatorics, the rejected output `o` of `z`, and the white arrows, it gives
`ParentSquareOut`. The uniqueness of the white selections (`hwu`) gives the white clauses and the rejection of `q0` at `z`. -/

namespace FLatticePaper.GenericSquare

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.W1NonfreeOut
  FLatticePaper.EndpointRows

/-- **The generic parent square.** The black corners of the chain take their arrows from the quota; the white corners take the
arrows `A0`, `A1`, `A2` (supplied by their classes). The output `o` is the retained input of the white root `z`. -/
theorem psq_of_arrows {G : Field} {R : Site → Site → Prop} {z q0 q1 q2 o : Site} {a b : ℤ}
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    (hq : RetainQuota G R)
    (hwu : ∀ c j j', laplacian G c = 0 → R c j → R c j' → j = j')
    (hzw : laplacian G z = 0)
    (hz : z ∈ squareCorners a b) (h0 : q0 ∈ squareCorners a b) (h1 : q1 ∈ squareCorners a b)
    (h2 : q2 ∈ squareCorners a b)
    (hcov : ∀ c' ∈ squareCorners a b, c' ≠ z → c' = q0 ∨ c' = q1 ∨ c' = q2)
    (d01 : q0 ≠ q1) (d12 : q1 ≠ q2) (d02 : q0 ≠ q2)
    (hin0 : q0 = incomingNeg z ∨ q0 = incomingPos z)
    (e1 : Edge q1 q0) (e2 : Edge q2 q1) (e3 : Edge z q2)
    (A0 : laplacian G q0 = 0 → R q0 q1) (A1 : laplacian G q1 = 0 → R q1 q2) (A2 : laplacian G q2 = 0 → R q2 z)
    (hout : o = incomingNeg z ∨ o = incomingPos z) (hosq : o ∉ squareCorners a b) (ro : R z o) :
    ParentSquareOut G R z := by
  -- the arrows: black corners by the quota, white corners by their class
  have r01 : R q0 q1 := by
    rcases hbin q0 with hb | hb
    · rcases e1 with h | h
      · rw [h]; exact (hq.1 q0 hb).1
      · rw [h]; exact (hq.1 q0 hb).2
    · exact A0 hb
  have r12 : R q1 q2 := by
    rcases hbin q1 with hb | hb
    · rcases e2 with h | h
      · rw [h]; exact (hq.1 q1 hb).1
      · rw [h]; exact (hq.1 q1 hb).2
    · exact A1 hb
  have r20 : R q2 z := by
    rcases hbin q2 with hb | hb
    · rcases e3 with h | h
      · rw [h]; exact (hq.1 q2 hb).1
      · rw [h]; exact (hq.1 q2 hb).2
    · exact A2 hb
  -- the white clauses: the unique retained input is the successor
  have c0 : laplacian G q0 = -1 ∨ (laplacian G q0 = 0 ∧ ∀ j, R q0 j → j = q1) := by
    rcases hbin q0 with hb | hb
    · exact Or.inl hb
    · exact Or.inr ⟨hb, fun j hj => hwu q0 j q1 hb hj r01⟩
  have c1 : laplacian G q1 = -1 ∨ (laplacian G q1 = 0 ∧ ∀ j, R q1 j → j = q2) := by
    rcases hbin q1 with hb | hb
    · exact Or.inl hb
    · exact Or.inr ⟨hb, fun j hj => hwu q1 j q2 hb hj r12⟩
  have c2 : laplacian G q2 = -1 ∨ (laplacian G q2 = 0 ∧ ∀ j, R q2 j → j = z) := by
    rcases hbin q2 with hb | hb
    · exact Or.inl hb
    · exact Or.inr ⟨hb, fun j hj => hwu q2 j z hb hj r20⟩
  -- the root retains only `o`, so it rejects `q0`
  have huq : ∀ j, R z j → j = o := fun j hj => hwu z j o hzw hj ro
  have hn0 : ¬ R z q0 := by
    intro h
    have e : q0 = o := hwu z q0 o hzw h ro
    exact hosq (by rw [← e]; exact h0)
  exact parentSquareOut_of_square hz h0 h1 h2 hcov d01 d12 d02 hin0 hn0 e1 e2 e3 r01 r12 r20 hout hosq ro huq c0 c1 c2

/-- **The arrow of a free white corner on the H side is its prescription** (`PrescribedAt`, the class of a free H point). -/
theorem arrow_of_free_H {frame : ChildFrame} {G : Field} {R : Site → Site → Prop} {η : ℤ}
    (hpres : PrescribedAt frame G η R) {p : Site} (hp : p ∈ frame.freeH) (hl : laplacian G p = 0) :
    R p (p + frame.prescribedH η p) :=
  (hpres.1 p hp hl _).mpr rfl

/-- **The arrow of a free white corner on the V side is its prescription.** -/
theorem arrow_of_free_V {frame : ChildFrame} {G : Field} {R : Site → Site → Prop} {η : ℤ}
    (hpres : PrescribedAt frame G η R) {p : Site} (hp : p ∈ frame.freeV) (hl : laplacian G p = 0) :
    R p (p + frame.prescribedV η p) :=
  (hpres.2 p hp hl _).mpr rfl

/-- **The arrow of a white corner that is a deck translate of a free H point**: `w = f − c` for the deck vector `c`, and the
equivariance `hdeck` of the policy moves the free arrow `f → f + p` to `w → w + p`. -/
theorem arrow_of_transport {frame : ChildFrame} {R : Site → Site → Prop}
    (hdeck : ∀ (i j : ℤ) (z u : Site), R z u → R (z - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j))
    {f p : Site} {i j : ℤ} (hf : R f (f + p)) :
    R (f - frame.child.modifiedDeck.combine i j) (f - frame.child.modifiedDeck.combine i j + p) := by
  have h := hdeck i j f (f + p) hf
  have e : f + p - frame.child.modifiedDeck.combine i j = f - frame.child.modifiedDeck.combine i j + p := by abel
  rw [e] at h
  exact h

end FLatticePaper.GenericSquare
