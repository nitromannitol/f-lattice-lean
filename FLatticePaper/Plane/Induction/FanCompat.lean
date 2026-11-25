import FLatticePaper.Plane.Induction.SquareClauses
import FLatticePaper.Plane.Induction.FanAcyclic
import FLatticePaper.Plane.Induction.AndOrRank

/-! # Fan compatibility with the W1-forced whites (AUDIT_FREE_THREE_STEP_RETURNS §1, "Fan compatibility")

Let `G` be a directed graph on a vertex set `V` with: each black vertex has both inputs as successors; each white vertex has one successor,
an input; successors of vertices of `V` lie in `V`; and `G` lowers a rank strictly along its edges (the contact fan's rank, `FanAcyclic`).
Then every W1-forced white of `V` (a `ForcedEdge` at a vertex of `V`) is selected by `G` with the forced input. The proof is the audit's:
a conflicting selection starts a walk inside the forcing square, which by the induction hypothesis stays in `G` and must close, contradicting
the strictly decreasing rank. -/

namespace FLatticePaper.FanCompat

open FLatticePaper FLatticePaper.Induction FLatticePaper.AndOrRank

/-- Exactly one input of a corner of a unit square lies in the square. -/
theorem mem_squareCorners_iff (a b : ℤ) (p : Site) :
    p ∈ squareCorners a b ↔ (p.1 = a ∨ p.1 = a + 1) ∧ (p.2 = b ∨ p.2 = b + 1) := by
  obtain ⟨x, y⟩ := p
  unfold squareCorners
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

theorem square_one_input (a b : ℤ) {c : Site} (hc : c ∈ squareCorners a b) :
    (incomingNeg c ∈ squareCorners a b) ↔ ¬ (incomingPos c ∈ squareCorners a b) := by
  rw [mem_squareCorners_iff] at hc
  simp only [mem_squareCorners_iff]
  obtain ⟨x, y⟩ := c
  unfold incomingNeg incomingPos EvenSite at *
  by_cases hp : (x + y) % 2 = 0
  · rw [if_pos hp, if_pos hp]
    dsimp only at hc ⊢
    constructor <;> intro h <;> omega
  · rw [if_neg hp, if_neg hp]
    dsimp only at hc ⊢
    constructor <;> intro h <;> omega

end FLatticePaper.FanCompat
