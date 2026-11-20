import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Basic

/-! The physical F-lattice and its incoming Laplacian. -/

namespace FLatticePaper

abbrev Site := ℤ × ℤ

abbrev Field := Site → ℤ

/-- Incoming edges are horizontal at even sites and vertical at odd sites. -/
def EvenSite (x : Site) : Prop := (x.1 + x.2) % 2 = 0

instance (x : Site) : Decidable (EvenSite x) :=
  inferInstanceAs (Decidable ((x.1 + x.2) % 2 = 0))

def incomingNeg (x : Site) : Site :=
  if EvenSite x then (x.1 - 1, x.2) else (x.1, x.2 - 1)

def incomingPos (x : Site) : Site :=
  if EvenSite x then (x.1 + 1, x.2) else (x.1, x.2 + 1)

def Edge (y x : Site) : Prop := y = incomingNeg x ∨ y = incomingPos x

theorem incomingNeg_ne_incomingPos (x : Site) : incomingNeg x ≠ incomingPos x := by
  by_cases h : EvenSite x
  · intro heq
    simp only [incomingNeg, incomingPos, if_pos h, Prod.mk.injEq] at heq
    omega
  · intro heq
    simp only [incomingNeg, incomingPos, if_neg h, Prod.mk.injEq] at heq
    omega

/-- The signed sum over the two incoming edges, as in `eq:superharmonic`. -/
def laplacian (g : Field) (x : Site) : ℤ :=
  (g (incomingNeg x) - g x) + (g (incomingPos x) - g x)

def Superharmonic (g : Field) : Prop := ∀ x, laplacian g x ≤ 0

def incomingBoundary (X : Finset Site) : Set Site :=
  {y | y ∉ X ∧ ∃ x ∈ X, Edge y x}

/-- Indegree in the subgraph induced by `X`, as an integer. -/
def incomingDegree (X : Finset Site) (x : Site) : ℤ :=
  (if incomingNeg x ∈ X then 1 else 0) + (if incomingPos x ∈ X then 1 else 0)

/-- An induced subgraph is allowed if some vertex has enough chips for its indegree. -/
def Allowed (s : Field) (X : Finset Site) : Prop :=
  ∃ x ∈ X, incomingDegree X x ≤ s x

end FLatticePaper
