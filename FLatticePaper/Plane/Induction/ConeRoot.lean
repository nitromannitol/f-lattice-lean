import FLatticePaper.Graph

/-! The cone of the fan (ALL_SLOPE_STEP, "Propagation"): the cone roots and the cone inputs from the start `b`.
Kept separate from the cap module so that the row lemmas (`FreeRows`) can use `ConeRoot` without the cap's imports. -/

namespace FLatticePaper.CapRay

open FLatticePaper

/-- A root of the fan cone from `b` (see the section comment). -/
def ConeRoot (b : Site) (K : ℕ) (x : Site) : Prop :=
  1 ≤ x.2 - b.2 ∧ x.2 - b.2 ≤ (K : ℤ) - 1 ∧
    (EvenSite x → x.1 - b.1 ≥ x.2 - b.2 - 1) ∧ (¬ EvenSite x → x.1 - b.1 ≥ x.2 - b.2)

/-- An input of the cone: height in `[0, K]`, `ℓ ≥ k − 1` on even sites, `ℓ ≥ k − 2` on odd sites. -/
def InCone (b : Site) (K : ℕ) (i : Site) : Prop :=
  0 ≤ i.2 - b.2 ∧ i.2 - b.2 ≤ (K : ℤ) ∧
    (EvenSite i → i.1 - b.1 ≥ i.2 - b.2 - 1) ∧ (¬ EvenSite i → i.1 - b.1 ≥ i.2 - b.2 - 2)


end FLatticePaper.CapRay
