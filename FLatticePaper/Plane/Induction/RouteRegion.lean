import FLatticePaper.Plane.Induction.CanonForced
import FLatticePaper.Plane.Induction.RegionalCompat

/-! # The regional argument for a nonfree white route arrow (one generic statement)

A white `q` with a unit derivation `ForcedEdgeIn F R (fun _ _ => False) q o` inside a region `R` has its forced output `o`. Let `S` be
a region with a relation `K` (the region's chosen arrows) satisfying the hypotheses of `RegionalCompat.regional_forced`, with `S`
closed under the `K`-arrows that land in `R`. Then the forced output is a `K`-arrow from `q`, and the canonical policy keeps it
(`CanonForced.canon_of_forced`).

A route instance fixes `K` at its white sites to the route's next site, so the forced output is the next site. The derivation is
an input: `W1Forced` supplies it on the strict interior; the sites outside it need their own derivation. -/

namespace FLatticePaper.RouteRegion

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.RegionalCompat FLatticePaper.CanonForced
  FLatticePaper.SquareClauses

/-- **The regional argument, generic form.** A white `q` with a unit derivation `q → o` inside `R`, in a region `S` whose arrows
`K` satisfy the regional hypotheses, has the `K`-arrow `o`, which the canonical policy keeps. -/
theorem nonfree_policy_of_region {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    {R : Site → Prop} {S : Site → Prop} {K : Site → Site → Prop} {r : Site → ℤ}
    (hr : ∀ x u, K x u → r u < r x)
    (hS : ∀ x u, S x → K x u → R u → S u)
    (hblack : ∀ x, S x → laplacian G x = -1 → ∀ u, (u = incomingNeg x ∨ u = incomingPos x) → K x u)
    (hwhite : ∀ x, S x → laplacian G x = 0 → ∃ u, K x u ∧ (u = incomingNeg x ∨ u = incomingPos x))
    {q o : Site} (hqw : laplacian G q = 0) (hqS : S q)
    (hf : ForcedEdgeIn G R (fun _ _ => False) q o) :
    K q o ∧ C.policy q o :=
  ⟨regional_forced hr hS hblack hwhite hf hqS, canon_of_forced C hqw (forcedEdgeIn_forced hf)⟩

/-- **The strict-interior instance**: the derivation is `W1Forced`'s, inside `StrictInterior`. -/
theorem nonfree_policy_of_strict {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    {n d : ℤ} (hW1 : W1Forced n d G)
    {S : Site → Prop} {K : Site → Site → Prop} {r : Site → ℤ}
    (hr : ∀ x u, K x u → r u < r x)
    (hS : ∀ x u, S x → K x u → StrictInterior n d u → S u)
    (hblack : ∀ x, S x → laplacian G x = -1 → ∀ u, (u = incomingNeg x ∨ u = incomingPos x) → K x u)
    (hwhite : ∀ x, S x → laplacian G x = 0 → ∃ u, K x u ∧ (u = incomingNeg x ∨ u = incomingPos x))
    {q : Site} (hq : StrictInterior n d q) (hqw : laplacian G q = 0) (hqS : S q) :
    ∃ o, K q o ∧ C.policy q o := by
  obtain ⟨o, hf⟩ := hW1 q hq hqw
  exact ⟨o, (nonfree_policy_of_region C hr hS hblack hwhite hqw hqS hf).1,
    (nonfree_policy_of_region C hr hS hblack hwhite hqw hqS hf).2⟩

/-- **A route instance.** When the region's arrows at `q` are exactly the route's next site `nxt`, the canonical policy keeps `nxt`
at `q`. -/
theorem nonfree_next_of_region {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    {R : Site → Prop} {S : Site → Prop} {K : Site → Site → Prop} {r : Site → ℤ}
    (hr : ∀ x u, K x u → r u < r x)
    (hS : ∀ x u, S x → K x u → R u → S u)
    (hblack : ∀ x, S x → laplacian G x = -1 → ∀ u, (u = incomingNeg x ∨ u = incomingPos x) → K x u)
    (hwhite : ∀ x, S x → laplacian G x = 0 → ∃ u, K x u ∧ (u = incomingNeg x ∨ u = incomingPos x))
    {q nxt o : Site} (hqw : laplacian G q = 0) (hqS : S q)
    (hf : ForcedEdgeIn G R (fun _ _ => False) q o) (hK : ∀ u, K q u → u = nxt) :
    C.policy q nxt := by
  have hKo := (nonfree_policy_of_region C hr hS hblack hwhite hqw hqS hf).1
  have hpol := (nonfree_policy_of_region C hr hS hblack hwhite hqw hqS hf).2
  rw [hK o hKo] at hpol
  exact hpol

end FLatticePaper.RouteRegion
