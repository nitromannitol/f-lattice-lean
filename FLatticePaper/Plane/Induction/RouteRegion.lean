import FLatticePaper.Plane.Induction.CanonForced
import FLatticePaper.Plane.Induction.RegionalCompat
import FLatticePaper.Plane.Induction.ForcedArrows

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

/-- An input is never the site it feeds. -/
theorem input_ne (x u : Site) (hu : u = incomingNeg x ∨ u = incomingPos x) : u ≠ x := by
  intro h
  subst h
  rcases hu with hu | hu
  · unfold incomingNeg at hu
    split_ifs at hu <;> simp only [Prod.ext_iff] at hu <;> omega
  · unfold incomingPos at hu
    split_ifs at hu <;> simp only [Prod.ext_iff] at hu <;> omega

/-- **The port instance.** A white `q` whose route next `nxt` is an input, and whose translate `q + s` (with `s` even and the
deck equivariance `hT`) lies in the strict interior, while the translate of `nxt` does not: the region `{q + s}` with the single
arrow to `nxt + s` satisfies the regional hypotheses, so the canonical policy keeps `nxt` at `q`. -/
theorem route_port_arrow {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hW1 : W1Forced frame.child.num frame.child.den G)
    {q nxt s : Site} (hs : EvenSite s)
    (hT : ∀ x u, C.policy x u ↔ C.policy (x + s) (u + s))
    (hqw : laplacian G (q + s) = 0)
    (hqS : StrictInterior frame.child.num frame.child.den (q + s))
    (hin : nxt = incomingNeg q ∨ nxt = incomingPos q)
    (hport : ¬ StrictInterior frame.child.num frame.child.den (nxt + s)) :
    C.policy q nxt := by
  have hne : nxt ≠ q := input_ne q nxt hin
  have hne' : nxt + s ≠ q + s := fun h => hne (add_right_cancel h)
  have hin' : nxt + s = incomingNeg (q + s) ∨ nxt + s = incomingPos (q + s) := by
    rcases hin with h | h
    · left
      rw [FLatticePaper.ForcedArrows.incomingNeg_add_even hs, h]
    · right
      rw [FLatticePaper.ForcedArrows.incomingPos_add_even hs, h]
  obtain ⟨o, hf⟩ := hW1 (q + s) hqS hqw
  have hr : ∀ x u, (x = q + s ∧ u = nxt + s) →
      (if u = q + s then (1:ℤ) else 0) < (if x = q + s then (1:ℤ) else 0) := by
    rintro x u ⟨hx, hu⟩
    subst hx
    subst hu
    rw [if_neg hne', if_pos rfl]
    norm_num
  have hS : ∀ x u, (x = q + s) → (x = q + s ∧ u = nxt + s) → StrictInterior frame.child.num frame.child.den u →
      (u = q + s) := by
    intro x u _ hK hR
    exact absurd (hK.2 ▸ hR) hport
  have hblack : ∀ x, (x = q + s) → laplacian G x = -1 →
      ∀ u, (u = incomingNeg x ∨ u = incomingPos x) → (x = q + s ∧ u = nxt + s) := by
    intro x hx hl
    rw [hx, hqw] at hl
    norm_num at hl
  have hwhite : ∀ x, (x = q + s) → laplacian G x = 0 →
      ∃ u, (x = q + s ∧ u = nxt + s) ∧ (u = incomingNeg x ∨ u = incomingPos x) := by
    intro x hx _
    subst hx
    exact ⟨nxt + s, ⟨rfl, rfl⟩, hin'⟩
  have hpol : C.policy (q + s) (nxt + s) :=
    nonfree_next_of_region C (R := StrictInterior frame.child.num frame.child.den)
      (S := fun x => x = q + s) (K := fun x u => x = q + s ∧ u = nxt + s)
      (r := fun x => if x = q + s then (1:ℤ) else 0) (q := q + s) (nxt := nxt + s)
      hr hS hblack hwhite hqw rfl hf (fun u h => h.2)
  exact (hT q nxt).mpr hpol

end FLatticePaper.RouteRegion
