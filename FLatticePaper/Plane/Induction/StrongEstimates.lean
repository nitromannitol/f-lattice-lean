import FLatticePaper.Plane.Induction.Potentials
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.AlternateMidpoint
import FLatticePaper.Plane.Induction.SignedPolicy

/-! # The strong estimates of a standard field (task 49, step 0)

The induction of the I1 and I2 comparisons (fixes/Q4-strips.md) uses, at the strictly earlier word `u` (the swapped birth prefix),
the packet of its standard field together with the two price ranges, the short-slip range, and the unit increments and no-cross
stars of the slip and of the primitive price. This file states these as one structure `StrongEstimates u`, with the notions taken
from `Potentials.lean` (`slip`, `price`, `cutPrice`, `shortShift`) and `AlternateMidpoint.lean` (`HasUnitSlip`, `NoEvenSlipSaddle`).

The signed-policy notions (quotas, monotonicity along retained edges, reflected policies) are those of `SignedPolicy.lean`
(task 38, w1). F2 and F3 are the policy of the standard field and its weighted ranks; F2 and F4 are the chain mate and its reflected
policy. Not yet in this structure: the drifts of the price ranges and the even-parity extension of the odd zero strip
(NO_ODD_SLIP_AUDIT §§2–4), which need their statements read from the audit.
-/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The primitive price increment over an input edge: `P(input) − P(center)`. -/
def priceIncrement (frame : ChildFrame) (F : Field) (center input : Site) : ℤ :=
  frame.price F input - frame.price F center

/-- F1 for the primitive price: its increments over the edges are in `{−1, 0, 1}`. -/
def HasUnitPrice (frame : ChildFrame) (F : Field) : Prop :=
  ∀ center input, Edge input center →
    -1 ≤ priceIncrement frame F center input ∧ priceIncrement frame F center input ≤ 1

/-- F1 for the primitive price, no-cross stars: at a star the two input increments are not opposite nonzero steps. -/
def NoPriceSaddle (frame : ChildFrame) (F : Field) : Prop :=
  ∀ site,
    let neg := priceIncrement frame F site (incomingNeg site)
    let pos := priceIncrement frame F site (incomingPos site)
    ¬ ((neg = -1 ∧ pos = 1) ∨ (neg = 1 ∧ pos = -1))

/-- A rank that strictly decreases along the retained edges, and whose increments on the generators `U`, `V` are a positive
integer multiple `λ` of `(p, q)`. -/
def RankWithIncrements (retained : Site → Site → Prop) (U V : Site) (p q : ℤ) : Prop :=
  ∃ rank : Site → ℤ, ∃ lam : ℤ, 0 < lam ∧ (∀ x i, retained x i → rank i < rank x) ∧
    (∀ z, rank (z + U) - rank z = p * lam) ∧ (∀ z, rank (z + V) - rank z = q * lam)

/-- The strong estimates of the standard field of a word `u`, the earlier word of an induction step. -/
structure StrongEstimates (u : Word) : Prop where
  /-- The packet of the standard field: periods, strips, reflection, binarity. -/
  packet : (frameAt u).Packet (standardField u)
  /-- The short-slip range `0 ≤ D_1 ≤ 2` on the closed polygon, with `D_η(z) = F(z) − F(z + ησ)`. -/
  slipRange : ∀ z ∈ (frameAt u).closedPolygon,
    0 ≤ (frameAt u).slip (standardField u) 1 z ∧ (frameAt u).slip (standardField u) 1 z ≤ 2
  /-- The primitive-price range `c_0 − 1 ≤ P ≤ c_0` on the closed polygon, with `c_0 = cutPrice`. -/
  priceRange : ∀ z ∈ (frameAt u).closedPolygon,
    (frameAt u).cutPrice - 1 ≤ (frameAt u).price (standardField u) z ∧
      (frameAt u).price (standardField u) z ≤ (frameAt u).cutPrice
  /-- F1, the slip: unit increments of `F` against its σ-translate on every edge. -/
  F1_unitSlip : HasUnitSlip (standardField u) (fun z => standardField u (z + (frameAt u).shortShift))
  /-- F1, the slip: no-cross stars. -/
  F1_noSlipSaddle : NoEvenSlipSaddle (standardField u) (fun z => standardField u (z + (frameAt u).shortShift))
  /-- F1, the primitive price: unit increments on every edge. -/
  F1_unitPrice : HasUnitPrice (frameAt u) (standardField u)
  /-- F1, the primitive price: no opposite nonzero increments at a star (no-cross primitive stars). -/
  F1_noPriceSaddle : NoPriceSaddle (frameAt u) (standardField u)
  /-- F2 and F3 for the standard field: a signed policy that is a quota policy, along whose retained edges the field does not
  increase, and for every pair of positive weights `(a, c)` a rank with increments `λ(−a, cη)` on the generators `U′`, `V′`
  (`U′`, `V′` the kernel and the transverse period of the earlier child, `η = ε`). -/
  F2F3_policy : ∃ policy : Site → Site → Prop,
    RetainQuota (standardField u) policy ∧ NonincreasingAlong (standardField u) policy ∧
      ∀ a c : ℤ, 0 < a → 0 < c →
        RankWithIncrements policy (frameAt u).child.modifiedDeck.kernel (frameAt u).child.modifiedDeck.transverse
          (-a) (c * (frameAt u).eps)
  /-- F2 and F4 for the chain mate `h′ = chainSheet ε`: a chain policy along which `h′` does not decrease; its reflection
  `ξ ↦ R′ − w′ − ξ` has a nondecreasing `Φ = F′ − h′`, the black and white quotas for `h′`, and for every pair of positive weights
  a rank with the opposite increments `λ(a, −cη)`. -/
  F2F4_chain : ∃ chainPolicy : Site → Site → Prop,
    NondecreasingAlong (fun z => (frameAt u).chainSheet (standardField u) (frameAt u).eps z) chainPolicy ∧
      ∃ R w : Site,
        NondecreasingAlong (fun z => (frameAt u).chainPotential (standardField u) (frameAt u).eps z)
            (ReflectedPolicy R w chainPolicy) ∧
          RetainQuota (fun z => (frameAt u).chainSheet (standardField u) (frameAt u).eps z)
            (ReflectedPolicy R w chainPolicy) ∧
          ∀ a c : ℤ, 0 < a → 0 < c →
            RankWithIncrements (ReflectedPolicy R w chainPolicy)
              (frameAt u).child.modifiedDeck.kernel (frameAt u).child.modifiedDeck.transverse
              a (-(c * (frameAt u).eps))

namespace StrongEstimates

variable {u : Word}

/-- The short-slip range, from the structure. -/
theorem slip_mem_range (h : StrongEstimates u) {z : Site} (hz : z ∈ (frameAt u).closedPolygon) :
    0 ≤ (frameAt u).slip (standardField u) 1 z ∧ (frameAt u).slip (standardField u) 1 z ≤ 2 :=
  h.slipRange z hz

/-- The primitive-price range, from the structure. -/
theorem price_mem_range (h : StrongEstimates u) {z : Site} (hz : z ∈ (frameAt u).closedPolygon) :
    (frameAt u).cutPrice - 1 ≤ (frameAt u).price (standardField u) z ∧
      (frameAt u).price (standardField u) z ≤ (frameAt u).cutPrice :=
  h.priceRange z hz

end StrongEstimates

end FLatticePaper.Induction
