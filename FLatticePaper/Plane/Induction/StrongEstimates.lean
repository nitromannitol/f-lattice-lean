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
policy and the drifts of the price and the slip on the generators. Not yet in this structure: the even-parity extension of the odd
zero strip (NO_ODD_SLIP_AUDIT §§2–4), whose frame (the odd conjugate's own coordinates) is not yet identified with `frameAt u`.
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

/-- The odd parent `N / D` of the current word whose conjugate is `u`, read from the child of `u`: `D − N` is the numerator and
`D + N` the denominator of the earlier child (the fix's `b` and `r`). -/
def parentN (u : Word) : ℤ := ((frameAt u).child.den - (frameAt u).child.num) / 2

/-- The denominator `D` of the odd parent of the current word whose conjugate is `u`, see `parentN`. -/
def parentD (u : Word) : ℤ := ((frameAt u).child.den + (frameAt u).child.num) / 2

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
  /-- The drifts of the primitive price on the generators `U` (kernel) and `V` (transverse) of the earlier child:
  `P(z + U) − P(z) = −1` and `P(z + V) − P(z) = 0` (checked numerically on the standard fields of the proper words of length
  at most three). -/
  priceDrift : ∀ z,
    (frameAt u).price (standardField u) (z + (frameAt u).child.modifiedDeck.kernel) -
        (frameAt u).price (standardField u) z = -1 ∧
      (frameAt u).price (standardField u) (z + (frameAt u).child.modifiedDeck.transverse) -
        (frameAt u).price (standardField u) z = 0
  /-- The drifts of the short slip `D_η` for `η = ±1`: `0` along `U` and `2η` along `V` (checked numerically as above). -/
  slipDrift : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∀ z,
    (frameAt u).slip (standardField u) η (z + (frameAt u).child.modifiedDeck.kernel) -
        (frameAt u).slip (standardField u) η z = 0 ∧
      (frameAt u).slip (standardField u) η (z + (frameAt u).child.modifiedDeck.transverse) -
        (frameAt u).slip (standardField u) η z = 2 * η
  /-- The zero strip of the quarter-turned earlier field in the parent transverse coordinate `t_p = N x₁ − D x₂`:
  `f = h₀ + F_u(Z ·) = quarterTurnField (standardField u)` vanishes for `1 − D ≤ t_p ≤ N + 2D − 1` (fix Q4-strips, the zero
  region). Checked numerically on the proper words of length at most three. -/
  zeroStripInterval : ∀ x : Site,
    1 - parentD u ≤ parentN u * x.1 - parentD u * x.2 →
      parentN u * x.1 - parentD u * x.2 ≤ parentN u + 2 * parentD u - 1 →
        quarterTurnField (standardField u) x = 0
  /-- The even-parity extension of the zero strip at `t_p = −D`: `f = 0` at the even sites with `t_p = −D` (fix Q4-strips,
  `f_even(−D) = 0`). Checked numerically on the proper words of length at most three. -/
  zeroEvenLine : ∀ x : Site, (x.1 + x.2) % 2 = 0 →
    parentN u * x.1 - parentD u * x.2 = -parentD u → quarterTurnField (standardField u) x = 0
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
  F2F3_policy : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∃ policy : Site → Site → Prop,
    RetainQuota (standardField u) policy ∧
      NonincreasingAlong ((frameAt u).chainPotential (standardField u) η) policy ∧
      ∀ a c : ℤ, 0 < a → 0 < c →
        RankWithIncrements policy (frameAt u).child.modifiedDeck.kernel (frameAt u).child.modifiedDeck.transverse
          (-a) (c * η)
  /-- F2 and F4 for the chain mate `h′_η = chainSheet η`, for each phase `η = ±1` (the sign of the chain step; `η = ε` is one
  of the two): a chain policy along which `h′_η` does not decrease; its reflection `ξ ↦ R′ − w′ − ξ` has a nondecreasing
  `Φ_η = chainPotential η`, the black and white quotas for `h′_η`, and for every pair of positive weights a rank with the opposite
  increments `λ(a, −cη)`. -/
  F2F4_chain : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∃ chainPolicy : Site → Site → Prop,
    NondecreasingAlong (fun z => (frameAt u).chainSheet (standardField u) η z) chainPolicy ∧
      ∃ R w : Site,
        NondecreasingAlong (fun z => (frameAt u).chainPotential (standardField u) η z)
            (ReflectedPolicy R w chainPolicy) ∧
          RetainQuota (fun z => (frameAt u).chainSheet (standardField u) η z)
            (ReflectedPolicy R w chainPolicy) ∧
          ∀ a c : ℤ, 0 < a → 0 < c →
            RankWithIncrements (ReflectedPolicy R w chainPolicy)
              (frameAt u).child.modifiedDeck.kernel (frameAt u).child.modifiedDeck.transverse
              a (-(c * η))

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
