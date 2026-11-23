import FLatticePaper.Plane.Induction.StrongResidual
import FLatticePaper.Plane.Induction.SquareClauses

/-! Task 61, part 2: the one interface of the earlier canonical policy that the Q3 chain uses.

`OldPolicyData frame G seed` is the policy on the conjugate field `G` of the frame, with the seed of the forced edges. Its
fields are exactly the properties the Q3 argument uses (paragraphs 3, 6, 7 and the fix's external facts):

* `retained`, `quota`: the retained edges; a black centre retains both inputs, a white one at least one (`RetainQuota`).
  This is the retention of the chosen parent edge at a black or tied minimum.
* `priceNonincreasing`, `rawSlipNonincreasing`: the conjugate's price `P'` and raw slip `D'_η` do not increase (so `p = c₀ − P'(Z·)` does not
  decrease, task 63) and the raw slip `b` does not decrease along the retained edges.
* `chainNonincreasing`: the chain potential `Φ_η` does not increase along them (the chain gap monotonicity).
* `reflection`: reflection about `I = (1, −1)` maps retained edges to retained edges (`f(I − x) = f(x)`).
* `forcedRetained`: the forced-white edges (`ForcedEdge`) are retained.
* `westAtException`: the prescribed west input at the exceptional `V_p + I` when `W = 1`.

`Comparison with the strong residual` (below) lists which fields are already present in `StrongResidual` and
`StrongResidualReduced`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The reflection centre `I = (1, −1)` of the Q3 argument. -/
def reflectionI : Site := (1, -1)

/-- The earlier canonical policy on the conjugate field `G` of `frame`, with the forced seed `seed`. The functions `p`
and `b` are the primitive and the raw-slip quantities of paragraphs 5 and 7; they are data here. -/
structure OldPolicyData (frame : ChildFrame) (G : Field) (seed : Site → Site → Prop) where
  /-- The retained edges of the policy. -/
  retained : Site → Site → Prop
  /-- Quota: a black centre retains both inputs, a white centre at least one. -/
  quota : RetainQuota G retained
  /-- The conjugate's own primitive price `P' = frame.price G` (with the conjugate's `parentShift`) does not increase along
  the retained edges. By paragraph 5, `p(x) = c₀ − P'(Zx)` with `Z x = (−x₂, x₁ − 1)`, so this is `p` nondecreasing along
  the transported policy (task 63; the current frame's `parentShift` plays no role). -/
  priceNonincreasing : NonincreasingAlong (frame.price G) retained
  /-- The conjugate's raw slip `D'_η(y) = G y − G (y + η σ_c)` (`σ_c` the conjugate's short shift, `η = ±1`) does not
  increase along the retained edges. By paragraph 6 the raw slip `b` of the sheets is `(1 + ε) − D'_ε(Z ·)`, so `b` does not
  decrease along the retained edges (task 69 (b)). -/
  rawSlipNonincreasing : ∀ η : ℤ, (η = 1 ∨ η = -1) →
    NonincreasingAlong (fun y => G y - G (y + η • frame.shortShift)) retained
  /-- The chain potential `Φ_η` does not increase along the retained edges, for `η = ±1`. -/
  chainNonincreasing : ∀ η : ℤ, (η = 1 ∨ η = -1) → NonincreasingAlong (frame.chainPotential G η) retained
  /-- Reflection about `I` at the roots the Q3 argument uses (`nonfree_drop_excluded`): a retained edge from a black root (which keeps
  both inputs) or a forced-white edge, is carried to a retained edge. The reflection of the clause system carries both kinds of
  root to the same kind, so this is what the canonical construction provides from the quota, `forcedRetained` and the symmetry. -/
  reflection : ∀ c i, retained c i → (laplacian G c = -1 ∨ FLatticePaper.SquareClauses.ForcedEdge G seed c i) →
    retained (reflectionI - c) (reflectionI - i)
  /-- The forced-white edges are retained (they are unique at a forced white). -/
  forcedRetained : ∀ c i, FLatticePaper.SquareClauses.ForcedEdge G seed c i → retained c i
  /-- The prescribed west input at the exceptional vertex `V_p + I` when `W = 1` (`ε = +1`). -/
  westAtException : frame.eps = 1 →
    retained (frame.parents.odd.num - frame.parents.odd.den + 1, frame.parents.odd.den + frame.parents.odd.num - 1)
      (incomingNeg (frame.parents.odd.num - frame.parents.odd.den + 1, frame.parents.odd.den + frame.parents.odd.num - 1))

end FLatticePaper.Induction
