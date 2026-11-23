import FLatticePaper.Plane.Induction.WeightChange
import FLatticePaper.Plane.Induction.StrongEstimates

/-! Task 42, step 2: the policy field reduces to one strict rank and two monotone deck-affine functions.

The policy field of `StrongEstimates` asks for `RankWithIncrements policy kernel transverse (−a) (c η)` for every pair of positive
weights `a, c`. Here it is enough to have the case `a = c = 1` (one strict rank) and two deck-affine functions `P` (increments
`(−1, 0)`) and `J` (increments `(0, η)`) that do not increase along the retained steps. Then every pair of weights follows. -/

namespace FLatticePaper.Induction

open FLatticePaper

/-- **Every pair of weights from one strict rank.** Let `retained` be invariant under the deck `(U, V)` with nonzero determinant, and
let `P, J` be deck-affine with increments `(−1, 0)` and `(0, η)`, both nonincreasing along retained steps. If one strict rank with
increments `(−1, 1·η)` exists, then for all positive `a, b` the rank with increments `(−a, b η)` exists. -/
theorem rankWithIncrements_of_monotone {retained : Site → Site → Prop} {U V : Site}
    (hD : U.1 * V.2 - U.2 * V.1 ≠ 0)
    (hiffU : ∀ c i, retained c i ↔ retained (c + U) (i + U))
    (hiffV : ∀ c i, retained c i ↔ retained (c + V) (i + V))
    {η : ℤ} (hη : η = 1 ∨ η = -1) {P J : Site → ℤ}
    (hPU : ∀ z, P (z + U) = P z - 1) (hPV : ∀ z, P (z + V) = P z)
    (hJU : ∀ z, J (z + U) = J z) (hJV : ∀ z, J (z + V) = J z + η)
    (hmono : ∀ x y, retained x y → P y ≤ P x ∧ J y ≤ J x)
    (hrank : RankWithIncrements retained U V (-1) (1 * η))
    (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    RankWithIncrements retained U V (-a) (b * η) := by
  unfold RankWithIncrements at hrank
  obtain ⟨r0, lam0, hlam0, hstrict0, hU0, hV0⟩ := hrank
  have hr0U : ∀ z, r0 (z + U) = r0 z + (-lam0) := fun z => by
    have := hU0 z
    linarith
  have hr0V : ∀ z, r0 (z + V) = r0 z + η * lam0 := fun z => by
    have := hV0 z
    linarith
  have hdec : ∀ x y, retained x y → r0 y < r0 x := fun x y h => hstrict0 x y h
  obtain ⟨lam, hlam, rank, hstrict, hU, hV⟩ :=
    FLatticePaper.WeightChange.exists_rank_increments U V hD hiffU hiffV η hη P J r0 (-lam0) (η * lam0) hPU hPV hJU hJV hr0U hr0V hmono hdec a b ha hb
  exact ⟨rank, lam, hlam, hstrict, fun z => by linarith [hU z], fun z => by linarith [hV z]⟩

end FLatticePaper.Induction
