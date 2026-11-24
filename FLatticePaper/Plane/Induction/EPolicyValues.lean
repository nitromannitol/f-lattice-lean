import FLatticePaper.Plane.Induction.EPolicySquares
import FLatticePaper.Plane.Induction.CanonicalSigned

/-!
# The value inequalities of the signed policy e(-1, eta) on the reciprocal field (task 118, W1 base)

The canonical signed policies `ePolicy d η (laplacian F)` of the reciprocal field `F = reciprocalField k` satisfy every field of
`CanonicalSignedPolicy` except the value inequalities. This module assembles the canonical signed policies and the two signs
`CanonicalSignedGames (reciprocalFrame k) (reciprocalField k)` from the value inequalities, which are collected in the structure
`ReciprocalValues k`:

* `slip`: the signed short slip `D_η(z) = F z − F(z + ησ)` does not increase along the policy (`slipPermits`);
* `price`: the primitive price `P` does not increase along the policy;
* `rank`: a rank strictly decreasing along the policy, for each sign;
* `chain`: the chain potential `Φ_η = D_η + P(· + ησ)` does not increase along the policy.

The rounded slip `J_η = ⌈D_η/2⌉` does not increase along the policy: it follows from `slip`.
-/

namespace FLatticePaper.EPolicy

open FLatticePaper FLatticePaper.Induction

/-- The value inequalities of the signed policy e(-1, eta) on the reciprocal field `reciprocalField k` (the items 4 and the
strict rank of the note): the raw slip and the price do not increase along the policy, the chain potential does not increase
along the policy, and a strict rank decreases along it. -/
structure ReciprocalValues (k : ℕ) : Prop where
  slip : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∀ c i,
    ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) c i →
      slipPermits (reciprocalField k) (fun z => reciprocalField k (z + η • (reciprocalFrame k).shortShift)) c i
  price : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∀ c i,
    ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) c i →
      (reciprocalFrame k).price (reciprocalField k) i ≤ (reciprocalFrame k).price (reciprocalField k) c
  rank : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∃ R : Site → ℤ, ∀ c i,
    ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) c i → R i < R c
  chain : ∀ η : ℤ, (η = 1 ∨ η = -1) →
    NonincreasingAlong ((reciprocalFrame k).chainPotential (reciprocalField k) η)
      (ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)))

/-- The rounded slip does not increase along the policy: `J_η = ⌈D_η/2⌉` is monotone in `D_η`. -/
theorem roundedSlip_nonincreasing_of_slip (k : ℕ) (V : ReciprocalValues k) (η : ℤ) (hη : η = 1 ∨ η = -1) (c i : Site)
    (h : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) c i) :
    (reciprocalFrame k).cutGrade (reciprocalField k) 0 1 η i ≤ (reciprocalFrame k).cutGrade (reciprocalField k) 0 1 η c := by
  have hs := V.slip η hη c i h
  unfold slipPermits slipIncrement at hs
  unfold ChildFrame.cutGrade ChildFrame.roundedSlip ChildFrame.slip at *
  dsimp only at hs
  simp only [zero_mul, zero_add, one_mul]
  omega

/-- The canonical signed policy of the sign `η` on the reciprocal field, from the value hypotheses `V`: every field of
`CanonicalSignedPolicy` is the lemma of the e-policy (quota, selection, squares, prescription, free set), except the value
inequalities, which are the fields of `V`. -/
noncomputable def canonicalSignedPolicy_reciprocal (k : ℕ) (V : ReciprocalValues k) (η : ℤ) (hη : η = 1 ∨ η = -1) :
    CanonicalSignedPolicy (reciprocalFrame k) (reciprocalField k) η where
  policy := ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k))
  free := FreeGlobal (2 * (k : ℤ) + 3)
  freeInvariant := by
    intro step hstep site
    rw [reciprocalFrame_child] at hstep
    exact freeGlobal_add_span (by omega) step hstep site
  quota := retainQuota_e k η hη
  permitted := V.slip η hη
  nonincreasingP := fun c i h => by
    rw [cutGrade_one_zero_one, cutGrade_one_zero_one]
    exact V.price η hη c i h
  nonincreasingJ := fun c i h => roundedSlip_nonincreasing_of_slip k V η hη c i h
  rank := Classical.choose (V.rank η hη)
  strictRank := fun c i h _ _ => Classical.choose_spec (V.rank η hη) c i h
  freePrescribed := fun c _ hw => freePrescribed_e k η hη c hw
  sel := selF k η
  sel_input := fun c _ => selF_input k η hη c
  white_policy := fun c hc i => ePolicy_iff_sel k η hη c i hc
  squares := squares_reciprocal k η hη
  prescribed := prescribedAt_reciprocal k η hη
  policyEdge := fun c i h => ePolicy_edge (by omega) (stairEven_valid_reciprocal k) η _ c i h
  westAtException := fun h => absurd h (by rw [reciprocal_eps]; norm_num)

/-- **The canonical signed games of the reciprocal field**, assembled from the value hypotheses `V`: the two signs
`game η` (`η = ±1`) and the chain claim `chainNonincreasing` (the value field `V.chain`). -/
noncomputable def canonicalSignedGames_reciprocal (k : ℕ) (V : ReciprocalValues k) :
    CanonicalSignedGames (reciprocalFrame k) (reciprocalField k) where
  game := fun η hη => canonicalSignedPolicy_reciprocal k V η hη
  chainNonincreasing := fun η hη => V.chain η hη

/-- The unit increment of a field along `e` at `z`. -/
def incr (F : Site → ℤ) (e z : Site) : ℤ := F (z + e) - F z

/-- The odd parent of the reciprocal frame is `0/1`. -/
theorem reciprocalFrame_odd (k : ℕ) : (reciprocalFrame k).parents.odd = ⟨0, 1⟩ := by
  show (FLatticePaper.Farey.parentsAt (List.replicate k FLatticePaper.Farey.Digit.three)).odd = _
  rw [FLatticePaper.Tiles.parentsAt_replicate_three]

/-- The short shift of the reciprocal frame is `(-2, 0)`. -/
theorem reciprocalFrame_shortShift (k : ℕ) : (reciprocalFrame k).shortShift = (-2, 0) := by
  unfold ChildFrame.shortShift
  rw [reciprocalFrame_odd, reciprocal_eps]
  ext <;> simp

/-- The parent shift of the reciprocal frame is `(1, -1)`. -/
theorem reciprocalFrame_parentShift (k : ℕ) : (reciprocalFrame k).parentShift = (1, -1) := by
  unfold ChildFrame.parentShift
  rw [reciprocalFrame_odd, reciprocal_eps]
  ext <;> simp

/-- The parent slope of the reciprocal frame is `-z₂`. -/
theorem reciprocalFrame_parentSlope (k : ℕ) (z : Site) : (reciprocalFrame k).parentSlope z = -z.2 := by
  unfold ChildFrame.parentSlope
  rw [reciprocalFrame_odd]
  simp

/-- The price of the reciprocal frame: `P(z) = F z − F(z − (1, −1)) − z₂`. -/
theorem price_reciprocal (k : ℕ) (F : Site → ℤ) (z : Site) :
    (reciprocalFrame k).price F z = F z - F (z - (1, -1)) - z.2 := by
  unfold ChildFrame.price
  rw [reciprocalFrame_parentShift, reciprocal_eps, reciprocalFrame_parentSlope]
  ring

/-- **The slip along an edge.** For `i = c + e`: `D(i) − D(c) = Δ_e(c) − Δ_e(c + ησ)`. -/
theorem slip_edge_sub (F : Site → ℤ) (fr : ChildFrame) (η : ℤ) (c e : Site) :
    (fr.slip F η (c + e) - fr.slip F η c) = incr F e c - incr F e (c + η • fr.shortShift) := by
  unfold ChildFrame.slip incr
  have h : c + e + η • fr.shortShift = c + η • fr.shortShift + e := by abel
  rw [h]
  ring

/-- If the increment does not grow along the shift, the slip does not increase along the edge. -/
theorem slip_edge_le (F : Site → ℤ) (fr : ChildFrame) (η : ℤ) (c e : Site)
    (h : incr F e c ≤ incr F e (c + η • fr.shortShift)) :
    fr.slip F η (c + e) ≤ fr.slip F η c := by
  have := slip_edge_sub F fr η c e
  linarith

/-- **The price along an edge of the reciprocal frame.** For `i = c + e`: `P(i) − P(c) = Δ_e(c) − Δ_e(c − (1, −1)) − e₂`. -/
theorem price_edge_sub (k : ℕ) (F : Site → ℤ) (c e : Site) :
    ((reciprocalFrame k).price F (c + e) - (reciprocalFrame k).price F c) =
      incr F e c - incr F e (c - (1, -1)) - e.2 := by
  rw [price_reciprocal, price_reciprocal]
  unfold incr
  have h : c + e - (1, -1) = c - (1, -1) + e := by abel
  rw [h]
  simp only [Prod.snd_add]
  ring

/-- If the increment satisfies the price inequality along the edge, the price does not increase along the edge. -/
theorem price_edge_le (k : ℕ) (F : Site → ℤ) (c e : Site)
    (h : incr F e c - incr F e (c - (1, -1)) ≤ e.2) :
    (reciprocalFrame k).price F (c + e) ≤ (reciprocalFrame k).price F c := by
  have := price_edge_sub k F c e
  linarith

/-- **The chain potential along an edge of the reciprocal frame.** For `i = c + e`:
`Φ(i) − Φ(c) = Δ_e(c) − Δ_e(c + ησ − (1, −1)) − e₂`. -/
theorem chain_edge_sub (k : ℕ) (F : Site → ℤ) (η : ℤ) (c e : Site) :
    ((reciprocalFrame k).chainPotential F η (c + e) - (reciprocalFrame k).chainPotential F η c) =
      incr F e c - incr F e (c + η • (reciprocalFrame k).shortShift - (1, -1)) - e.2 := by
  have hs := slip_edge_sub F (reciprocalFrame k) η c e
  have hp := price_edge_sub k F (c + η • (reciprocalFrame k).shortShift) e
  have h1 : c + e + η • (reciprocalFrame k).shortShift = (c + η • (reciprocalFrame k).shortShift) + e := by abel
  unfold ChildFrame.chainPotential
  rw [h1]
  linarith

/-- If the increment satisfies the chain inequality along the edge, the chain potential does not increase along it. -/
theorem chain_edge_le (k : ℕ) (F : Site → ℤ) (η : ℤ) (c e : Site)
    (h : incr F e c - incr F e (c + η • (reciprocalFrame k).shortShift - (1, -1)) ≤ e.2) :
    (reciprocalFrame k).chainPotential F η (c + e) ≤ (reciprocalFrame k).chainPotential F η c := by
  have := chain_edge_sub k F η c e
  linarith

end FLatticePaper.EPolicy
