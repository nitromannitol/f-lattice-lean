import FLatticePaper.Plane.Induction.EPolicySquares
import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.ReciprocalIncrements
import FLatticePaper.Plane.Induction.PureBasePrice

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
open FLatticePaper.Construction
open FLatticePaper.PureRank

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

/-- The raw increment: for raw `p` and `p + e` the increment of the reciprocal field is the stair difference. -/
theorem incr_raw_stair (k : ℕ) (e p : Site)
    (hp : p ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites)
    (hpe : p + e ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites) :
    incr (reciprocalField k) e p =
      BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (p + e) - BaseMask.stairEvenValue (2 * (k : ℤ) + 3) p := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have h := reciprocal_native_step k (z := p) (y := p) (e := e) (i := 0) (j := 0) hp hpe
    (by simp [combine_mk_one hd])
  unfold incr
  rw [h]
  ring

/-- The horizontal stair increment on row `y` at column `x` with step `s`. -/
def hG (d x y s : ℤ) : ℤ :=
  (min (x + s - 1) 0 - min (x - 1) 0) +
    ((if BaseMask.StairEvenCorner d (x + s, y) then 1 else 0) - (if BaseMask.StairEvenCorner d (x, y) then 1 else 0))

theorem stair_step_eq_hG (d x y s : ℤ) :
    BaseMask.stairEvenValue d (x + s, y) - BaseMask.stairEvenValue d (x, y) = hG d x y s := by
  unfold hG BaseMask.stairEvenValue
  dsimp only
  ring

/-- The stair corner indicator vanishes away from the two corners `(0, 0)` and `(2, d + 1)`. -/
theorem stair_corner_zero (d a b : ℤ) (h : ¬ ((a = 0 ∧ b = 0) ∨ (a = 2 ∧ b = d + 1))) :
    (if BaseMask.StairEvenCorner d (a, b) then (1 : ℤ) else 0) = 0 := by
  rw [if_neg]
  exact fun hc => h hc

/-- **Horizontal slip, interior.** On the interior box (all shifted sites raw and off the corners), the retained horizontal step does not increase the slip: `D(i) ≤ D(c)`. -/
theorem horiz_D_ineq (d η x y s : ℤ) (hd : d % 2 = 1) (hbox : 5 - d ≤ x ∧ x ≤ d - 3 ∧ 1 ≤ y ∧ y ≤ d - 1 ∧ 3 ≤ x + y ∧ x + y ≤ d)
    (hpar : (x + y) % 2 = 0) (hret : x = 1 ∨ (s, 0) = selDisp d η (x, y)) :
    hG d x y s ≤ hG d (x - 2 * η) y s := by
  unfold hG
  rw [stair_corner_zero d (x + s) (y) (by omega)]
  rw [stair_corner_zero d (x) (y) (by omega)]
  rw [stair_corner_zero d (x - 2 * η + s) (y) (by omega)]
  rw [stair_corner_zero d (x - 2 * η) (y) (by omega)]
  rcases hret with h1 | h1
  · subst h1
    omega
  · have hE : EvenSite (x, y) := by unfold EvenSite; dsimp only; omega
    unfold selDisp at h1
    rw [if_pos hE] at h1
    split_ifs at h1 <;> (try simp only [Prod.mk.injEq] at *) <;> omega

/-- **Horizontal price, interior.** The retained horizontal step does not increase the price, the shift `(-1, 1)`. -/
theorem horiz_P_ineq (d η x y s : ℤ) (hd : d % 2 = 1) (hbox : 5 - d ≤ x ∧ x ≤ d - 3 ∧ 1 ≤ y ∧ y ≤ d - 1 ∧ 3 ≤ x + y ∧ x + y ≤ d)
    (hpar : (x + y) % 2 = 0) (hret : x = 1 ∨ (s, 0) = selDisp d η (x, y)) :
    hG d x y s ≤ hG d (x - 1) (y + 1) s := by
  unfold hG
  rw [stair_corner_zero d (x + s) (y) (by omega)]
  rw [stair_corner_zero d (x) (y) (by omega)]
  rw [stair_corner_zero d (x - 1 + s) (y + 1) (by omega)]
  rw [stair_corner_zero d (x - 1) (y + 1) (by omega)]
  rcases hret with h1 | h1
  · subst h1
    omega
  · have hE : EvenSite (x, y) := by unfold EvenSite; dsimp only; omega
    unfold selDisp at h1
    rw [if_pos hE] at h1
    split_ifs at h1 <;> (try simp only [Prod.mk.injEq] at *) <;> omega

/-- **Horizontal chain, interior.** The retained horizontal step does not increase the chain potential, the shift `(-2η - 1, 1)`. -/
theorem horiz_Phi_ineq (d η x y s : ℤ) (hd : d % 2 = 1) (hbox : 5 - d ≤ x ∧ x ≤ d - 3 ∧ 1 ≤ y ∧ y ≤ d - 1 ∧ 3 ≤ x + y ∧ x + y ≤ d)
    (hpar : (x + y) % 2 = 0) (hret : x = 1 ∨ (s, 0) = selDisp d η (x, y)) :
    hG d x y s ≤ hG d (x - 2 * η - 1) (y + 1) s := by
  unfold hG
  rw [stair_corner_zero d (x + s) (y) (by omega)]
  rw [stair_corner_zero d (x) (y) (by omega)]
  rw [stair_corner_zero d (x - 2 * η - 1 + s) (y + 1) (by omega)]
  rw [stair_corner_zero d (x - 2 * η - 1) (y + 1) (by omega)]
  rcases hret with h1 | h1
  · subst h1
    omega
  · have hE : EvenSite (x, y) := by unfold EvenSite; dsimp only; omega
    unfold selDisp at h1
    rw [if_pos hE] at h1
    split_ifs at h1 <;> (try simp only [Prod.mk.injEq] at *) <;> omega

/-- The vertical stair increment: `vG y s` for the step `(0, s)` from row `y` (`s = ±1`). -/
def vG (y s : ℤ) : ℤ := if s = 1 then -y else y + -1

theorem tri_up (y : ℤ) : (y + 1) * (y + 1 - 1) / 2 - y * (y - 1) / 2 = y := by
  have h : (y + 1) * (y + 1 - 1) = y * (y - 1) + 2 * y := by ring
  rw [h]
  generalize y * (y - 1) = A
  omega

theorem tri_down (y : ℤ) : y * (y - 1) / 2 - (y + -1) * (y + -1 - 1) / 2 = y + -1 := by
  have h : y * (y - 1) = (y + -1) * (y + -1 - 1) + 2 * (y + -1) := by ring
  rw [h]
  generalize (y + -1) * (y + -1 - 1) = B
  omega

theorem not_stairCorner (d a b : ℤ) (h : ¬ ((a = 0 ∧ b = 0) ∨ (a = 2 ∧ b = d + 1))) :
    ¬ BaseMask.StairEvenCorner d (a, b) := h

/-- A site of the interior box is a raw site of the stair tile. -/
theorem mem_raw_of_box (k : ℕ) (a b : ℤ)
    (h : 2 - (2 * (k : ℤ) + 3) ≤ a ∧ a ≤ 2 * (k : ℤ) + 3 ∧ 0 ≤ b ∧ b ≤ 2 * (k : ℤ) + 3 + 1 ∧
      1 ≤ a + b ∧ a + b ≤ 2 * (k : ℤ) + 3 + 2) :
    (a, b) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites := by
  rw [BaseMask.mem_stairEven_raw_iff]
  exact ⟨⟨h.1, h.2.1⟩, ⟨h.2.2.1, h.2.2.2.1⟩, Or.inr ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩⟩

/-- The horizontal increment of the reciprocal field at a raw site is `hG`. -/
theorem incr_hG (k : ℕ) (s u v : ℤ) (hpt : (u + s, v) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites)
    (hu : (u, v) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites) :
    incr (reciprocalField k) (s, 0) (u, v) = hG (2 * (k : ℤ) + 3) u v s := by
  have e : (u, v) + (s, 0) = (u + s, v) := by ext <;> simp
  rw [incr_raw_stair k (s, 0) (u, v) hu (by rw [e]; exact hpt), e, stair_step_eq_hG]

/-- The vertical increment of the reciprocal field at a raw site, away from the corners, is `vG`. -/
theorem incr_vert (k : ℕ) (s x y : ℤ) (hs : s = 1 ∨ s = -1)
    (h0 : (x, y) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites)
    (h1 : (x, y + s) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites)
    (c0 : ¬ ((x = 0 ∧ y = 0) ∨ (x = 2 ∧ y = 2 * (k : ℤ) + 3 + 1)))
    (c1 : ¬ ((x = 0 ∧ y + s = 0) ∨ (x = 2 ∧ y + s = 2 * (k : ℤ) + 3 + 1))) :
    incr (reciprocalField k) (0, s) (x, y) = vG y s := by
  have e : (x, y) + (0, s) = (x, y + s) := by ext <;> simp
  rw [incr_raw_stair k (0, s) (x, y) h0 (by rw [e]; exact h1), e]
  rcases hs with rfl | rfl
  · have h := tri_up y
    rw [show vG y 1 = -y from by unfold vG; simp]
    unfold BaseMask.stairEvenValue
    dsimp only
    rw [if_neg (not_stairCorner _ _ _ c1), if_neg (not_stairCorner _ _ _ c0)]
    linarith
  · have h := tri_down y
    rw [show vG y (-1) = y + -1 from by unfold vG; norm_num]
    unfold BaseMask.stairEvenValue
    dsimp only
    rw [if_neg (not_stairCorner _ _ _ c1), if_neg (not_stairCorner _ _ _ c0)]
    linarith

/-- The vertical price/chain inequality: `vG y s − vG (y + 1) s ≤ s`. -/
theorem vG_one (y : ℤ) : vG y 1 = -y := by unfold vG; simp

theorem vG_neg_one (y : ℤ) : vG y (-1) = y + -1 := by unfold vG; norm_num

theorem vG_P (y s : ℤ) (hs : s = 1 ∨ s = -1) : vG y s - vG (y + 1) s ≤ s := by
  rcases hs with rfl | rfl
  · rw [vG_one, vG_one]; linarith
  · rw [vG_neg_one, vG_neg_one]; linarith

theorem smul_shortShift_recip (k : ℕ) (η : ℤ) : η • (reciprocalFrame k).shortShift = (-2 * η, 0) := by
  rw [reciprocalFrame_shortShift]
  ext <;> (simp; try ring)

/-- **Horizontal slip on the interior box.** -/
theorem slip_horiz_le (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hs : s = 1 ∨ s = -1)
    (hbox : 6 - (2 * (k : ℤ) + 3) ≤ x ∧ x ≤ 2 * (k : ℤ) + 3 - 3 ∧ 1 ≤ y ∧ y ≤ 2 * (k : ℤ) + 3 - 1 ∧
      4 ≤ x + y ∧ x + y ≤ 2 * (k : ℤ) + 3 - 1)
    (hpar : (x + y) % 2 = 0) (hret : x = 1 ∨ (s, 0) = selDisp (2 * (k : ℤ) + 3) η (x, y)) :
    (reciprocalFrame k).slip (reciprocalField k) η ((x, y) + (s, 0)) ≤
      (reciprocalFrame k).slip (reciprocalField k) η (x, y) := by
  apply slip_edge_le (reciprocalField k) (reciprocalFrame k) η (x, y) (s, 0)
  rw [smul_shortShift_recip k η]
  have e1 : (x, y) + (-2 * η, 0) = (x - 2 * η, y) := by ext <;> (simp; try ring)
  rw [e1, incr_hG k s x y (mem_raw_of_box k (x + s) y (by omega)) (mem_raw_of_box k x y (by omega)),
    incr_hG k s (x - 2 * η) y (mem_raw_of_box k (x - 2 * η + s) y (by omega))
      (mem_raw_of_box k (x - 2 * η) y (by omega))]
  exact horiz_D_ineq (2 * (k : ℤ) + 3) η x y s (by omega) (by omega) hpar hret

/-- **Vertical slip on the interior box** (no retention needed). -/
theorem slip_vert_le (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hs : s = 1 ∨ s = -1)
    (hbox : 6 - (2 * (k : ℤ) + 3) ≤ x ∧ x ≤ 2 * (k : ℤ) + 3 - 3 ∧ 1 ≤ y ∧ y ≤ 2 * (k : ℤ) + 3 - 1 ∧
      4 ≤ x + y ∧ x + y ≤ 2 * (k : ℤ) + 3 - 1) :
    (reciprocalFrame k).slip (reciprocalField k) η ((x, y) + (0, s)) ≤
      (reciprocalFrame k).slip (reciprocalField k) η (x, y) := by
  apply slip_edge_le (reciprocalField k) (reciprocalFrame k) η (x, y) (0, s)
  rw [smul_shortShift_recip k η]
  have e1 : (x, y) + (-2 * η, 0) = (x - 2 * η, y) := by ext <;> (simp; try ring)
  rw [e1, incr_vert k s x y hs (mem_raw_of_box k x y (by omega)) (mem_raw_of_box k x (y + s) (by omega))
      (by omega) (by omega),
    incr_vert k s (x - 2 * η) y hs (mem_raw_of_box k (x - 2 * η) y (by omega))
      (mem_raw_of_box k (x - 2 * η) (y + s) (by omega)) (by omega) (by omega)]

/-- **Horizontal price on the interior box.** -/
theorem price_horiz_le (k : ℕ) (η x y s : ℤ) (hs : s = 1 ∨ s = -1)
    (hbox : 6 - (2 * (k : ℤ) + 3) ≤ x ∧ x ≤ 2 * (k : ℤ) + 3 - 3 ∧ 1 ≤ y ∧ y ≤ 2 * (k : ℤ) + 3 - 1 ∧
      4 ≤ x + y ∧ x + y ≤ 2 * (k : ℤ) + 3 - 1)
    (hpar : (x + y) % 2 = 0) (hret : x = 1 ∨ (s, 0) = selDisp (2 * (k : ℤ) + 3) η (x, y)) :
    (reciprocalFrame k).price (reciprocalField k) ((x, y) + (s, 0)) ≤
      (reciprocalFrame k).price (reciprocalField k) (x, y) := by
  apply price_edge_le k (reciprocalField k) (x, y) (s, 0)
  have e1 : (x, y) - (1, -1) = (x - 1, y + 1) := by ext <;> (simp; try ring)
  rw [e1, incr_hG k s x y (mem_raw_of_box k (x + s) y (by omega)) (mem_raw_of_box k x y (by omega)),
    incr_hG k s (x - 1) (y + 1) (mem_raw_of_box k (x - 1 + s) (y + 1) (by omega))
      (mem_raw_of_box k (x - 1) (y + 1) (by omega))]
  dsimp only
  have := horiz_P_ineq (2 * (k : ℤ) + 3) η x y s (by omega) (by omega) hpar hret
  linarith

/-- **Vertical price on the interior box** (no retention needed). -/
theorem price_vert_le (k : ℕ) (x y s : ℤ) (hs : s = 1 ∨ s = -1)
    (hbox : 6 - (2 * (k : ℤ) + 3) ≤ x ∧ x ≤ 2 * (k : ℤ) + 3 - 3 ∧ 1 ≤ y ∧ y ≤ 2 * (k : ℤ) + 3 - 1 ∧
      4 ≤ x + y ∧ x + y ≤ 2 * (k : ℤ) + 3 - 1) :
    (reciprocalFrame k).price (reciprocalField k) ((x, y) + (0, s)) ≤
      (reciprocalFrame k).price (reciprocalField k) (x, y) := by
  apply price_edge_le k (reciprocalField k) (x, y) (0, s)
  have e1 : (x, y) - (1, -1) = (x - 1, y + 1) := by ext <;> (simp; try ring)
  rw [e1, incr_vert k s x y hs (mem_raw_of_box k x y (by omega)) (mem_raw_of_box k x (y + s) (by omega))
      (by omega) (by omega),
    incr_vert k s (x - 1) (y + 1) hs (mem_raw_of_box k (x - 1) (y + 1) (by omega))
      (mem_raw_of_box k (x - 1) (y + 1 + s) (by omega)) (by omega) (by omega)]
  dsimp only
  exact vG_P y s hs

/-- **Horizontal chain on the interior box.** -/
theorem chain_horiz_le (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hs : s = 1 ∨ s = -1)
    (hbox : 6 - (2 * (k : ℤ) + 3) ≤ x ∧ x ≤ 2 * (k : ℤ) + 3 - 3 ∧ 1 ≤ y ∧ y ≤ 2 * (k : ℤ) + 3 - 1 ∧
      4 ≤ x + y ∧ x + y ≤ 2 * (k : ℤ) + 3 - 1)
    (hpar : (x + y) % 2 = 0) (hret : x = 1 ∨ (s, 0) = selDisp (2 * (k : ℤ) + 3) η (x, y)) :
    (reciprocalFrame k).chainPotential (reciprocalField k) η ((x, y) + (s, 0)) ≤
      (reciprocalFrame k).chainPotential (reciprocalField k) η (x, y) := by
  apply chain_edge_le k (reciprocalField k) η (x, y) (s, 0)
  rw [smul_shortShift_recip k η]
  have e2 : (x, y) + (-2 * η, 0) - (1, -1) = (x - 2 * η - 1, y + 1) := by ext <;> (simp; try ring)
  rw [e2, incr_hG k s x y (mem_raw_of_box k (x + s) y (by omega)) (mem_raw_of_box k x y (by omega)),
    incr_hG k s (x - 2 * η - 1) (y + 1) (mem_raw_of_box k (x - 2 * η - 1 + s) (y + 1) (by omega))
      (mem_raw_of_box k (x - 2 * η - 1) (y + 1) (by omega))]
  dsimp only
  have := horiz_Phi_ineq (2 * (k : ℤ) + 3) η x y s (by omega) (by omega) hpar hret
  linarith

/-- **Vertical chain on the interior box** (no retention needed). -/
theorem chain_vert_le (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hs : s = 1 ∨ s = -1)
    (hbox : 6 - (2 * (k : ℤ) + 3) ≤ x ∧ x ≤ 2 * (k : ℤ) + 3 - 3 ∧ 1 ≤ y ∧ y ≤ 2 * (k : ℤ) + 3 - 1 ∧
      4 ≤ x + y ∧ x + y ≤ 2 * (k : ℤ) + 3 - 1) :
    (reciprocalFrame k).chainPotential (reciprocalField k) η ((x, y) + (0, s)) ≤
      (reciprocalFrame k).chainPotential (reciprocalField k) η (x, y) := by
  apply chain_edge_le k (reciprocalField k) η (x, y) (0, s)
  rw [smul_shortShift_recip k η]
  have e2 : (x, y) + (-2 * η, 0) - (1, -1) = (x - 2 * η - 1, y + 1) := by ext <;> (simp; try ring)
  rw [e2, incr_vert k s x y hs (mem_raw_of_box k x y (by omega)) (mem_raw_of_box k x (y + s) (by omega))
      (by omega) (by omega),
    incr_vert k s (x - 2 * η - 1) (y + 1) hs (mem_raw_of_box k (x - 2 * η - 1) (y + 1) (by omega))
      (mem_raw_of_box k (x - 2 * η - 1) (y + 1 + s) (by omega)) (by omega) (by omega)]
  dsimp only
  exact vG_P y s hs

/-- **Retention of a horizontal step.** For an interior even centre, a retained horizontal step is black (`x = 1`) or the
selected step of the white centre. -/
theorem retention_horiz (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1)
    (hN : NativeP (2 * (k : ℤ) + 3) (x, y))
    (hpar : (x + y) % 2 = 0)
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, y) ((x, y) + (s, 0))) :
    x = 1 ∨ (s, 0) = selDisp (2 * (k : ℤ) + 3) η (x, y) := by
  have hE : EvenSite (x, y) := by unfold EvenSite; dsimp only; omega
  by_cases hx : x = 1
  · exact Or.inl hx
  · right
    have hw : laplacian (reciprocalField k) (x, y) = 0 := by
      rw [laplacian_reciprocal_native k hN, if_pos hE]
      dsimp only
      rw [if_neg hx]
    rw [ePolicy_white k η hη (x, y) ((x, y) + (s, 0)) hw] at hpol
    rw [selDisp_nativeRep k η hη hN] at hpol
    have e : (x, y) + (s, 0) - (x, y) = (s, 0) := by ext <;> (simp; try ring)
    rw [e] at hpol
    exact hpol

/-- A raw site has the stair value as its reciprocal field value. -/
theorem reciprocalField_eq_stair (k : ℕ) {p : Site}
    (hp : p ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites) :
    reciprocalField k p = BaseMask.stairEvenValue (2 * (k : ℤ) + 3) p := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have h := reciprocalField_reduction k (z := p) (y := p) (i := 0) (j := 0) hp
    (by simp [combine_mk_one hd])
  omega

/-- The unit deck vector `U = (d, 1)` shifts the reciprocal field by nothing. -/
theorem reciprocalField_add_U (k : ℕ) (p : Site) :
    reciprocalField k (p + (2 * (k : ℤ) + 3, 1)) = reciprocalField k p := by
  have h := reciprocalField_period_kernel k p
  rw [kernel_threes] at h
  exact h

/-- A site whose `U`-translate is raw has the stair value of the translate. -/
theorem reciprocalField_eq_stair_U (k : ℕ) {p : Site}
    (hp : p + (2 * (k : ℤ) + 3, 1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites) :
    reciprocalField k p = BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (p + (2 * (k : ℤ) + 3, 1)) := by
  rw [← reciprocalField_add_U k p, reciprocalField_eq_stair k hp]

/-- The value of the reciprocal field at a raw site of the box. -/
theorem F_raw_pt (k : ℕ) (a b : ℤ)
    (h : 2 - (2 * (k : ℤ) + 3) ≤ a ∧ a ≤ 2 * (k : ℤ) + 3 ∧ 0 ≤ b ∧ b ≤ 2 * (k : ℤ) + 3 + 1 ∧
      1 ≤ a + b ∧ a + b ≤ 2 * (k : ℤ) + 3 + 2) :
    reciprocalField k (a, b) = BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (a, b) :=
  reciprocalField_eq_stair k (mem_raw_of_box k a b h)

/-- The value at `(a, b)` through its `U`-translate `(a + d, b + 1)`, which is raw. -/
theorem F_U_pt (k : ℕ) (a b : ℤ)
    (h : 2 - (2 * (k : ℤ) + 3) ≤ a + (2 * (k : ℤ) + 3) ∧ a + (2 * (k : ℤ) + 3) ≤ 2 * (k : ℤ) + 3 ∧
      0 ≤ b + 1 ∧ b + 1 ≤ 2 * (k : ℤ) + 3 + 1 ∧
      1 ≤ a + (2 * (k : ℤ) + 3) + (b + 1) ∧ a + (2 * (k : ℤ) + 3) + (b + 1) ≤ 2 * (k : ℤ) + 3 + 2) :
    reciprocalField k (a, b) = BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (a + (2 * (k : ℤ) + 3), b + 1) :=
  reciprocalField_eq_stair_U k (mem_raw_of_box k (a + (2 * (k : ℤ) + 3)) (b + 1) h)

/-- The retained horizontal steps on the sum-2 segment: black at `x = 1`, otherwise the selection, `-1` for `x ≤ 0`
and `+1` for `x ≥ 1`. -/
theorem retained_sign_sum2 (k : ℕ) (η x y s : ℤ) (hsum : x + y = 2) (hy : 1 ≤ y)
    (hx : 6 - (2 * (k : ℤ) + 3) ≤ x)
    (hret : x = 1 ∨ (s, 0) = selDisp (2 * (k : ℤ) + 3) η (x, y)) :
    x = 1 ∨ (x ≤ 0 ∧ s = -1) ∨ (1 ≤ x ∧ s = 1) := by
  rcases hret with h | h
  · exact Or.inl h
  · have hE : EvenSite (x, y) := by unfold EvenSite; dsimp only; omega
    unfold selDisp at h
    rw [if_pos hE] at h
    split_ifs at h <;> (try simp only [Prod.mk.injEq] at h) <;> (try simp only [Prod.mk.injEq] at *) <;> omega

/-- **Lower-left diagonal, horizontal slip (sum 2).** For the centre `(x, y)` on `x + y = 2` (`y ≥ 1`), the increment
of the reciprocal field along a retained horizontal step at the centre does not exceed the increment at the shifted centre.
The shifted sites outside the raw domain are read through their `U`-translates. -/
theorem diagLow_D_horiz (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1)
    (hs : s = 1 ∨ s = -1) (hsum : x + y = 2) (hy : 1 ≤ y) (hx : 6 - (2 * (k : ℤ) + 3) ≤ x)
    (hsign : x = 1 ∨ (x ≤ 0 ∧ s = -1) ∨ (1 ≤ x ∧ s = 1)) :
    incr (reciprocalField k) (s, 0) (x, y) ≤ incr (reciprocalField k) (s, 0) (x - 2 * η, y) := by
  have e1 : ∀ a b : ℤ, (a, b) + (s, 0) = (a + s, b) := fun a b => by ext <;> simp
  unfold incr
  rw [e1 x y, e1 (x - 2 * η) y]
  have htri := tri_up y
  rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
  · rw [F_raw_pt k (x + 1) y (by omega), F_raw_pt k x y (by omega), F_U_pt k (x - 2 * 1) y (by omega),
      F_raw_pt k (x - 2 * 1 + 1) y (by omega)]
    unfold BaseMask.stairEvenValue
    dsimp only
    rw [if_neg (not_stairCorner _ (x + 1) y (by omega)), if_neg (not_stairCorner _ x y (by omega)),
      if_neg (not_stairCorner _ (x - 2 * 1 + (2 * (k : ℤ) + 3)) (y + 1) (by omega)),
      if_neg (not_stairCorner _ (x - 2 * 1 + 1) y (by omega))]
    omega
  · rw [F_raw_pt k (x + -1) y (by omega), F_raw_pt k x y (by omega), F_U_pt k (x - 2 * 1) y (by omega),
      F_U_pt k (x - 2 * 1 + -1) y (by omega)]
    unfold BaseMask.stairEvenValue
    dsimp only
    rw [if_neg (not_stairCorner _ (x + -1) y (by omega)), if_neg (not_stairCorner _ x y (by omega)),
      if_neg (not_stairCorner _ (x - 2 * 1 + (2 * (k : ℤ) + 3)) (y + 1) (by omega)),
      if_neg (not_stairCorner _ (x - 2 * 1 + -1 + (2 * (k : ℤ) + 3)) (y + 1) (by omega))]
    omega
  · rw [F_raw_pt k (x + 1) y (by omega), F_raw_pt k x y (by omega), F_raw_pt k (x - 2 * -1) y (by omega),
      F_raw_pt k (x - 2 * -1 + 1) y (by omega)]
    unfold BaseMask.stairEvenValue
    dsimp only
    rw [if_neg (not_stairCorner _ (x + 1) y (by omega)), if_neg (not_stairCorner _ x y (by omega)),
      if_neg (not_stairCorner _ (x - 2 * -1) y (by omega)),
      if_neg (not_stairCorner _ (x - 2 * -1 + 1) y (by omega))]
    omega
  · rw [F_raw_pt k (x + -1) y (by omega), F_raw_pt k x y (by omega), F_raw_pt k (x - 2 * -1) y (by omega),
      F_raw_pt k (x - 2 * -1 + -1) y (by omega)]
    unfold BaseMask.stairEvenValue
    dsimp only
    rw [if_neg (not_stairCorner _ (x + -1) y (by omega)), if_neg (not_stairCorner _ x y (by omega)),
      if_neg (not_stairCorner _ (x - 2 * -1) y (by omega)),
      if_neg (not_stairCorner _ (x - 2 * -1 + -1) y (by omega))]
    omega

/-- **Lower-left diagonal, horizontal price (sum 2).** On the sum-2 segment every site of the price is raw. -/
theorem diagLow_P_horiz (k : ℕ) (x y s : ℤ) (hs : s = 1 ∨ s = -1)
    (hsum : x + y = 2) (hy : 1 ≤ y) (hx : 6 - (2 * (k : ℤ) + 3) ≤ x)
    (hsign : x = 1 ∨ (x ≤ 0 ∧ s = -1) ∨ (1 ≤ x ∧ s = 1)) :
    incr (reciprocalField k) (s, 0) (x, y) - incr (reciprocalField k) (s, 0) (x - 1, y + 1) ≤ 0 := by
  have e1 : ∀ a b : ℤ, (a, b) + (s, 0) = (a + s, b) := fun a b => by ext <;> simp
  unfold incr
  rw [e1 x y, e1 (x - 1) (y + 1)]
  have htri := tri_up y
  rcases hs with rfl | rfl
  · rw [F_raw_pt k (x + 1) y (by omega), F_raw_pt k x y (by omega), F_raw_pt k (x - 1 + 1) (y + 1) (by omega),
      F_raw_pt k (x - 1) (y + 1) (by omega)]
    unfold BaseMask.stairEvenValue
    dsimp only
    rw [if_neg (not_stairCorner _ (x + 1) y (by omega)), if_neg (not_stairCorner _ x y (by omega)),
      if_neg (not_stairCorner _ (x - 1 + 1) (y + 1) (by omega)), if_neg (not_stairCorner _ (x - 1) (y + 1) (by omega))]
    omega
  · rw [F_raw_pt k (x + -1) y (by omega), F_raw_pt k x y (by omega), F_raw_pt k (x - 1 + -1) (y + 1) (by omega),
      F_raw_pt k (x - 1) (y + 1) (by omega)]
    unfold BaseMask.stairEvenValue
    dsimp only
    rw [if_neg (not_stairCorner _ (x + -1) y (by omega)), if_neg (not_stairCorner _ x y (by omega)),
      if_neg (not_stairCorner _ (x - 1 + -1) (y + 1) (by omega)), if_neg (not_stairCorner _ (x - 1) (y + 1) (by omega))]
    omega

/-- **Lower-left diagonal, horizontal chain (sum 2).** The shifted sites `(x - 2 eta - 1, y + 1)` are read through their
`U`-translates when they leave the raw domain (eta = 1). -/
theorem diagLow_Phi_horiz (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hs : s = 1 ∨ s = -1)
    (hsum : x + y = 2) (hy : 1 ≤ y) (hx : 6 - (2 * (k : ℤ) + 3) ≤ x)
    (hsign : x = 1 ∨ (x ≤ 0 ∧ s = -1) ∨ (1 ≤ x ∧ s = 1)) :
    incr (reciprocalField k) (s, 0) (x, y) - incr (reciprocalField k) (s, 0) (x - 2 * η - 1, y + 1) ≤ 0 := by
  have e1 : ∀ a b : ℤ, (a, b) + (s, 0) = (a + s, b) := fun a b => by ext <;> simp
  unfold incr
  rw [e1 x y, e1 (x - 2 * η - 1) (y + 1)]
  have htri := tri_up y
  have htri2 := tri_up (y + 1)
  rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
  · rw [F_raw_pt k (x + 1) y (by omega), F_raw_pt k x y (by omega), F_U_pt k (x - 2 * 1 - 1) (y + 1) (by omega),
      F_raw_pt k (x - 2 * 1 - 1 + 1) (y + 1) (by omega)]
    unfold BaseMask.stairEvenValue
    dsimp only
    rw [if_neg (not_stairCorner _ (x + 1) y (by omega)), if_neg (not_stairCorner _ x y (by omega)),
      if_neg (not_stairCorner _ (x - 2 * 1 - 1 + (2 * (k : ℤ) + 3)) (y + 1 + 1) (by omega)),
      if_neg (not_stairCorner _ (x - 2 * 1 - 1 + 1) (y + 1) (by omega))]
    omega
  · rw [F_raw_pt k (x + -1) y (by omega), F_raw_pt k x y (by omega), F_U_pt k (x - 2 * 1 - 1) (y + 1) (by omega),
      F_U_pt k (x - 2 * 1 - 1 + -1) (y + 1) (by omega)]
    unfold BaseMask.stairEvenValue
    dsimp only
    rw [if_neg (not_stairCorner _ (x + -1) y (by omega)), if_neg (not_stairCorner _ x y (by omega)),
      if_neg (not_stairCorner _ (x - 2 * 1 - 1 + (2 * (k : ℤ) + 3)) (y + 1 + 1) (by omega)),
      if_neg (not_stairCorner _ (x - 2 * 1 - 1 + -1 + (2 * (k : ℤ) + 3)) (y + 1 + 1) (by omega))]
    omega
  · rw [F_raw_pt k (x + 1) y (by omega), F_raw_pt k x y (by omega), F_raw_pt k (x - 2 * -1 - 1) (y + 1) (by omega),
      F_raw_pt k (x - 2 * -1 - 1 + 1) (y + 1) (by omega)]
    unfold BaseMask.stairEvenValue
    dsimp only
    rw [if_neg (not_stairCorner _ (x + 1) y (by omega)), if_neg (not_stairCorner _ x y (by omega)),
      if_neg (not_stairCorner _ (x - 2 * -1 - 1) (y + 1) (by omega)),
      if_neg (not_stairCorner _ (x - 2 * -1 - 1 + 1) (y + 1) (by omega))]
    omega
  · rw [F_raw_pt k (x + -1) y (by omega), F_raw_pt k x y (by omega), F_raw_pt k (x - 2 * -1 - 1) (y + 1) (by omega),
      F_raw_pt k (x - 2 * -1 - 1 + -1) (y + 1) (by omega)]
    unfold BaseMask.stairEvenValue
    dsimp only
    rw [if_neg (not_stairCorner _ (x + -1) y (by omega)), if_neg (not_stairCorner _ x y (by omega)),
      if_neg (not_stairCorner _ (x - 2 * -1 - 1) (y + 1) (by omega)),
      if_neg (not_stairCorner _ (x - 2 * -1 - 1 + -1) (y + 1) (by omega))]
    omega

theorem incr_vert_U (k : ℕ) (s a b : ℤ) (hs : s = 1 ∨ s = -1)
    (h0 : (a + (2 * (k : ℤ) + 3), b + 1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites)
    (h1 : (a + (2 * (k : ℤ) + 3), b + 1 + s) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites)
    (c0 : ¬ ((a + (2 * (k : ℤ) + 3) = 0 ∧ b + 1 = 0) ∨ (a + (2 * (k : ℤ) + 3) = 2 ∧ b + 1 = (2 * (k : ℤ) + 3) + 1)))
    (c1 : ¬ ((a + (2 * (k : ℤ) + 3) = 0 ∧ b + 1 + s = 0) ∨ (a + (2 * (k : ℤ) + 3) = 2 ∧ b + 1 + s = (2 * (k : ℤ) + 3) + 1))) :
    incr (reciprocalField k) (0, s) (a, b) = vG (b + 1) s := by
  have key := incr_vert k s (a + (2 * (k : ℤ) + 3)) (b + 1) hs h0 h1 c0 c1
  have hA := reciprocalField_add_U k (a, b)
  have hB := reciprocalField_add_U k ((a, b) + (0, s))
  unfold incr at key ⊢
  rw [← hA, ← hB]
  have e1 : (a, b) + (0, s) + ((2 * (k : ℤ) + 3), 1) = (a + (2 * (k : ℤ) + 3), b + 1 + s) := by ext <;> (simp; try ring)
  have e2 : (a, b) + ((2 * (k : ℤ) + 3), 1) = (a + (2 * (k : ℤ) + 3), b + 1) := by ext <;> (simp; try ring)
  have e4 : (a + (2 * (k : ℤ) + 3), b + 1) + (0, s) = (a + (2 * (k : ℤ) + 3), b + 1 + s) := by ext <;> (simp; try ring)
  rw [e1, e2]
  rw [e4] at key
  exact key

theorem diagLow3_D_vert (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hs : s = 1 ∨ s = -1) (hsum : x + y = 3) (hy : 1 ≤ y)
    (hx : 6 - (2 * (k : ℤ) + 3) ≤ x) :
    incr (reciprocalField k) (0, s) (x, y) ≤ incr (reciprocalField k) (0, s) (x - 2 * η, y) := by
  rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
  · have hi1 := incr_vert k (1) (x) (y) (by norm_num)
      (mem_raw_of_box k (x) (y) (by omega)) (mem_raw_of_box k (x) ((y) + (1)) (by omega))
      (by omega) (by omega)
    have hi2 := incr_vert k (1) (x - 2 * 1) (y) (by norm_num)
      (mem_raw_of_box k (x - 2 * 1) (y) (by omega)) (mem_raw_of_box k (x - 2 * 1) ((y) + (1)) (by omega))
      (by omega) (by omega)
    linarith [vG_one y, vG_neg_one y, vG_one (y + 1), vG_neg_one (y + 1), vG_one (y + 1 + 1), vG_neg_one (y + 1 + 1)]
  · have hi3 := incr_vert k (-1) (x) (y) (by norm_num)
      (mem_raw_of_box k (x) (y) (by omega)) (mem_raw_of_box k (x) ((y) + (-1)) (by omega))
      (by omega) (by omega)
    have hi4 := incr_vert_U k (-1) (x - 2 * 1) (y) (by norm_num)
      (mem_raw_of_box k ((x - 2 * 1) + (2 * (k : ℤ) + 3)) ((y) + 1) (by omega))
      (mem_raw_of_box k ((x - 2 * 1) + (2 * (k : ℤ) + 3)) ((y) + 1 + (-1)) (by omega)) (by omega) (by omega)
    linarith [vG_one y, vG_neg_one y, vG_one (y + 1), vG_neg_one (y + 1), vG_one (y + 1 + 1), vG_neg_one (y + 1 + 1)]
  · have hi5 := incr_vert k (1) (x) (y) (by norm_num)
      (mem_raw_of_box k (x) (y) (by omega)) (mem_raw_of_box k (x) ((y) + (1)) (by omega))
      (by omega) (by omega)
    have hi6 := incr_vert k (1) (x - 2 * -1) (y) (by norm_num)
      (mem_raw_of_box k (x - 2 * -1) (y) (by omega)) (mem_raw_of_box k (x - 2 * -1) ((y) + (1)) (by omega))
      (by omega) (by omega)
    linarith [vG_one y, vG_neg_one y, vG_one (y + 1), vG_neg_one (y + 1), vG_one (y + 1 + 1), vG_neg_one (y + 1 + 1)]
  · have hi7 := incr_vert k (-1) (x) (y) (by norm_num)
      (mem_raw_of_box k (x) (y) (by omega)) (mem_raw_of_box k (x) ((y) + (-1)) (by omega))
      (by omega) (by omega)
    have hi8 := incr_vert k (-1) (x - 2 * -1) (y) (by norm_num)
      (mem_raw_of_box k (x - 2 * -1) (y) (by omega)) (mem_raw_of_box k (x - 2 * -1) ((y) + (-1)) (by omega))
      (by omega) (by omega)
    linarith [vG_one y, vG_neg_one y, vG_one (y + 1), vG_neg_one (y + 1), vG_one (y + 1 + 1), vG_neg_one (y + 1 + 1)]

theorem diagLow3_P_vert (k : ℕ) (x y s : ℤ) (hs : s = 1 ∨ s = -1) (hsum : x + y = 3) (hy : 1 ≤ y)
    (hx : 6 - (2 * (k : ℤ) + 3) ≤ x) :
    incr (reciprocalField k) (0, s) (x, y) - incr (reciprocalField k) (0, s) (x - 1, y + 1) ≤ s := by
  rcases hs with rfl | rfl
  · have hi9 := incr_vert k (1) (x) (y) (by norm_num)
      (mem_raw_of_box k (x) (y) (by omega)) (mem_raw_of_box k (x) ((y) + (1)) (by omega))
      (by omega) (by omega)
    have hi10 := incr_vert k (1) (x - 1) (y + 1) (by norm_num)
      (mem_raw_of_box k (x - 1) (y + 1) (by omega)) (mem_raw_of_box k (x - 1) ((y + 1) + (1)) (by omega))
      (by omega) (by omega)
    linarith [vG_one y, vG_neg_one y, vG_one (y + 1), vG_neg_one (y + 1), vG_one (y + 1 + 1), vG_neg_one (y + 1 + 1)]
  · have hi11 := incr_vert k (-1) (x) (y) (by norm_num)
      (mem_raw_of_box k (x) (y) (by omega)) (mem_raw_of_box k (x) ((y) + (-1)) (by omega))
      (by omega) (by omega)
    have hi12 := incr_vert k (-1) (x - 1) (y + 1) (by norm_num)
      (mem_raw_of_box k (x - 1) (y + 1) (by omega)) (mem_raw_of_box k (x - 1) ((y + 1) + (-1)) (by omega))
      (by omega) (by omega)
    linarith [vG_one y, vG_neg_one y, vG_one (y + 1), vG_neg_one (y + 1), vG_one (y + 1 + 1), vG_neg_one (y + 1 + 1)]

theorem diagLow3_Phi_vert (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hs : s = 1 ∨ s = -1) (hsum : x + y = 3) (hy : 1 ≤ y)
    (hx : 6 - (2 * (k : ℤ) + 3) ≤ x) :
    incr (reciprocalField k) (0, s) (x, y) - incr (reciprocalField k) (0, s) (x - 2 * η - 1, y + 1) ≤ s := by
  rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
  · have hi13 := incr_vert k (1) (x) (y) (by norm_num)
      (mem_raw_of_box k (x) (y) (by omega)) (mem_raw_of_box k (x) ((y) + (1)) (by omega))
      (by omega) (by omega)
    have hi14 := incr_vert k (1) (x - 2 * 1 - 1) (y + 1) (by norm_num)
      (mem_raw_of_box k (x - 2 * 1 - 1) (y + 1) (by omega)) (mem_raw_of_box k (x - 2 * 1 - 1) ((y + 1) + (1)) (by omega))
      (by omega) (by omega)
    linarith [vG_one y, vG_neg_one y, vG_one (y + 1), vG_neg_one (y + 1), vG_one (y + 1 + 1), vG_neg_one (y + 1 + 1)]
  · have hi15 := incr_vert k (-1) (x) (y) (by norm_num)
      (mem_raw_of_box k (x) (y) (by omega)) (mem_raw_of_box k (x) ((y) + (-1)) (by omega))
      (by omega) (by omega)
    have hi16 := incr_vert_U k (-1) (x - 2 * 1 - 1) (y + 1) (by norm_num)
      (mem_raw_of_box k ((x - 2 * 1 - 1) + (2 * (k : ℤ) + 3)) ((y + 1) + 1) (by omega))
      (mem_raw_of_box k ((x - 2 * 1 - 1) + (2 * (k : ℤ) + 3)) ((y + 1) + 1 + (-1)) (by omega)) (by omega) (by omega)
    linarith [vG_one y, vG_neg_one y, vG_one (y + 1), vG_neg_one (y + 1), vG_one (y + 1 + 1), vG_neg_one (y + 1 + 1)]
  · have hi17 := incr_vert k (1) (x) (y) (by norm_num)
      (mem_raw_of_box k (x) (y) (by omega)) (mem_raw_of_box k (x) ((y) + (1)) (by omega))
      (by omega) (by omega)
    have hi18 := incr_vert k (1) (x - 2 * -1 - 1) (y + 1) (by norm_num)
      (mem_raw_of_box k (x - 2 * -1 - 1) (y + 1) (by omega)) (mem_raw_of_box k (x - 2 * -1 - 1) ((y + 1) + (1)) (by omega))
      (by omega) (by omega)
    linarith [vG_one y, vG_neg_one y, vG_one (y + 1), vG_neg_one (y + 1), vG_one (y + 1 + 1), vG_neg_one (y + 1 + 1)]
  · have hi19 := incr_vert k (-1) (x) (y) (by norm_num)
      (mem_raw_of_box k (x) (y) (by omega)) (mem_raw_of_box k (x) ((y) + (-1)) (by omega))
      (by omega) (by omega)
    have hi20 := incr_vert k (-1) (x - 2 * -1 - 1) (y + 1) (by norm_num)
      (mem_raw_of_box k (x - 2 * -1 - 1) (y + 1) (by omega)) (mem_raw_of_box k (x - 2 * -1 - 1) ((y + 1) + (-1)) (by omega))
      (by omega) (by omega)
    linarith [vG_one y, vG_neg_one y, vG_one (y + 1), vG_neg_one (y + 1), vG_one (y + 1 + 1), vG_neg_one (y + 1 + 1)]

theorem diagLow1_D_vert (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hsgn : s = -η) (hsum : x + y = 1) (hy : 1 ≤ y)
    (hx : 6 - (2 * (k : ℤ) + 3) ≤ x) :
    incr (reciprocalField k) (0, s) (x, y) ≤ incr (reciprocalField k) (0, s) (x - 2 * η, y) := by
  rcases hη with rfl | rfl
  · have hs' : s = -1 := by omega
    subst hs'
    have hi21 := incr_vert_U k (-1) (x) (y) (by norm_num)
      (mem_raw_of_box k ((x) + (2 * (k : ℤ) + 3)) ((y) + 1) (by omega))
      (mem_raw_of_box k ((x) + (2 * (k : ℤ) + 3)) ((y) + 1 + (-1)) (by omega)) (by omega) (by omega)
    have hi22 := incr_vert_U k (-1) (x - 2 * 1) (y) (by norm_num)
      (mem_raw_of_box k ((x - 2 * 1) + (2 * (k : ℤ) + 3)) ((y) + 1) (by omega))
      (mem_raw_of_box k ((x - 2 * 1) + (2 * (k : ℤ) + 3)) ((y) + 1 + (-1)) (by omega)) (by omega) (by omega)
    linarith [vG_one y, vG_neg_one y, vG_one (y + 1), vG_neg_one (y + 1), vG_one (y + 1 + 1), vG_neg_one (y + 1 + 1)]
  · have hs' : s = 1 := by omega
    subst hs'
    have hi23 := incr_vert k (1) (x) (y) (by norm_num)
      (mem_raw_of_box k (x) (y) (by omega)) (mem_raw_of_box k (x) ((y) + (1)) (by omega))
      (by omega) (by omega)
    have hi24 := incr_vert k (1) (x - 2 * -1) (y) (by norm_num)
      (mem_raw_of_box k (x - 2 * -1) (y) (by omega)) (mem_raw_of_box k (x - 2 * -1) ((y) + (1)) (by omega))
      (by omega) (by omega)
    linarith [vG_one y, vG_neg_one y, vG_one (y + 1), vG_neg_one (y + 1), vG_one (y + 1 + 1), vG_neg_one (y + 1 + 1)]

theorem diagLow1_P_vert (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hsgn : s = -η) (hsum : x + y = 1) (hy : 1 ≤ y)
    (hx : 6 - (2 * (k : ℤ) + 3) ≤ x) :
    incr (reciprocalField k) (0, s) (x, y) - incr (reciprocalField k) (0, s) (x - 1, y + 1) ≤ s := by
  rcases hη with rfl | rfl
  · have hs' : s = -1 := by omega
    subst hs'
    have hi25 := incr_vert_U k (-1) (x) (y) (by norm_num)
      (mem_raw_of_box k ((x) + (2 * (k : ℤ) + 3)) ((y) + 1) (by omega))
      (mem_raw_of_box k ((x) + (2 * (k : ℤ) + 3)) ((y) + 1 + (-1)) (by omega)) (by omega) (by omega)
    have hi26 := incr_vert_U k (-1) (x - 1) (y + 1) (by norm_num)
      (mem_raw_of_box k ((x - 1) + (2 * (k : ℤ) + 3)) ((y + 1) + 1) (by omega))
      (mem_raw_of_box k ((x - 1) + (2 * (k : ℤ) + 3)) ((y + 1) + 1 + (-1)) (by omega)) (by omega) (by omega)
    linarith [vG_one y, vG_neg_one y, vG_one (y + 1), vG_neg_one (y + 1), vG_one (y + 1 + 1), vG_neg_one (y + 1 + 1)]
  · have hs' : s = 1 := by omega
    subst hs'
    have hi27 := incr_vert k (1) (x) (y) (by norm_num)
      (mem_raw_of_box k (x) (y) (by omega)) (mem_raw_of_box k (x) ((y) + (1)) (by omega))
      (by omega) (by omega)
    have hi28 := incr_vert k (1) (x - 1) (y + 1) (by norm_num)
      (mem_raw_of_box k (x - 1) (y + 1) (by omega)) (mem_raw_of_box k (x - 1) ((y + 1) + (1)) (by omega))
      (by omega) (by omega)
    linarith [vG_one y, vG_neg_one y, vG_one (y + 1), vG_neg_one (y + 1), vG_one (y + 1 + 1), vG_neg_one (y + 1 + 1)]

theorem diagLow1_Phi_vert (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hsgn : s = -η) (hsum : x + y = 1) (hy : 1 ≤ y)
    (hx : 6 - (2 * (k : ℤ) + 3) ≤ x) :
    incr (reciprocalField k) (0, s) (x, y) - incr (reciprocalField k) (0, s) (x - 2 * η - 1, y + 1) ≤ s := by
  rcases hη with rfl | rfl
  · have hs' : s = -1 := by omega
    subst hs'
    have hi29 := incr_vert_U k (-1) (x) (y) (by norm_num)
      (mem_raw_of_box k ((x) + (2 * (k : ℤ) + 3)) ((y) + 1) (by omega))
      (mem_raw_of_box k ((x) + (2 * (k : ℤ) + 3)) ((y) + 1 + (-1)) (by omega)) (by omega) (by omega)
    have hi30 := incr_vert_U k (-1) (x - 2 * 1 - 1) (y + 1) (by norm_num)
      (mem_raw_of_box k ((x - 2 * 1 - 1) + (2 * (k : ℤ) + 3)) ((y + 1) + 1) (by omega))
      (mem_raw_of_box k ((x - 2 * 1 - 1) + (2 * (k : ℤ) + 3)) ((y + 1) + 1 + (-1)) (by omega)) (by omega) (by omega)
    linarith [vG_one y, vG_neg_one y, vG_one (y + 1), vG_neg_one (y + 1), vG_one (y + 1 + 1), vG_neg_one (y + 1 + 1)]
  · have hs' : s = 1 := by omega
    subst hs'
    have hi31 := incr_vert k (1) (x) (y) (by norm_num)
      (mem_raw_of_box k (x) (y) (by omega)) (mem_raw_of_box k (x) ((y) + (1)) (by omega))
      (by omega) (by omega)
    have hi32 := incr_vert k (1) (x - 2 * -1 - 1) (y + 1) (by norm_num)
      (mem_raw_of_box k (x - 2 * -1 - 1) (y + 1) (by omega)) (mem_raw_of_box k (x - 2 * -1 - 1) ((y + 1) + (1)) (by omega))
      (by omega) (by omega)
    linarith [vG_one y, vG_neg_one y, vG_one (y + 1), vG_neg_one (y + 1), vG_one (y + 1 + 1), vG_neg_one (y + 1 + 1)]

/-- A retained vertical step at a sum-1 centre is the selected step `(0, -eta)` (the odd down step). -/
theorem retention_vert1 (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1)
    (hN : NativeP (2 * (k : ℤ) + 3) (x, y)) (hsum : x + y = 1) (hy : 1 ≤ y)
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, y) ((x, y) + (0, s))) :
    s = -η := by
  have hN' := hN
  simp only [NativeP, Prod.mk.injEq] at hN'
  have hE : ¬ EvenSite (x, y) := by unfold EvenSite; dsimp only; omega
  have hw : laplacian (reciprocalField k) (x, y) = 0 := by
    rw [laplacian_reciprocal_native k hN, if_neg hE]
    dsimp only
    rw [if_neg]
    omega
  rw [ePolicy_white k η hη (x, y) ((x, y) + (0, s)) hw, selDisp_nativeRep k η hη hN] at hpol
  have e : (x, y) + (0, s) - (x, y) = (0, s) := by ext <;> (simp; try ring)
  rw [e] at hpol
  unfold selDisp at hpol
  rw [if_neg hE] at hpol
  split_ifs at hpol with hO <;> (try simp only [Prod.mk.injEq] at hpol) <;> (try dsimp only at hO) <;> omega

/-- **Lower-left diagonal, horizontal slip on the policy edge (sum 2).** -/
theorem slip_low2_h (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hs : s = 1 ∨ s = -1)
    (hsum : x + y = 2) (hy : 1 ≤ y) (hx : 6 - (2 * (k : ℤ) + 3) ≤ x)
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, y) ((x, y) + (s, 0))) :
    (reciprocalFrame k).slip (reciprocalField k) η ((x, y) + (s, 0)) ≤ (reciprocalFrame k).slip (reciprocalField k) η (x, y) := by
  have hN : NativeP (2 * (k : ℤ) + 3) (x, y) := by
    unfold NativeP; left; dsimp only; omega
  have hsign := retained_sign_sum2 k η x y s hsum hy hx (retention_horiz k η x y s hη hN (by omega) hpol)
  apply slip_edge_le (reciprocalField k) (reciprocalFrame k) η (x, y) (s, 0)
  rw [smul_shortShift_recip k η]
  have e1 : (x, y) + (-2 * η, 0) = (x - 2 * η, y) := by ext <;> (simp; try ring)
  rw [e1]
  exact diagLow_D_horiz k η x y s hη hs hsum hy hx hsign

/-- **Lower-left diagonal, horizontal price on the policy edge (sum 2).** -/
theorem price_low2_h (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hs : s = 1 ∨ s = -1)
    (hsum : x + y = 2) (hy : 1 ≤ y) (hx : 6 - (2 * (k : ℤ) + 3) ≤ x)
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, y) ((x, y) + (s, 0))) :
    (reciprocalFrame k).price (reciprocalField k) ((x, y) + (s, 0)) ≤ (reciprocalFrame k).price (reciprocalField k) (x, y) := by
  have hN : NativeP (2 * (k : ℤ) + 3) (x, y) := by
    unfold NativeP; left; dsimp only; omega
  have hsign := retained_sign_sum2 k η x y s hsum hy hx (retention_horiz k η x y s hη hN (by omega) hpol)
  apply price_edge_le k (reciprocalField k) (x, y) (s, 0)
  have e1 : (x, y) - (1, -1) = (x - 1, y + 1) := by ext <;> (simp; try ring)
  rw [e1]
  exact diagLow_P_horiz k x y s hs hsum hy hx hsign

/-- **Lower-left diagonal, horizontal chain on the policy edge (sum 2).** -/
theorem chain_low2_h (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hs : s = 1 ∨ s = -1)
    (hsum : x + y = 2) (hy : 1 ≤ y) (hx : 6 - (2 * (k : ℤ) + 3) ≤ x)
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, y) ((x, y) + (s, 0))) :
    (reciprocalFrame k).chainPotential (reciprocalField k) η ((x, y) + (s, 0)) ≤
      (reciprocalFrame k).chainPotential (reciprocalField k) η (x, y) := by
  have hN : NativeP (2 * (k : ℤ) + 3) (x, y) := by
    unfold NativeP; left; dsimp only; omega
  have hsign := retained_sign_sum2 k η x y s hsum hy hx (retention_horiz k η x y s hη hN (by omega) hpol)
  apply chain_edge_le k (reciprocalField k) η (x, y) (s, 0)
  rw [smul_shortShift_recip k η]
  have e2 : (x, y) + (-2 * η, 0) - (1, -1) = (x - 2 * η - 1, y + 1) := by ext <;> (simp; try ring)
  rw [e2]
  exact diagLow_Phi_horiz k η x y s hη hs hsum hy hx hsign

/-- **Lower-left diagonal, vertical slip on the sum-3 edges (black centres).** -/
theorem slip_low3_v (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hs : s = 1 ∨ s = -1)
    (hsum : x + y = 3) (hy : 1 ≤ y) (hx : 6 - (2 * (k : ℤ) + 3) ≤ x) :
    (reciprocalFrame k).slip (reciprocalField k) η ((x, y) + (0, s)) ≤ (reciprocalFrame k).slip (reciprocalField k) η (x, y) := by
  apply slip_edge_le (reciprocalField k) (reciprocalFrame k) η (x, y) (0, s)
  rw [smul_shortShift_recip k η]
  have e1 : (x, y) + (-2 * η, 0) = (x - 2 * η, y) := by ext <;> (simp; try ring)
  rw [e1]
  exact diagLow3_D_vert k η x y s hη hs hsum hy hx

/-- **Lower-left diagonal, vertical price on the sum-3 edges.** -/
theorem price_low3_v (k : ℕ) (x y s : ℤ) (hs : s = 1 ∨ s = -1) (hsum : x + y = 3) (hy : 1 ≤ y)
    (hx : 6 - (2 * (k : ℤ) + 3) ≤ x) :
    (reciprocalFrame k).price (reciprocalField k) ((x, y) + (0, s)) ≤ (reciprocalFrame k).price (reciprocalField k) (x, y) := by
  apply price_edge_le k (reciprocalField k) (x, y) (0, s)
  have e1 : (x, y) - (1, -1) = (x - 1, y + 1) := by ext <;> (simp; try ring)
  rw [e1]
  exact diagLow3_P_vert k x y s hs hsum hy hx

/-- **Lower-left diagonal, vertical chain on the sum-3 edges.** -/
theorem chain_low3_v (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hs : s = 1 ∨ s = -1)
    (hsum : x + y = 3) (hy : 1 ≤ y) (hx : 6 - (2 * (k : ℤ) + 3) ≤ x) :
    (reciprocalFrame k).chainPotential (reciprocalField k) η ((x, y) + (0, s)) ≤
      (reciprocalFrame k).chainPotential (reciprocalField k) η (x, y) := by
  apply chain_edge_le k (reciprocalField k) η (x, y) (0, s)
  rw [smul_shortShift_recip k η]
  have e2 : (x, y) + (-2 * η, 0) - (1, -1) = (x - 2 * η - 1, y + 1) := by ext <;> (simp; try ring)
  rw [e2]
  exact diagLow3_Phi_vert k η x y s hη hs hsum hy hx

/-- **Lower-left diagonal, vertical slip on the retained sum-1 edge.** -/
theorem slip_low1_v (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1)
    (hN : NativeP (2 * (k : ℤ) + 3) (x, y)) (hsum : x + y = 1) (hy : 1 ≤ y)
    (hx : 6 - (2 * (k : ℤ) + 3) ≤ x)
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, y) ((x, y) + (0, s))) :
    (reciprocalFrame k).slip (reciprocalField k) η ((x, y) + (0, s)) ≤ (reciprocalFrame k).slip (reciprocalField k) η (x, y) := by
  have hsgn := retention_vert1 k η x y s hη hN hsum hy hpol
  apply slip_edge_le (reciprocalField k) (reciprocalFrame k) η (x, y) (0, s)
  rw [smul_shortShift_recip k η]
  have e1 : (x, y) + (-2 * η, 0) = (x - 2 * η, y) := by ext <;> (simp; try ring)
  rw [e1]
  exact diagLow1_D_vert k η x y s hη hsgn hsum hy hx

/-- **Lower-left diagonal, vertical price on the retained sum-1 edge.** -/
theorem price_low1_v (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1)
    (hN : NativeP (2 * (k : ℤ) + 3) (x, y)) (hsum : x + y = 1) (hy : 1 ≤ y)
    (hx : 6 - (2 * (k : ℤ) + 3) ≤ x)
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, y) ((x, y) + (0, s))) :
    (reciprocalFrame k).price (reciprocalField k) ((x, y) + (0, s)) ≤ (reciprocalFrame k).price (reciprocalField k) (x, y) := by
  have hsgn := retention_vert1 k η x y s hη hN hsum hy hpol
  apply price_edge_le k (reciprocalField k) (x, y) (0, s)
  have e1 : (x, y) - (1, -1) = (x - 1, y + 1) := by ext <;> (simp; try ring)
  rw [e1]
  exact diagLow1_P_vert k η x y s hη hsgn hsum hy hx

/-- **Lower-left diagonal, vertical chain on the retained sum-1 edge.** -/
theorem chain_low1_v (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1)
    (hN : NativeP (2 * (k : ℤ) + 3) (x, y)) (hsum : x + y = 1) (hy : 1 ≤ y)
    (hx : 6 - (2 * (k : ℤ) + 3) ≤ x)
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, y) ((x, y) + (0, s))) :
    (reciprocalFrame k).chainPotential (reciprocalField k) η ((x, y) + (0, s)) ≤
      (reciprocalFrame k).chainPotential (reciprocalField k) η (x, y) := by
  have hsgn := retention_vert1 k η x y s hη hN hsum hy hpol
  apply chain_edge_le k (reciprocalField k) η (x, y) (0, s)
  rw [smul_shortShift_recip k η]
  have e2 : (x, y) + (-2 * η, 0) - (1, -1) = (x - 2 * η - 1, y + 1) := by ext <;> (simp; try ring)
  rw [e2]
  exact diagLow1_Phi_vert k η x y s hη hsgn hsum hy hx

/-- The vertical increment at a site whose `(-U)`-translate carries the vertical step: `vG (b - 1) s`. -/
theorem incr_vert_negU (k : ℕ) (s a b : ℤ) (hs : s = 1 ∨ s = -1)
    (h0 : (a - (2 * (k : ℤ) + 3), b - 1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites)
    (h1 : (a - (2 * (k : ℤ) + 3), b - 1 + s) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites)
    (c0 : ¬ ((a - (2 * (k : ℤ) + 3) = 0 ∧ b - 1 = 0) ∨ (a - (2 * (k : ℤ) + 3) = 2 ∧ b - 1 = (2 * (k : ℤ) + 3) + 1)))
    (c1 : ¬ ((a - (2 * (k : ℤ) + 3) = 0 ∧ b - 1 + s = 0) ∨ (a - (2 * (k : ℤ) + 3) = 2 ∧ b - 1 + s = (2 * (k : ℤ) + 3) + 1))) :
    incr (reciprocalField k) (0, s) (a, b) = vG (b - 1) s := by
  have key := incr_vert k s (a - (2 * (k : ℤ) + 3)) (b - 1) hs h0 h1 c0 c1
  have eA : (a - (2 * (k : ℤ) + 3), b - 1) + ((2 * (k : ℤ) + 3), 1) = (a, b) := by ext <;> (simp; try ring)
  have eB : (a - (2 * (k : ℤ) + 3), b - 1) + (0, s) + ((2 * (k : ℤ) + 3), 1) = (a, b) + (0, s) := by ext <;> (simp; try ring)
  have hA := reciprocalField_add_U k (a - (2 * (k : ℤ) + 3), b - 1)
  have hB := reciprocalField_add_U k ((a - (2 * (k : ℤ) + 3), b - 1) + (0, s))
  rw [eA] at hA
  rw [eB] at hB
  unfold incr at key ⊢
  rw [hA, hB]
  exact key

/-- Retained vertical steps on the sum-`d + 2` centres (the odd down step `OddDown`): `s = -eta`. -/
theorem retention_top (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1)
    (hN : NativeP (2 * (k : ℤ) + 3) (x, y)) (hsum : x + y = (2 * (k : ℤ) + 3) + 2) (hx : 2 ≤ x) (hxd : x ≤ (2 * (k : ℤ) + 3))
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, y) ((x, y) + (0, s))) :
    s = -η := by
  have hE : ¬ EvenSite (x, y) := by unfold EvenSite; dsimp only; omega
  have hw : laplacian (reciprocalField k) (x, y) = 0 := by
    rw [laplacian_reciprocal_native k hN, if_neg hE]
    dsimp only
    rw [if_neg]
    omega
  rw [ePolicy_white k η hη (x, y) ((x, y) + (0, s)) hw, selDisp_nativeRep k η hη hN] at hpol
  have e : (x, y) + (0, s) - (x, y) = (0, s) := by ext <;> (simp; try ring)
  rw [e] at hpol
  unfold selDisp at hpol
  rw [if_neg hE] at hpol
  split_ifs at hpol with hO <;> (try simp only [Prod.mk.injEq] at hpol) <;> (try dsimp only at hO) <;> omega

/-- **Upper-right diagonal, vertical slip (sum d + 2).** -/
theorem top_D_vert (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hsgn : s = -η)
    (hsum : x + y = (2 * (k : ℤ) + 3) + 2) (hx : 3 ≤ x) (hxd : x ≤ (2 * (k : ℤ) + 3)) :
    incr (reciprocalField k) (0, s) (x, y) ≤ incr (reciprocalField k) (0, s) (x - 2 * η, y) := by
  rcases hη with rfl | rfl
  · have hs' : s = -1 := by omega
    subst hs'
    have i1 := incr_vert k (-1) x y (by norm_num) (mem_raw_of_box k x y (by omega))
      (mem_raw_of_box k x (y + -1) (by omega)) (by omega) (by omega)
    have i2 := incr_vert k (-1) (x - 2 * 1) y (by norm_num) (mem_raw_of_box k (x - 2 * 1) y (by omega))
      (mem_raw_of_box k (x - 2 * 1) (y + -1) (by omega)) (by omega) (by omega)
    linarith [vG_neg_one y]
  · have hs' : s = 1 := by omega
    subst hs'
    have i1 := incr_vert_negU k 1 x y (by norm_num) (mem_raw_of_box k (x - (2 * (k : ℤ) + 3)) (y - 1) (by omega))
      (mem_raw_of_box k (x - (2 * (k : ℤ) + 3)) (y - 1 + 1) (by omega)) (by omega) (by omega)
    have i2 := incr_vert_negU k 1 (x - 2 * -1) y (by norm_num)
      (mem_raw_of_box k (x - 2 * -1 - (2 * (k : ℤ) + 3)) (y - 1) (by omega))
      (mem_raw_of_box k (x - 2 * -1 - (2 * (k : ℤ) + 3)) (y - 1 + 1) (by omega)) (by omega) (by omega)
    linarith [vG_one (y - 1)]

/-- **Upper-right diagonal, vertical price (sum d + 2).** -/
theorem top_P_vert (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hsgn : s = -η)
    (hsum : x + y = (2 * (k : ℤ) + 3) + 2) (hx : 3 ≤ x) (hxd : x ≤ (2 * (k : ℤ) + 3)) :
    incr (reciprocalField k) (0, s) (x, y) - incr (reciprocalField k) (0, s) (x - 1, y + 1) ≤ s := by
  rcases hη with rfl | rfl
  · have hs' : s = -1 := by omega
    subst hs'
    have i1 := incr_vert k (-1) x y (by norm_num) (mem_raw_of_box k x y (by omega))
      (mem_raw_of_box k x (y + -1) (by omega)) (by omega) (by omega)
    have i3 := incr_vert k (-1) (x - 1) (y + 1) (by norm_num) (mem_raw_of_box k (x - 1) (y + 1) (by omega))
      (mem_raw_of_box k (x - 1) (y + 1 + -1) (by omega)) (by omega) (by omega)
    linarith [vG_neg_one y, vG_neg_one (y + 1)]
  · have hs' : s = 1 := by omega
    subst hs'
    have i1 := incr_vert_negU k 1 x y (by norm_num) (mem_raw_of_box k (x - (2 * (k : ℤ) + 3)) (y - 1) (by omega))
      (mem_raw_of_box k (x - (2 * (k : ℤ) + 3)) (y - 1 + 1) (by omega)) (by omega) (by omega)
    have i3 := incr_vert_negU k 1 (x - 1) (y + 1) (by norm_num)
      (mem_raw_of_box k (x - 1 - (2 * (k : ℤ) + 3)) (y + 1 - 1) (by omega))
      (mem_raw_of_box k (x - 1 - (2 * (k : ℤ) + 3)) (y + 1 - 1 + 1) (by omega)) (by omega) (by omega)
    linarith [vG_one (y - 1), vG_one (y + 1 - 1), vG_one y]

/-- **Upper-right diagonal, vertical chain (sum d + 2).** -/
theorem top_Phi_vert (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hsgn : s = -η)
    (hsum : x + y = (2 * (k : ℤ) + 3) + 2) (hx : 3 ≤ x) (hxd : x ≤ (2 * (k : ℤ) + 3)) :
    incr (reciprocalField k) (0, s) (x, y) - incr (reciprocalField k) (0, s) (x - 2 * η - 1, y + 1) ≤ s := by
  rcases hη with rfl | rfl
  · have hs' : s = -1 := by omega
    subst hs'
    have i1 := incr_vert k (-1) x y (by norm_num) (mem_raw_of_box k x y (by omega))
      (mem_raw_of_box k x (y + -1) (by omega)) (by omega) (by omega)
    have i4 := incr_vert k (-1) (x - 2 * 1 - 1) (y + 1) (by norm_num)
      (mem_raw_of_box k (x - 2 * 1 - 1) (y + 1) (by omega))
      (mem_raw_of_box k (x - 2 * 1 - 1) (y + 1 + -1) (by omega)) (by omega) (by omega)
    linarith [vG_neg_one y, vG_neg_one (y + 1)]
  · have hs' : s = 1 := by omega
    subst hs'
    have i1 := incr_vert_negU k 1 x y (by norm_num) (mem_raw_of_box k (x - (2 * (k : ℤ) + 3)) (y - 1) (by omega))
      (mem_raw_of_box k (x - (2 * (k : ℤ) + 3)) (y - 1 + 1) (by omega)) (by omega) (by omega)
    have i4 := incr_vert_negU k 1 (x - 2 * -1 - 1) (y + 1) (by norm_num)
      (mem_raw_of_box k (x - 2 * -1 - 1 - (2 * (k : ℤ) + 3)) (y + 1 - 1) (by omega))
      (mem_raw_of_box k (x - 2 * -1 - 1 - (2 * (k : ℤ) + 3)) (y + 1 - 1 + 1) (by omega)) (by omega) (by omega)
    linarith [vG_one (y - 1), vG_one (y + 1 - 1), vG_one y]

/-- **Upper-right diagonal (sum d + 2), slip on the policy edge.** -/
theorem slip_top_v (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1)
    (hsum : x + y = (2 * (k : ℤ) + 3) + 2) (hx : 3 ≤ x) (hxd : x ≤ (2 * (k : ℤ) + 3))
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, y) ((x, y) + (0, s))) :
    (reciprocalFrame k).slip (reciprocalField k) η ((x, y) + (0, s)) ≤ (reciprocalFrame k).slip (reciprocalField k) η (x, y) := by
  have hN : NativeP (2 * (k : ℤ) + 3) (x, y) := by
    unfold NativeP; left; dsimp only; omega
  have hsgn := retention_top k η x y s hη hN hsum (by omega) hxd hpol
  apply slip_edge_le (reciprocalField k) (reciprocalFrame k) η (x, y) (0, s)
  rw [smul_shortShift_recip k η]
  have e1 : (x, y) + (-2 * η, 0) = (x - 2 * η, y) := by ext <;> (simp; try ring)
  rw [e1]
  exact top_D_vert k η x y s hη hsgn hsum hx hxd

/-- **Upper-right diagonal (sum d + 2), price on the policy edge.** -/
theorem price_top_v (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1)
    (hsum : x + y = (2 * (k : ℤ) + 3) + 2) (hx : 3 ≤ x) (hxd : x ≤ (2 * (k : ℤ) + 3))
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, y) ((x, y) + (0, s))) :
    (reciprocalFrame k).price (reciprocalField k) ((x, y) + (0, s)) ≤ (reciprocalFrame k).price (reciprocalField k) (x, y) := by
  have hN : NativeP (2 * (k : ℤ) + 3) (x, y) := by
    unfold NativeP; left; dsimp only; omega
  have hsgn := retention_top k η x y s hη hN hsum (by omega) hxd hpol
  apply price_edge_le k (reciprocalField k) (x, y) (0, s)
  have e1 : (x, y) - (1, -1) = (x - 1, y + 1) := by ext <;> (simp; try ring)
  rw [e1]
  exact top_P_vert k η x y s hη hsgn hsum hx hxd

/-- **Upper-right diagonal (sum d + 2), chain on the policy edge.** -/
theorem chain_top_v (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1)
    (hsum : x + y = (2 * (k : ℤ) + 3) + 2) (hx : 3 ≤ x) (hxd : x ≤ (2 * (k : ℤ) + 3))
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, y) ((x, y) + (0, s))) :
    (reciprocalFrame k).chainPotential (reciprocalField k) η ((x, y) + (0, s)) ≤
      (reciprocalFrame k).chainPotential (reciprocalField k) η (x, y) := by
  have hN : NativeP (2 * (k : ℤ) + 3) (x, y) := by
    unfold NativeP; left; dsimp only; omega
  have hsgn := retention_top k η x y s hη hN hsum (by omega) hxd hpol
  apply chain_edge_le k (reciprocalField k) η (x, y) (0, s)
  rw [smul_shortShift_recip k η]
  have e2 : (x, y) + (-2 * η, 0) - (1, -1) = (x - 2 * η - 1, y + 1) := by ext <;> (simp; try ring)
  rw [e2]
  exact top_Phi_vert k η x y s hη hsgn hsum hx hxd

/-- **Sum d, black centres, vertical slip (both steps retained).** -/
theorem sumd_D_vert (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hs : s = 1 ∨ s = -1)
    (hsum : x + y = (2 * (k : ℤ) + 3)) (hx : 3 ≤ x) (hy : 2 ≤ y) :
    incr (reciprocalField k) (0, s) (x, y) ≤ incr (reciprocalField k) (0, s) (x - 2 * η, y) := by
  rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
  · have i1 := incr_vert k 1 x y (by norm_num) (mem_raw_of_box k x y (by omega))
      (mem_raw_of_box k x (y + 1) (by omega)) (by omega) (by omega)
    have i2 := incr_vert k 1 (x - 2 * 1) y (by norm_num) (mem_raw_of_box k (x - 2 * 1) y (by omega))
      (mem_raw_of_box k (x - 2 * 1) (y + 1) (by omega)) (by omega) (by omega)
    linarith [vG_one y]
  · have i1 := incr_vert k (-1) x y (by norm_num) (mem_raw_of_box k x y (by omega))
      (mem_raw_of_box k x (y + -1) (by omega)) (by omega) (by omega)
    have i2 := incr_vert k (-1) (x - 2 * 1) y (by norm_num) (mem_raw_of_box k (x - 2 * 1) y (by omega))
      (mem_raw_of_box k (x - 2 * 1) (y + -1) (by omega)) (by omega) (by omega)
    linarith [vG_neg_one y]
  · have i1 := incr_vert k 1 x y (by norm_num) (mem_raw_of_box k x y (by omega))
      (mem_raw_of_box k x (y + 1) (by omega)) (by omega) (by omega)
    have i2 := incr_vert_negU k 1 (x - 2 * -1) y (by norm_num)
      (mem_raw_of_box k (x - 2 * -1 - (2 * (k : ℤ) + 3)) (y - 1) (by omega))
      (mem_raw_of_box k (x - 2 * -1 - (2 * (k : ℤ) + 3)) (y - 1 + 1) (by omega)) (by omega) (by omega)
    linarith [vG_one y, vG_one (y - 1)]
  · have i1 := incr_vert k (-1) x y (by norm_num) (mem_raw_of_box k x y (by omega))
      (mem_raw_of_box k x (y + -1) (by omega)) (by omega) (by omega)
    have i2 := incr_vert k (-1) (x - 2 * -1) y (by norm_num) (mem_raw_of_box k (x - 2 * -1) y (by omega))
      (mem_raw_of_box k (x - 2 * -1) (y + -1) (by omega)) (by omega) (by omega)
    linarith [vG_neg_one y]

/-- **Sum d, black centres, vertical price.** -/
theorem sumd_P_vert (k : ℕ) (x y s : ℤ) (hs : s = 1 ∨ s = -1) (hsum : x + y = (2 * (k : ℤ) + 3)) (hx : 3 ≤ x) (hy : 2 ≤ y) :
    incr (reciprocalField k) (0, s) (x, y) - incr (reciprocalField k) (0, s) (x - 1, y + 1) ≤ s := by
  rcases hs with rfl | rfl
  · have i1 := incr_vert k 1 x y (by norm_num) (mem_raw_of_box k x y (by omega))
      (mem_raw_of_box k x (y + 1) (by omega)) (by omega) (by omega)
    have i3 := incr_vert k 1 (x - 1) (y + 1) (by norm_num) (mem_raw_of_box k (x - 1) (y + 1) (by omega))
      (mem_raw_of_box k (x - 1) (y + 1 + 1) (by omega)) (by omega) (by omega)
    linarith [vG_P y 1 (by norm_num)]
  · have i1 := incr_vert k (-1) x y (by norm_num) (mem_raw_of_box k x y (by omega))
      (mem_raw_of_box k x (y + -1) (by omega)) (by omega) (by omega)
    have i3 := incr_vert k (-1) (x - 1) (y + 1) (by norm_num) (mem_raw_of_box k (x - 1) (y + 1) (by omega))
      (mem_raw_of_box k (x - 1) (y + 1 + -1) (by omega)) (by omega) (by omega)
    linarith [vG_P y (-1) (by norm_num)]

/-- **Sum d, black centres, vertical chain.** -/
theorem sumd_Phi_vert (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hs : s = 1 ∨ s = -1)
    (hsum : x + y = (2 * (k : ℤ) + 3)) (hx : 3 ≤ x) (hy : 2 ≤ y) :
    incr (reciprocalField k) (0, s) (x, y) - incr (reciprocalField k) (0, s) (x - 2 * η - 1, y + 1) ≤ s := by
  rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
  · have i1 := incr_vert k 1 x y (by norm_num) (mem_raw_of_box k x y (by omega))
      (mem_raw_of_box k x (y + 1) (by omega)) (by omega) (by omega)
    have i4 := incr_vert k 1 (x - 2 * 1 - 1) (y + 1) (by norm_num)
      (mem_raw_of_box k (x - 2 * 1 - 1) (y + 1) (by omega)) (mem_raw_of_box k (x - 2 * 1 - 1) (y + 1 + 1) (by omega))
      (by omega) (by omega)
    linarith [vG_P y 1 (by norm_num)]
  · have i1 := incr_vert k (-1) x y (by norm_num) (mem_raw_of_box k x y (by omega))
      (mem_raw_of_box k x (y + -1) (by omega)) (by omega) (by omega)
    have i4 := incr_vert k (-1) (x - 2 * 1 - 1) (y + 1) (by norm_num)
      (mem_raw_of_box k (x - 2 * 1 - 1) (y + 1) (by omega)) (mem_raw_of_box k (x - 2 * 1 - 1) (y + 1 + -1) (by omega))
      (by omega) (by omega)
    linarith [vG_P y (-1) (by norm_num)]
  · have i1 := incr_vert k 1 x y (by norm_num) (mem_raw_of_box k x y (by omega))
      (mem_raw_of_box k x (y + 1) (by omega)) (by omega) (by omega)
    have i4 := incr_vert_negU k 1 (x - 2 * -1 - 1) (y + 1) (by norm_num)
      (mem_raw_of_box k (x - 2 * -1 - 1 - (2 * (k : ℤ) + 3)) (y + 1 - 1) (by omega))
      (mem_raw_of_box k (x - 2 * -1 - 1 - (2 * (k : ℤ) + 3)) (y + 1 - 1 + 1) (by omega)) (by omega) (by omega)
    linarith [vG_one y, vG_one (y + 1 - 1)]
  · have i1 := incr_vert k (-1) x y (by norm_num) (mem_raw_of_box k x y (by omega))
      (mem_raw_of_box k x (y + -1) (by omega)) (by omega) (by omega)
    have i4 := incr_vert k (-1) (x - 2 * -1 - 1) (y + 1) (by norm_num)
      (mem_raw_of_box k (x - 2 * -1 - 1) (y + 1) (by omega)) (mem_raw_of_box k (x - 2 * -1 - 1) (y + 1 + -1) (by omega))
      (by omega) (by omega)
    linarith [vG_P y (-1) (by norm_num)]

/-- **Sum d (black centres), slip on the policy edge.** -/
theorem slip_sumd_v (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hs : s = 1 ∨ s = -1)
    (hsum : x + y = (2 * (k : ℤ) + 3)) (hx : 3 ≤ x) (hy : 2 ≤ y) :
    (reciprocalFrame k).slip (reciprocalField k) η ((x, y) + (0, s)) ≤ (reciprocalFrame k).slip (reciprocalField k) η (x, y) := by
  apply slip_edge_le (reciprocalField k) (reciprocalFrame k) η (x, y) (0, s)
  rw [smul_shortShift_recip k η]
  have e1 : (x, y) + (-2 * η, 0) = (x - 2 * η, y) := by ext <;> (simp; try ring)
  rw [e1]
  exact sumd_D_vert k η x y s hη hs hsum hx hy

/-- **Sum d (black centres), price on the policy edge.** -/
theorem price_sumd_v (k : ℕ) (x y s : ℤ) (hs : s = 1 ∨ s = -1) (hsum : x + y = (2 * (k : ℤ) + 3)) (hx : 3 ≤ x) (hy : 2 ≤ y) :
    (reciprocalFrame k).price (reciprocalField k) ((x, y) + (0, s)) ≤ (reciprocalFrame k).price (reciprocalField k) (x, y) := by
  apply price_edge_le k (reciprocalField k) (x, y) (0, s)
  have e1 : (x, y) - (1, -1) = (x - 1, y + 1) := by ext <;> (simp; try ring)
  rw [e1]
  exact sumd_P_vert k x y s hs hsum hx hy

/-- **Sum d (black centres), chain on the policy edge.** -/
theorem chain_sumd_v (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1) (hs : s = 1 ∨ s = -1)
    (hsum : x + y = (2 * (k : ℤ) + 3)) (hx : 3 ≤ x) (hy : 2 ≤ y) :
    (reciprocalFrame k).chainPotential (reciprocalField k) η ((x, y) + (0, s)) ≤
      (reciprocalFrame k).chainPotential (reciprocalField k) η (x, y) := by
  apply chain_edge_le k (reciprocalField k) η (x, y) (0, s)
  rw [smul_shortShift_recip k η]
  have e2 : (x, y) + (-2 * η, 0) - (1, -1) = (x - 2 * η - 1, y + 1) := by ext <;> (simp; try ring)
  rw [e2]
  exact sumd_Phi_vert k η x y s hη hs hsum hx hy

/-- The horizontal increment at a site whose minus-`U` translate carries the step: `hG` at the translate. -/
theorem incr_hG_negU (k : ℕ) (s a b : ℤ)
    (hpt : (a - (2 * (k : ℤ) + 3) + s, b - 1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites)
    (hu : (a - (2 * (k : ℤ) + 3), b - 1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites) :
    incr (reciprocalField k) (s, 0) (a, b) = hG (2 * (k : ℤ) + 3) (a - (2 * (k : ℤ) + 3)) (b - 1) s := by
  have key := incr_hG k s (a - (2 * (k : ℤ) + 3)) (b - 1) hpt hu
  have eA : (a - (2 * (k : ℤ) + 3), b - 1) + ((2 * (k : ℤ) + 3), 1) = (a, b) := by ext <;> (simp; try ring)
  have eB : (a - (2 * (k : ℤ) + 3), b - 1) + (s, 0) + ((2 * (k : ℤ) + 3), 1) = (a, b) + (s, 0) := by ext <;> (simp; try ring)
  have hA := reciprocalField_add_U k (a - (2 * (k : ℤ) + 3), b - 1)
  have hB := reciprocalField_add_U k ((a - (2 * (k : ℤ) + 3), b - 1) + (s, 0))
  rw [eA] at hA
  rw [eB] at hB
  unfold incr at key ⊢
  rw [hA, hB]
  exact key

/-- Retained horizontal step on the sum-`d + 1` centres with `2 <= x <= d - 1`: the step is `+1`. -/
theorem retention_sumd1 (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1)
    (hN : NativeP (2 * (k : ℤ) + 3) (x, y)) (hsum : x + y = (2 * (k : ℤ) + 3) + 1) (hx : 2 ≤ x)
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, y) ((x, y) + (s, 0))) :
    s = 1 := by
  have hE : EvenSite (x, y) := by unfold EvenSite; dsimp only; omega
  have hw : laplacian (reciprocalField k) (x, y) = 0 := by
    rw [laplacian_reciprocal_native k hN, if_pos hE]
    dsimp only
    rw [if_neg]
    omega
  rw [ePolicy_white k η hη (x, y) ((x, y) + (s, 0)) hw, selDisp_nativeRep k η hη hN] at hpol
  have e : (x, y) + (s, 0) - (x, y) = (s, 0) := by ext <;> (simp; try ring)
  rw [e] at hpol
  unfold selDisp at hpol
  rw [if_pos hE] at hpol
  split_ifs at hpol <;> (try simp only [Prod.mk.injEq] at *) <;> omega

/-- **Sum d + 1 (white centres, the step `+1`), horizontal slip.** -/
theorem sumd1_D (k : ℕ) (η x y : ℤ) (hη : η = 1 ∨ η = -1) (hsum : x + y = (2 * (k : ℤ) + 3) + 1) (hx : 2 ≤ x) (hy : 2 ≤ y) :
    incr (reciprocalField k) (1, 0) (x, y) ≤ incr (reciprocalField k) (1, 0) (x - 2 * η, y) := by
  have i1 := incr_hG k 1 x y (mem_raw_of_box k (x + 1) y (by omega)) (mem_raw_of_box k x y (by omega))
  rcases hη with rfl | rfl
  · have i2 := incr_hG k 1 (x - 2 * 1) y (mem_raw_of_box k (x - 2 * 1 + 1) y (by omega))
      (mem_raw_of_box k (x - 2 * 1) y (by omega))
    rw [i1, i2]
    unfold hG
    rw [if_neg (not_stairCorner _ (x + 1) y (by omega)), if_neg (not_stairCorner _ x y (by omega)),
      if_neg (not_stairCorner _ (x - 2 * 1 + 1) y (by omega)), if_neg (not_stairCorner _ (x - 2 * 1) y (by omega))]
    omega
  · have i2 := incr_hG_negU k 1 (x - 2 * -1) y
      (mem_raw_of_box k (x - 2 * -1 - (2 * (k : ℤ) + 3) + 1) (y - 1) (by omega))
      (mem_raw_of_box k (x - 2 * -1 - (2 * (k : ℤ) + 3)) (y - 1) (by omega))
    rw [i1, i2]
    unfold hG
    rw [if_neg (not_stairCorner _ (x + 1) y (by omega)), if_neg (not_stairCorner _ x y (by omega)),
      if_neg (not_stairCorner _ (x - 2 * -1 - (2 * (k : ℤ) + 3) + 1) (y - 1) (by omega)),
      if_neg (not_stairCorner _ (x - 2 * -1 - (2 * (k : ℤ) + 3)) (y - 1) (by omega))]
    omega

/-- **Sum d + 1, horizontal price (the step `+1`).** -/
theorem sumd1_P (k : ℕ) (x y : ℤ) (hsum : x + y = (2 * (k : ℤ) + 3) + 1) (hx : 2 ≤ x) (hy : 2 ≤ y) :
    incr (reciprocalField k) (1, 0) (x, y) - incr (reciprocalField k) (1, 0) (x - 1, y + 1) ≤ 0 := by
  have i1 := incr_hG k 1 x y (mem_raw_of_box k (x + 1) y (by omega)) (mem_raw_of_box k x y (by omega))
  have i3 := incr_hG k 1 (x - 1) (y + 1) (mem_raw_of_box k (x - 1 + 1) (y + 1) (by omega))
    (mem_raw_of_box k (x - 1) (y + 1) (by omega))
  rw [i1, i3]
  unfold hG
  rw [if_neg (not_stairCorner _ (x + 1) y (by omega)), if_neg (not_stairCorner _ x y (by omega)),
    if_neg (not_stairCorner _ (x - 1 + 1) (y + 1) (by omega)), if_neg (not_stairCorner _ (x - 1) (y + 1) (by omega))]
  omega

/-- **Sum d + 1, horizontal chain (the step `+1`).** -/
theorem sumd1_Phi (k : ℕ) (η x y : ℤ) (hη : η = 1 ∨ η = -1) (hsum : x + y = (2 * (k : ℤ) + 3) + 1) (hx : 2 ≤ x) (hy : 2 ≤ y) :
    incr (reciprocalField k) (1, 0) (x, y) - incr (reciprocalField k) (1, 0) (x - 2 * η - 1, y + 1) ≤ 0 := by
  have i1 := incr_hG k 1 x y (mem_raw_of_box k (x + 1) y (by omega)) (mem_raw_of_box k x y (by omega))
  rcases hη with rfl | rfl
  · have i4 := incr_hG k 1 (x - 2 * 1 - 1) (y + 1) (mem_raw_of_box k (x - 2 * 1 - 1 + 1) (y + 1) (by omega))
      (mem_raw_of_box k (x - 2 * 1 - 1) (y + 1) (by omega))
    rw [i1, i4]
    unfold hG
    rw [if_neg (not_stairCorner _ (x + 1) y (by omega)), if_neg (not_stairCorner _ x y (by omega)),
      if_neg (not_stairCorner _ (x - 2 * 1 - 1 + 1) (y + 1) (by omega)),
      if_neg (not_stairCorner _ (x - 2 * 1 - 1) (y + 1) (by omega))]
    omega
  · have i4 := incr_hG_negU k 1 (x - 2 * -1 - 1) (y + 1)
      (mem_raw_of_box k (x - 2 * -1 - 1 - (2 * (k : ℤ) + 3) + 1) (y + 1 - 1) (by omega))
      (mem_raw_of_box k (x - 2 * -1 - 1 - (2 * (k : ℤ) + 3)) (y + 1 - 1) (by omega))
    rw [i1, i4]
    unfold hG
    rw [if_neg (not_stairCorner _ (x + 1) y (by omega)), if_neg (not_stairCorner _ x y (by omega)),
      if_neg (not_stairCorner _ (x - 2 * -1 - 1 - (2 * (k : ℤ) + 3) + 1) (y + 1 - 1) (by omega)),
      if_neg (not_stairCorner _ (x - 2 * -1 - 1 - (2 * (k : ℤ) + 3)) (y + 1 - 1) (by omega))]
    omega

/-- **Sum d + 1, horizontal slip on the policy edge.** -/
theorem slip_sumd1_h (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1)
    (hsum : x + y = (2 * (k : ℤ) + 3) + 1) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, y) ((x, y) + (s, 0))) :
    (reciprocalFrame k).slip (reciprocalField k) η ((x, y) + (s, 0)) ≤ (reciprocalFrame k).slip (reciprocalField k) η (x, y) := by
  have hN : NativeP (2 * (k : ℤ) + 3) (x, y) := by
    unfold NativeP; left; dsimp only; omega
  have hsgn := retention_sumd1 k η x y s hη hN hsum hx hpol
  subst hsgn
  apply slip_edge_le (reciprocalField k) (reciprocalFrame k) η (x, y) (1, 0)
  rw [smul_shortShift_recip k η]
  have e1 : (x, y) + (-2 * η, 0) = (x - 2 * η, y) := by ext <;> (simp; try ring)
  rw [e1]
  exact sumd1_D k η x y hη hsum hx hy

/-- **Sum d + 1, horizontal price on the policy edge.** -/
theorem price_sumd1_h (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1)
    (hsum : x + y = (2 * (k : ℤ) + 3) + 1) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, y) ((x, y) + (s, 0))) :
    (reciprocalFrame k).price (reciprocalField k) ((x, y) + (s, 0)) ≤ (reciprocalFrame k).price (reciprocalField k) (x, y) := by
  have hN : NativeP (2 * (k : ℤ) + 3) (x, y) := by
    unfold NativeP; left; dsimp only; omega
  have hsgn := retention_sumd1 k η x y s hη hN hsum hx hpol
  subst hsgn
  apply price_edge_le k (reciprocalField k) (x, y) (1, 0)
  have e1 : (x, y) - (1, -1) = (x - 1, y + 1) := by ext <;> (simp; try ring)
  rw [e1]
  exact sumd1_P k x y hsum hx hy

/-- **Sum d + 1, horizontal chain on the policy edge.** -/
theorem chain_sumd1_h (k : ℕ) (η x y s : ℤ) (hη : η = 1 ∨ η = -1)
    (hsum : x + y = (2 * (k : ℤ) + 3) + 1) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, y) ((x, y) + (s, 0))) :
    (reciprocalFrame k).chainPotential (reciprocalField k) η ((x, y) + (s, 0)) ≤
      (reciprocalFrame k).chainPotential (reciprocalField k) η (x, y) := by
  have hN : NativeP (2 * (k : ℤ) + 3) (x, y) := by
    unfold NativeP; left; dsimp only; omega
  have hsgn := retention_sumd1 k η x y s hη hN hsum hx hpol
  subst hsgn
  apply chain_edge_le k (reciprocalField k) η (x, y) (1, 0)
  rw [smul_shortShift_recip k η]
  have e2 : (x, y) + (-2 * η, 0) - (1, -1) = (x - 2 * η - 1, y + 1) := by ext <;> (simp; try ring)
  rw [e2]
  exact sumd1_Phi k η x y hη hsum hx hy

/-- **Bottom row, even centres (horizontal step `+1`), slip.** -/
theorem bot_E_D (k : ℕ) (η x : ℤ) (hη : η = 1 ∨ η = -1) (hx : 4 ≤ x) (hxd : x ≤ (2 * (k : ℤ) + 3) - 3) :
    incr (reciprocalField k) (1, 0) (x, 0) ≤ incr (reciprocalField k) (1, 0) (x - 2 * η, 0) := by
  have i1 := incr_hG k 1 x 0 (mem_raw_of_box k (x + 1) 0 (by omega)) (mem_raw_of_box k x 0 (by omega))
  rcases hη with rfl | rfl
  · have i2 := incr_hG k 1 (x - 2 * 1) 0 (mem_raw_of_box k (x - 2 * 1 + 1) 0 (by omega))
      (mem_raw_of_box k (x - 2 * 1) 0 (by omega))
    rw [i1, i2]
    unfold hG
    rw [if_neg (not_stairCorner _ (x + 1) 0 (by omega)), if_neg (not_stairCorner _ x 0 (by omega)),
      if_neg (not_stairCorner _ (x - 2 * 1 + 1) 0 (by omega)), if_neg (not_stairCorner _ (x - 2 * 1) 0 (by omega))]
    omega
  · have i2 := incr_hG k 1 (x - 2 * -1) 0 (mem_raw_of_box k (x - 2 * -1 + 1) 0 (by omega))
      (mem_raw_of_box k (x - 2 * -1) 0 (by omega))
    rw [i1, i2]
    unfold hG
    rw [if_neg (not_stairCorner _ (x + 1) 0 (by omega)), if_neg (not_stairCorner _ x 0 (by omega)),
      if_neg (not_stairCorner _ (x - 2 * -1 + 1) 0 (by omega)), if_neg (not_stairCorner _ (x - 2 * -1) 0 (by omega))]
    omega

/-- **Bottom row, even centres, price.** -/
theorem bot_E_P (k : ℕ) (x : ℤ) (hx : 4 ≤ x) (hxd : x ≤ (2 * (k : ℤ) + 3) - 3) :
    incr (reciprocalField k) (1, 0) (x, 0) - incr (reciprocalField k) (1, 0) (x - 1, 1) ≤ 0 := by
  have i1 := incr_hG k 1 x 0 (mem_raw_of_box k (x + 1) 0 (by omega)) (mem_raw_of_box k x 0 (by omega))
  have i3 := incr_hG k 1 (x - 1) 1 (mem_raw_of_box k (x - 1 + 1) 1 (by omega))
    (mem_raw_of_box k (x - 1) 1 (by omega))
  rw [i1, i3]
  unfold hG
  rw [if_neg (not_stairCorner _ (x + 1) 0 (by omega)), if_neg (not_stairCorner _ x 0 (by omega)),
    if_neg (not_stairCorner _ (x - 1 + 1) 1 (by omega)), if_neg (not_stairCorner _ (x - 1) 1 (by omega))]
  omega

/-- **Bottom row, even centres, chain.** -/
theorem bot_E_Phi (k : ℕ) (η x : ℤ) (hη : η = 1 ∨ η = -1) (hx : 4 ≤ x) (hxd : x ≤ (2 * (k : ℤ) + 3) - 3) :
    incr (reciprocalField k) (1, 0) (x, 0) - incr (reciprocalField k) (1, 0) (x - 2 * η - 1, 1) ≤ 0 := by
  have i1 := incr_hG k 1 x 0 (mem_raw_of_box k (x + 1) 0 (by omega)) (mem_raw_of_box k x 0 (by omega))
  rcases hη with rfl | rfl
  · have i4 := incr_hG k 1 (x - 2 * 1 - 1) 1 (mem_raw_of_box k (x - 2 * 1 - 1 + 1) 1 (by omega))
      (mem_raw_of_box k (x - 2 * 1 - 1) 1 (by omega))
    rw [i1, i4]
    unfold hG
    rw [if_neg (not_stairCorner _ (x + 1) 0 (by omega)), if_neg (not_stairCorner _ x 0 (by omega)),
      if_neg (not_stairCorner _ (x - 2 * 1 - 1 + 1) 1 (by omega)), if_neg (not_stairCorner _ (x - 2 * 1 - 1) 1 (by omega))]
    omega
  · have i4 := incr_hG k 1 (x - 2 * -1 - 1) 1 (mem_raw_of_box k (x - 2 * -1 - 1 + 1) 1 (by omega))
      (mem_raw_of_box k (x - 2 * -1 - 1) 1 (by omega))
    rw [i1, i4]
    unfold hG
    rw [if_neg (not_stairCorner _ (x + 1) 0 (by omega)), if_neg (not_stairCorner _ x 0 (by omega)),
      if_neg (not_stairCorner _ (x - 2 * -1 - 1 + 1) 1 (by omega)), if_neg (not_stairCorner _ (x - 2 * -1 - 1) 1 (by omega))]
    omega

/-- **Bottom row, odd centres (vertical step `+1`), slip.** -/
theorem bot_O_D (k : ℕ) (η x : ℤ) (hη : η = 1 ∨ η = -1) (hx : 3 ≤ x) (hxd : x ≤ (2 * (k : ℤ) + 3) - 2) :
    incr (reciprocalField k) (0, 1) (x, 0) ≤ incr (reciprocalField k) (0, 1) (x - 2 * η, 0) := by
  have i1 := incr_vert k 1 x 0 (by norm_num) (mem_raw_of_box k x 0 (by omega))
    (mem_raw_of_box k x (0 + 1) (by omega)) (by omega) (by omega)
  rcases hη with rfl | rfl
  · have i2 := incr_vert k 1 (x - 2 * 1) 0 (by norm_num) (mem_raw_of_box k (x - 2 * 1) 0 (by omega))
      (mem_raw_of_box k (x - 2 * 1) (0 + 1) (by omega)) (by omega) (by omega)
    rw [i1, i2]
  · have i2 := incr_vert k 1 (x - 2 * -1) 0 (by norm_num) (mem_raw_of_box k (x - 2 * -1) 0 (by omega))
      (mem_raw_of_box k (x - 2 * -1) (0 + 1) (by omega)) (by omega) (by omega)
    rw [i1, i2]

/-- **Bottom row, odd centres, price.** -/
theorem bot_O_P (k : ℕ) (x : ℤ) (hx : 3 ≤ x) (hxd : x ≤ (2 * (k : ℤ) + 3) - 2) :
    incr (reciprocalField k) (0, 1) (x, 0) - incr (reciprocalField k) (0, 1) (x - 1, 1) ≤ 1 := by
  have i1 := incr_vert k 1 x 0 (by norm_num) (mem_raw_of_box k x 0 (by omega))
    (mem_raw_of_box k x (0 + 1) (by omega)) (by omega) (by omega)
  have i3 := incr_vert k 1 (x - 1) 1 (by norm_num) (mem_raw_of_box k (x - 1) 1 (by omega))
    (mem_raw_of_box k (x - 1) (1 + 1) (by omega)) (by omega) (by omega)
  rw [i1, i3]
  linarith [vG_one 0, vG_one 1]

/-- **Bottom row, odd centres, chain.** -/
theorem bot_O_Phi (k : ℕ) (η x : ℤ) (hη : η = 1 ∨ η = -1) (hx : 3 ≤ x) (hxd : x ≤ (2 * (k : ℤ) + 3) - 2) :
    incr (reciprocalField k) (0, 1) (x, 0) - incr (reciprocalField k) (0, 1) (x - 2 * η - 1, 1) ≤ 1 := by
  have i1 := incr_vert k 1 x 0 (by norm_num) (mem_raw_of_box k x 0 (by omega))
    (mem_raw_of_box k x (0 + 1) (by omega)) (by omega) (by omega)
  rcases hη with rfl | rfl
  · have i4 := incr_vert k 1 (x - 2 * 1 - 1) 1 (by norm_num) (mem_raw_of_box k (x - 2 * 1 - 1) 1 (by omega))
      (mem_raw_of_box k (x - 2 * 1 - 1) (1 + 1) (by omega)) (by omega) (by omega)
    rw [i1, i4]
    linarith [vG_one 0, vG_one 1]
  · have i4 := incr_vert k 1 (x - 2 * -1 - 1) 1 (by norm_num) (mem_raw_of_box k (x - 2 * -1 - 1) 1 (by omega))
      (mem_raw_of_box k (x - 2 * -1 - 1) (1 + 1) (by omega)) (by omega) (by omega)
    rw [i1, i4]
    linarith [vG_one 0, vG_one 1]

/-- Retained horizontal step at an even bottom centre `(x, 0)`, `2 <= x`: the step is `+1` (the special row `y = 0`). -/
theorem retention_bot_even (k : ℕ) (η x s : ℤ) (hη : η = 1 ∨ η = -1)
    (hN : NativeP (2 * (k : ℤ) + 3) (x, 0)) (hpar : x % 2 = 0) (hx : 2 ≤ x)
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, 0) ((x, 0) + (s, 0))) :
    s = 1 := by
  have hE : EvenSite (x, 0) := by unfold EvenSite; dsimp only; omega
  have hw : laplacian (reciprocalField k) (x, 0) = 0 := by
    rw [laplacian_reciprocal_native k hN, if_pos hE]
    dsimp only
    rw [if_neg]
    omega
  rw [ePolicy_white k η hη (x, 0) ((x, 0) + (s, 0)) hw, selDisp_nativeRep k η hη hN] at hpol
  rw [add_sub_cancel_left] at hpol
  unfold selDisp at hpol
  rw [if_pos hE] at hpol
  split_ifs at hpol <;> (try simp only [Prod.mk.injEq] at *) <;> omega

/-- Retained vertical step at an odd bottom centre `(x, 0)`, `3 <= x`: the step is `+1`. -/
theorem retention_bot_odd (k : ℕ) (η x s : ℤ) (hη : η = 1 ∨ η = -1)
    (hN : NativeP (2 * (k : ℤ) + 3) (x, 0)) (hpar : x % 2 = 1) (hx : 3 ≤ x)
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, 0) ((x, 0) + (0, s))) :
    s = 1 := by
  have hE : ¬ EvenSite (x, 0) := by unfold EvenSite; dsimp only; omega
  have hw : laplacian (reciprocalField k) (x, 0) = 0 := by
    rw [laplacian_reciprocal_native k hN, if_neg hE]
    dsimp only
    rw [if_neg]
    omega
  rw [ePolicy_white k η hη (x, 0) ((x, 0) + (0, s)) hw, selDisp_nativeRep k η hη hN] at hpol
  rw [add_sub_cancel_left] at hpol
  unfold selDisp at hpol
  rw [if_neg hE] at hpol
  split_ifs at hpol <;> (try simp only [Prod.mk.injEq] at *) <;> omega

/-- **Bottom row, even centre, slip on the policy edge.** -/
theorem slip_bot_E (k : ℕ) (η x s : ℤ) (hη : η = 1 ∨ η = -1) (hpar : x % 2 = 0)
    (hx : 4 ≤ x) (hxd : x ≤ (2 * (k : ℤ) + 3) - 3)
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, 0) ((x, 0) + (s, 0))) :
    (reciprocalFrame k).slip (reciprocalField k) η ((x, 0) + (s, 0)) ≤ (reciprocalFrame k).slip (reciprocalField k) η (x, 0) := by
  have hN : NativeP (2 * (k : ℤ) + 3) (x, 0) := by
    unfold NativeP; left; dsimp only; omega
  have hsgn := retention_bot_even k η x s hη hN hpar (by omega) hpol
  subst hsgn
  apply slip_edge_le (reciprocalField k) (reciprocalFrame k) η (x, 0) (1, 0)
  have e1 : (x, 0) + η • (reciprocalFrame k).shortShift = (x - 2 * η, 0) := by
    rw [smul_shortShift_recip k η]
    ext <;> (simp; try ring)
  rw [e1]
  exact bot_E_D k η x hη hx hxd

/-- **Bottom row, even centre, price on the policy edge.** -/
theorem price_bot_E (k : ℕ) (η x s : ℤ) (hη : η = 1 ∨ η = -1) (hpar : x % 2 = 0)
    (hx : 4 ≤ x) (hxd : x ≤ (2 * (k : ℤ) + 3) - 3)
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, 0) ((x, 0) + (s, 0))) :
    (reciprocalFrame k).price (reciprocalField k) ((x, 0) + (s, 0)) ≤ (reciprocalFrame k).price (reciprocalField k) (x, 0) := by
  have hN : NativeP (2 * (k : ℤ) + 3) (x, 0) := by
    unfold NativeP; left; dsimp only; omega
  have hsgn := retention_bot_even k η x s hη hN hpar (by omega) hpol
  subst hsgn
  apply price_edge_le k (reciprocalField k) (x, 0) (1, 0)
  have e1 : (x, 0) - (1, -1) = (x - 1, 1) := by ext <;> (simp; try ring)
  simp only [e1]
  exact bot_E_P k x hx hxd

/-- **Bottom row, even centre, chain on the policy edge.** -/
theorem chain_bot_E (k : ℕ) (η x s : ℤ) (hη : η = 1 ∨ η = -1) (hpar : x % 2 = 0)
    (hx : 4 ≤ x) (hxd : x ≤ (2 * (k : ℤ) + 3) - 3)
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, 0) ((x, 0) + (s, 0))) :
    (reciprocalFrame k).chainPotential (reciprocalField k) η ((x, 0) + (s, 0)) ≤
      (reciprocalFrame k).chainPotential (reciprocalField k) η (x, 0) := by
  have hN : NativeP (2 * (k : ℤ) + 3) (x, 0) := by
    unfold NativeP; left; dsimp only; omega
  have hsgn := retention_bot_even k η x s hη hN hpar (by omega) hpol
  subst hsgn
  apply chain_edge_le k (reciprocalField k) η (x, 0) (1, 0)
  rw [smul_shortShift_recip k η]
  have e2 : (x, 0) + (-2 * η, 0) - (1, -1) = (x - 2 * η - 1, 1) := by ext <;> (simp; try ring)
  simp only [e2]
  exact bot_E_Phi k η x hη hx hxd

/-- **Bottom row, odd centre, slip on the policy edge.** -/
theorem slip_bot_O (k : ℕ) (η x s : ℤ) (hη : η = 1 ∨ η = -1) (hpar : x % 2 = 1)
    (hx : 3 ≤ x) (hxd : x ≤ (2 * (k : ℤ) + 3) - 2)
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, 0) ((x, 0) + (0, s))) :
    (reciprocalFrame k).slip (reciprocalField k) η ((x, 0) + (0, s)) ≤ (reciprocalFrame k).slip (reciprocalField k) η (x, 0) := by
  have hN : NativeP (2 * (k : ℤ) + 3) (x, 0) := by
    unfold NativeP; left; dsimp only; omega
  have hsgn := retention_bot_odd k η x s hη hN hpar hx hpol
  subst hsgn
  apply slip_edge_le (reciprocalField k) (reciprocalFrame k) η (x, 0) (0, 1)
  have e1 : (x, 0) + η • (reciprocalFrame k).shortShift = (x - 2 * η, 0) := by
    rw [smul_shortShift_recip k η]
    ext <;> (simp; try ring)
  rw [e1]
  exact bot_O_D k η x hη hx hxd

/-- **Bottom row, odd centre, price on the policy edge.** -/
theorem price_bot_O (k : ℕ) (η x s : ℤ) (hη : η = 1 ∨ η = -1) (hpar : x % 2 = 1)
    (hx : 3 ≤ x) (hxd : x ≤ (2 * (k : ℤ) + 3) - 2)
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, 0) ((x, 0) + (0, s))) :
    (reciprocalFrame k).price (reciprocalField k) ((x, 0) + (0, s)) ≤ (reciprocalFrame k).price (reciprocalField k) (x, 0) := by
  have hN : NativeP (2 * (k : ℤ) + 3) (x, 0) := by
    unfold NativeP; left; dsimp only; omega
  have hsgn := retention_bot_odd k η x s hη hN hpar hx hpol
  subst hsgn
  apply price_edge_le k (reciprocalField k) (x, 0) (0, 1)
  have e1 : (x, 0) - (1, -1) = (x - 1, 1) := by ext <;> (simp; try ring)
  simp only [e1]
  exact bot_O_P k x hx hxd

/-- **Bottom row, odd centre, chain on the policy edge.** -/
theorem chain_bot_O (k : ℕ) (η x s : ℤ) (hη : η = 1 ∨ η = -1) (hpar : x % 2 = 1)
    (hx : 3 ≤ x) (hxd : x ≤ (2 * (k : ℤ) + 3) - 2)
    (hpol : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) (x, 0) ((x, 0) + (0, s))) :
    (reciprocalFrame k).chainPotential (reciprocalField k) η ((x, 0) + (0, s)) ≤
      (reciprocalFrame k).chainPotential (reciprocalField k) η (x, 0) := by
  have hN : NativeP (2 * (k : ℤ) + 3) (x, 0) := by
    unfold NativeP; left; dsimp only; omega
  have hsgn := retention_bot_odd k η x s hη hN hpar hx hpol
  subst hsgn
  apply chain_edge_le k (reciprocalField k) η (x, 0) (0, 1)
  rw [smul_shortShift_recip k η]
  have e2 : (x, 0) + (-2 * η, 0) - (1, -1) = (x - 2 * η - 1, 1) := by ext <;> (simp; try ring)
  simp only [e2]
  exact bot_O_Phi k η x hη hx hxd

end FLatticePaper.EPolicy
