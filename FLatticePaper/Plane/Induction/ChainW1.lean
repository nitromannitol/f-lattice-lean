import FLatticePaper.Plane.Induction.BothFreeRise
import FLatticePaper.Plane.Induction.Q24Instances
import FLatticePaper.Plane.Induction.BothFreeNative
import FLatticePaper.Plane.Induction.ChainDeck
import FLatticePaper.Plane.Induction.TransferW1
import FLatticePaper.Plane.Induction.CollarBand

/-! Task 72 / Q28: the chain monotonicity from the W1 classification, with no joint hypothesis.

The packet `hpk : frame.Packet F` supplies the Laplacian and price drifts (`ChainDeck`), the strips and the binarity. Each root of a rising
edge is moved into the closed polygon by a deck translate (`closedPolygon_covers`); `rise_roots_not_SI` applies to the translated rise, and
the non-SI roots are nonfree (`nonfree_strictInterior`), hence have native free representatives (`exists_translate_of_not_nonfree`). The
two native roots are then excluded by `both_free_rise_native`. The deck equivariance of the sign `η` game is `hdeck`, and of the sign `−η`
game is `hdeckOpp`. -/

namespace FLatticePaper.ChainW1

open FLatticePaper FLatticePaper.Induction FLatticePaper.BothFreeRise FLatticePaper.Q24Instances FLatticePaper.ChainDeck
  FLatticePaper.BothFreeNative

/-- **The chain monotonicity from the W1 classification (Q28, with the packet).** `Φ_η` does not increase along the sign-`η` game, given the
packet of the field, the W1 forcing of the word's frame, and the deck equivariance of both signs (`hdeck`, `hdeckOpp`) and the chain drift
`hdrift`. -/
theorem chain_nonincreasing_of_W1 (frame : ChildFrame) {F : Field} (G : CanonicalSignedGames frame F)
    (hpk : frame.Packet F) {η : ℤ} (hη : η = 1 ∨ η = -1)
    (hc : 3 ≤ frame.child.den - frame.child.num) (hU : HasUnitPrice frame F)
    (hW1word : FLatticePaper.W1.W1Forced frame.child.num frame.child.den F)
    (hdeck : ∀ z u (i j : ℤ), (G.game η hη).policy z u →
      (G.game η hη).policy (z - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j))
    (hdeckOpp : ∀ z u (i j : ℤ), (G.game (-η) (neg_unit hη)).policy z u →
      (G.game (-η) (neg_unit hη)).policy (z - frame.child.modifiedDeck.combine i j)
        (u - frame.child.modifiedDeck.combine i j))
    (hdrift : ∀ i j : ℤ, ∃ c : ℤ, ∀ x,
      frame.chainPotential F η (x - frame.child.modifiedDeck.combine i j) = frame.chainPotential F η x + c) :
    NonincreasingAlong (frame.chainPotential F η) (G.game η hη).policy := by
  intro z u hu
  by_contra hnot
  rw [not_le] at hnot
  have hS : frame.HasStrips F := hpk.strips
  have hlapF : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0 := hpk.binary
  have hs : ((η • frame.shortShift).1 + (η • frame.shortShift).2) % 2 = 0 := by
    obtain ⟨k, hk⟩ : (2 : ℤ) ∣ frame.shortShift.1 + frame.shortShift.2 :=
      Int.dvd_of_emod_eq_zero (FLatticePaper.BothFreeGrades.shortShift_even frame)
    rcases hη with h | h <;> simp only [h, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> omega
  set C := G.game η hη with hCdef
  set O := G.game (-η) (neg_unit hη) with hOdef
  have hin : u = incomingNeg z ∨ u = incomingPos z := C.policyEdge z u hu
  have hunit : ∀ a b, C.policy a b →
      frame.price F (b + η • frame.shortShift) ≤ frame.price F (a + η • frame.shortShift) + 1 := by
    intro a b hab
    have he := TwoRank.edge_add_of_even (η • frame.shortShift) hs (C.policyEdge a b hab)
    have h1 := (hU _ _ he).2
    unfold priceIncrement at h1
    omega
  obtain ⟨hgF, hF, -, -, hPs, v, hv1, hv2, hvQ⟩ := TwoRank.rise_local_frame frame C hη O.policy
    (rawSlip_of_canonical O) O.quota (price_nonincreasing_of_canonical O) hlapF hunit hu hin hnot
  have hu' := TwoRank.edge_add_of_even (η • frame.shortShift) hs (C.policyEdge z u hu)
  -- the two roots, each moved into the closed polygon by its own deck vector
  obtain ⟨y0, hy0, c0i, c0j, hz0⟩ := frame.closedPolygon_covers z
  obtain ⟨y1, hy1, c1i, c1j, hz1⟩ := frame.closedPolygon_covers (z + η • frame.shortShift)
  have hy0' : y0 = z - frame.child.modifiedDeck.combine c0i c0j := by
    rw [hz0]
    abel
  have hy1' : y1 = z + η • frame.shortShift - frame.child.modifiedDeck.combine c1i c1j := by
    rw [hz1]
    abel
  -- the first root: the translated rise by `c0` has its first root in the polygon, and it is not SI
  obtain ⟨c0, hc0⟩ := hdrift c0i c0j
  have hrise0 : frame.chainPotential F η (z - frame.child.modifiedDeck.combine c0i c0j) <
      frame.chainPotential F η (u - frame.child.modifiedDeck.combine c0i c0j) := by
    rw [hc0, hc0]
    linarith
  obtain ⟨hNSI0, -⟩ := rise_roots_not_SI C O hη hlapF hU hW1word (hdeck z u c0i c0j hu) hrise0
  have hyeq0 : z - frame.child.modifiedDeck.combine c0i c0j = y0 := by
    rw [hz0, add_sub_cancel_right]
  rw [hyeq0] at hNSI0
  have hNN0 : ¬ Nonfree frame y0 := fun hnf => hNSI0 (TransferW1.nonfree_strictInterior frame hy0 hnf)
  obtain ⟨a0, b0, hfree0⟩ := CollarBand.exists_translate_of_not_nonfree frame hNN0
  rw [← combine_eq_vec frame a0 b0] at hfree0
  have hw0mem := (Set.mem_union _ _ _).mp hfree0
  -- the second root: the translated rise by `c1` has its second root `y1` in the polygon, and it is not SI
  obtain ⟨c1, hc1⟩ := hdrift c1i c1j
  have hrise1 : frame.chainPotential F η (z - frame.child.modifiedDeck.combine c1i c1j) <
      frame.chainPotential F η (u - frame.child.modifiedDeck.combine c1i c1j) := by
    rw [hc1, hc1]
    linarith
  obtain ⟨-, hNSI1⟩ := rise_roots_not_SI C O hη hlapF hU hW1word (hdeck z u c1i c1j hu) hrise1
  have hyeq1 : z - frame.child.modifiedDeck.combine c1i c1j + η • frame.shortShift = y1 := by
    have e : z - frame.child.modifiedDeck.combine c1i c1j + η • frame.shortShift =
        (z + η • frame.shortShift) - frame.child.modifiedDeck.combine c1i c1j := by abel
    rw [e, hz1, add_sub_cancel_right]
  rw [hyeq1] at hNSI1
  have hNN1 : ¬ Nonfree frame y1 := fun hnf => hNSI1 (TransferW1.nonfree_strictInterior frame hy1 hnf)
  obtain ⟨a1, b1, hfree1⟩ := CollarBand.exists_translate_of_not_nonfree frame hNN1
  rw [← combine_eq_vec frame a1 b1] at hfree1
  have hw1mem := (Set.mem_union _ _ _).mp hfree1
  -- the laplacian at the native roots: the Laplacian is invariant under deck vectors
  have hly0 : laplacian F y0 = 0 := by
    have e : laplacian F z = laplacian F y0 := by
      rw [hz0, frame.laplacian_add_lattice hpk]
    rw [← e]
    exact hF
  have hlw0 : laplacian F (y0 + frame.child.modifiedDeck.combine a0 b0) = 0 := by
    rw [frame.laplacian_add_lattice hpk]
    exact hly0
  have hly1 : laplacian F y1 = 0 := by
    have e : laplacian F (z + η • frame.shortShift) = laplacian F y1 := by
      rw [hz1, frame.laplacian_add_lattice hpk]
    rw [← e]
    exact hgF
  have hlw1 : laplacian F (y1 + frame.child.modifiedDeck.combine a1 b1) = 0 := by
    rw [frame.laplacian_add_lattice hpk]
    exact hly1
  -- the policy at the native root `w0`: the translate by `c0 − a0`
  have hw0eq : z - frame.child.modifiedDeck.combine (c0i - a0) (c0j - b0) =
      y0 + frame.child.modifiedDeck.combine a0 b0 := by
    rw [combine_sub_eq, hz0]
    abel
  have hPw : C.policy (y0 + frame.child.modifiedDeck.combine a0 b0)
      ((y0 + frame.child.modifiedDeck.combine a0 b0) + (u - z)) := by
    have key := hdeck z u (c0i - a0) (c0j - b0) hu
    rw [hw0eq] at key
    have hu2 : u - frame.child.modifiedDeck.combine (c0i - a0) (c0j - b0) =
        (y0 + frame.child.modifiedDeck.combine a0 b0) + (u - z) := by
      rw [combine_sub_eq, hz0]
      abel
    rw [hu2] at key
    exact key
  -- the policy at the native root `w1`: the opposite policy translated by `c1 − a1`
  have hvz : v = z + z - u := other_input z u v hin hv1 hv2
  have hQw : O.policy (y1 + frame.child.modifiedDeck.combine a1 b1)
      ((y1 + frame.child.modifiedDeck.combine a1 b1) - (u - z)) := by
    have hvQ' : O.policy ((z + η • frame.shortShift) - frame.child.modifiedDeck.combine (c1i - a1) (c1j - b1))
        ((v + η • frame.shortShift) - frame.child.modifiedDeck.combine (c1i - a1) (c1j - b1)) :=
      hdeckOpp _ _ (c1i - a1) (c1j - b1) hvQ
    have eA : (z + η • frame.shortShift) - frame.child.modifiedDeck.combine (c1i - a1) (c1j - b1) =
        y1 + frame.child.modifiedDeck.combine a1 b1 := by
      rw [combine_sub_eq, hy1']
      abel
    have eB : (v + η • frame.shortShift) - frame.child.modifiedDeck.combine (c1i - a1) (c1j - b1) =
        (y1 + frame.child.modifiedDeck.combine a1 b1) - (u - z) := by
      rw [combine_sub_eq, hvz, hy1']
      abel
    rw [eA, eB] at hvQ'
    exact hvQ'
  -- the input relation at the native root `w1`
  have hu'' := TwoRank.edge_add_of_even (frame.child.modifiedDeck.combine (a1 - c1i) (b1 - c1j))
    (combine_even frame (a1 - c1i) (b1 - c1j)) hu'
  have eU : (u + η • frame.shortShift) + frame.child.modifiedDeck.combine (a1 - c1i) (b1 - c1j) =
      (y1 + frame.child.modifiedDeck.combine a1 b1) + (u - z) := by
    rw [combine_sub_eq, hy1']
    abel
  have eZ : (z + η • frame.shortShift) + frame.child.modifiedDeck.combine (a1 - c1i) (b1 - c1j) =
      y1 + frame.child.modifiedDeck.combine a1 b1 := by
    rw [combine_sub_eq, hy1']
    abel
  rw [eU, eZ] at hu''
  have hu''' : (y1 + frame.child.modifiedDeck.combine a1 b1) + (u - z) =
      incomingNeg (y1 + frame.child.modifiedDeck.combine a1 b1) ∨
      (y1 + frame.child.modifiedDeck.combine a1 b1) + (u - z) =
      incomingPos (y1 + frame.child.modifiedDeck.combine a1 b1) := hu''
  -- the price rise at the native root `w1`: the price drifts by the same deck amount at both ends
  have hprice1 := ChainDeck.price_combine frame hpk (a1 - c1i) (b1 - c1j) (u + η • frame.shortShift)
  have hprice2 := ChainDeck.price_combine frame hpk (a1 - c1i) (b1 - c1j) (z + η • frame.shortShift)
  have hrise : frame.price F ((y1 + frame.child.modifiedDeck.combine a1 b1) + (u - z)) =
      frame.price F (y1 + frame.child.modifiedDeck.combine a1 b1) + 1 := by
    rw [← eU, ← eZ]
    linarith
  -- the congruence of the two native roots
  have hcong : (y1 + frame.child.modifiedDeck.combine a1 b1) =
      (y0 + frame.child.modifiedDeck.combine a0 b0) + η • frame.shortShift +
        frame.child.modifiedDeck.combine (c0i - c1i + a1) (c0j - c1j + b1) -
          frame.child.modifiedDeck.combine a0 b0 := by
    rw [combine_lin frame c0i c0j c1i c1j a1 b1, hy0', hy1']
    abel
  have hpar : EvenSite (y0 + frame.child.modifiedDeck.combine a0 b0) ↔
      EvenSite (y1 + frame.child.modifiedDeck.combine a1 b1) := by
    have hsum := congrArg (fun p : Site => p.1 + p.2) hcong
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hsum
    have e1 := combine_even frame a0 b0
    have e2 := combine_even frame a1 b1
    have e3 := combine_even frame (c0i - c1i + a1) (c0j - c1j + b1)
    unfold EvenSite
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  exact both_free_rise_native frame hS hη hc C.prescribed O.prescribed (c0i - c1i + a1) (c0j - c1j + b1) a0 b0
    hw0mem hw1mem hlw0 hlw1 hPw hQw hu''' hrise hcong hpar

end FLatticePaper.ChainW1
