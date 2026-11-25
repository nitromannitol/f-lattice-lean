import FLatticePaper.Plane.Induction.EvenVSquare
import FLatticePaper.Plane.Induction.EndpointRows
import FLatticePaper.Plane.Induction.EndpointStrips
import FLatticePaper.Plane.Induction.DeckParentSquare
import FLatticePaper.Plane.Induction.W1NonfreeHsqC

/-! # Wiring the endpoint rows and the even V squares into the native classifier (temporary named classes)

The native classifier `native_of_classes` gives `ParentSquareOut` at every native free white root `z ∈ freeH ∪ freeV`:

* the first V root `vFirst = (0,0)` for both signs (`EndpointRows.row_V0`, with the endpoint facts of the strips);
* the last V root `vLast` for `η = +1` (`EndpointRows.native_vLast_plus`); for `η = −1` the even square covers `vLast`;
* the other even free V roots by `EvenVSquare.evenV_square`, with `δ = −η`, the colour and freeness facts of its corners as
  named inputs (`hX1`, `hX2`, `hX3`) and the canonical rule `hcanon` as a named input;
* the odd free V roots and the free H roots as named classes (`hVodd`, `hH`).

The deck equivariance of the policy (`hdeck`) is named; `hdU`, `hdV` are derived from it. `hfree_of_classes` gives the free-root
`hfree` of `W1NonfreeHsqC.W1Forced_of_inputs` through `DeckParentSquare.parentSquareOut_of_native`, and `W1Forced_chain` closes
`W1Forced` of the sheet minimum from the headline input `hW1`. The named inputs are the open items of the chain. -/

namespace FLatticePaper.ChainWire

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1 FLatticePaper.W1NonfreeOut
  FLatticePaper.W1Witness FLatticePaper.DeckParentSquare

/-- The negated deck combination: `combine (−i) (−j) = −combine i j`. -/
theorem combine_neg (frame : ChildFrame) (i j : ℤ) :
    frame.child.modifiedDeck.combine (-i) (-j) = -frame.child.modifiedDeck.combine i j := by
  unfold PeriodDeck.combine
  refine Prod.ext ?_ ?_ <;> simp <;> ring

/-- A deck shift is an equivalence of the policy: `R x u ↔ R (x + combine i j) (u + combine i j)`, from the equivariance under the
deck. -/
theorem deck_shift_iff {frame : ChildFrame} {R : Site → Site → Prop}
    (hdeck : ∀ (i j : ℤ) (z u : Site), R z u → R (z - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j))
    (i j : ℤ) (x u : Site) :
    R x u ↔ R (x + frame.child.modifiedDeck.combine i j) (u + frame.child.modifiedDeck.combine i j) := by
  constructor
  · intro h
    have h' := hdeck (-i) (-j) x u h
    rw [combine_neg, sub_neg_eq_add, sub_neg_eq_add] at h'
    exact h'
  · intro h
    have h' := hdeck i j _ _ h
    simpa using h'

/-- The kernel shift `Kdeck` is the deck combination `combine 1 0`. -/
theorem combine_one_zero_eq_Kdeck (frame : ChildFrame) :
    frame.child.modifiedDeck.combine 1 0 = Kdeck frame := by
  unfold PeriodDeck.combine Kdeck
  rw [frame.kernel_coords]
  simp

/-- The transverse shift `Vdeck` is the deck combination `combine 0 1`. -/
theorem combine_zero_one_eq_Vdeck (frame : ChildFrame) :
    frame.child.modifiedDeck.combine 0 1 = Vdeck frame := by
  unfold PeriodDeck.combine Vdeck
  rw [frame.child_modifiedDeck_transverse]
  simp

/-- The kernel equivariance `hdU` of the policy, from the deck equivariance. -/
theorem hdU_of_deck {frame : ChildFrame} {R : Site → Site → Prop}
    (hdeck : ∀ (i j : ℤ) (z u : Site), R z u → R (z - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j)) :
    ∀ x u, R x u ↔ R (x + Kdeck frame) (u + Kdeck frame) := by
  intro x u
  rw [← combine_one_zero_eq_Kdeck]
  exact deck_shift_iff hdeck 1 0 x u

/-- The transverse equivariance `hdV` of the policy, from the deck equivariance. -/
theorem hdV_of_deck {frame : ChildFrame} {R : Site → Site → Prop}
    (hdeck : ∀ (i j : ℤ) (z u : Site), R z u → R (z - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j)) :
    ∀ x u, R x u ↔ R (x + Vdeck frame) (u + Vdeck frame) := by
  intro x u
  rw [← combine_zero_one_eq_Vdeck]
  exact deck_shift_iff hdeck 0 1 x u

/-- The white uniqueness of a witness of a canonical signed policy. -/
theorem hwu_of_canonical {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (C : CanonicalSignedPolicy frame G η) (W : OldPolicyWitness frame G seed η) (hW : W.retained = C.policy) :
    ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j' := by
  intro c j j' hc h1 h2
  rw [hW] at h1 h2
  have e1 := (C.white_policy c hc j).mp h1
  have e2 := (C.white_policy c hc j').mp h2
  rw [e1, e2]

/-- The prescription of a witness of a canonical signed policy. -/
theorem presc_of_canonical {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (C : CanonicalSignedPolicy frame G η) (W : OldPolicyWitness frame G seed η) (hW : W.retained = C.policy) :
    PrescribedAt frame G η W.retained := by
  rw [hW]
  exact C.prescribed

/-- The side condition of the even square: `η = −1`, or the root is not `vLast`. -/
theorem side_cond {frame : ChildFrame} {η : ℤ} {z : Site} (hη : η = 1 ∨ η = -1)
    (hL : ¬ (η = 1 ∧ z = frame.vLast)) : η = -1 ∨ z ≠ frame.vLast := by
  by_cases h1 : η = 1
  · right
    intro h
    exact hL ⟨h1, h⟩
  · left
    omega

/-- **The first V root `vFirst = (0,0)`, both signs** (the row `V0`, `EndpointRows.row_V0`). -/
theorem vFirst_parent {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (hP : frame.Packet G) (W : OldPolicyWitness frame G seed η)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    (hpres : PrescribedAt frame G η W.retained)
    (hdU : ∀ x u, W.retained x u ↔ W.retained (x + Kdeck frame) (u + Kdeck frame)) :
    ParentSquareOut G W.retained FLatticePaper.Induction.vFirst :=
  FLatticePaper.EndpointRows.row_V0 W hwu hpres hdU (FLatticePaper.EndpointStrips.endpointFacts_of_strips hP.strips)

/-- **The last V root `vLast`, for `η = +1`** (the row `Vend`, `EndpointRows.native_vLast_plus`). -/
theorem vLast_parent_plus {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (hP : frame.Packet G) (W : OldPolicyWitness frame G seed 1)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    (hpres : PrescribedAt frame G 1 W.retained)
    (hdU : ∀ x u, W.retained x u ↔ W.retained (x + Kdeck frame) (u + Kdeck frame))
    (hdV : ∀ x u, W.retained x u ↔ W.retained (x + Vdeck frame) (u + Vdeck frame)) :
    ParentSquareOut G W.retained frame.vLast :=
  FLatticePaper.EndpointRows.native_vLast_plus W hwu hpres hdU hdV
    (FLatticePaper.EndpointStrips.endpointFacts_of_strips hP.strips) hP

/-- **The native classifier from the classes.** Every native free white root `z ∈ freeH ∪ freeV` has `ParentSquareOut`: the V0 and
Vend rows, the even V squares (`EvenVSquare.evenV_square` with `δ = −η`), the odd V and the free H classes (named). -/
theorem native_of_classes {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η δ : ℤ}
    (hη : η = -δ) (hδ : δ = 1 ∨ δ = -1) (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (C : CanonicalSignedPolicy frame G η) (W : OldPolicyWitness frame G seed η) (hW : W.retained = C.policy)
    (hdeck : ∀ (i j : ℤ) (z u : Site), W.retained z u →
      W.retained (z - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j))
    (hH : ∀ z ∈ frame.freeH, laplacian G z = 0 → ParentSquareOut G W.retained z)
    (hVodd : ∀ z ∈ frame.freeV, ¬ EvenSite z → laplacian G z = 0 → ParentSquareOut G W.retained z)
    (hX3 : ∀ z ∈ frame.freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      (η = -1 ∨ z ≠ frame.vLast) → laplacian G z = 0 →
      (z.1, z.2 - δ) ∈ frame.freeV ∧ laplacian G (z.1, z.2 - δ) = 0)
    (hX1 : ∀ z ∈ frame.freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      (η = -1 ∨ z ≠ frame.vLast) → laplacian G z = 0 →
      laplacian G (z.1 + δ, z.2) = -1 ∨ (laplacian G (z.1 + δ, z.2) = 0 ∧ Nonfree frame (z.1 + δ, z.2)))
    (hX2 : ∀ z ∈ frame.freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      (η = -1 ∨ z ≠ frame.vLast) → laplacian G z = 0 →
      laplacian G (z.1 + δ, z.2 - δ) = -1 ∨
        (laplacian G (z.1 + δ, z.2 - δ) = 0 ∧ Nonfree frame (z.1 + δ, z.2 - δ)))
    (hcanon : ∀ z ∈ frame.freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      (η = -1 ∨ z ≠ frame.vLast) → laplacian G z = 0 →
      laplacian G (z.1 + δ, z.2) = 0 → laplacian G (z.1 + δ, z.2 - δ) = -1 →
      W.retained (z.1 + δ, z.2) (z.1 + δ, z.2 - δ)) :
    ∀ z ∈ frame.freeH ∪ frame.freeV, laplacian G z = 0 → ParentSquareOut G W.retained z := by
  have hwu := hwu_of_canonical C W hW
  have hpres := presc_of_canonical C W hW
  have hdU := hdU_of_deck hdeck
  have hdV := hdV_of_deck hdeck
  have hη' : η = 1 ∨ η = -1 := by
    rcases hδ with h | h <;> omega
  intro z hzU hw
  rcases (Set.mem_union z frame.freeH frame.freeV).mp hzU with hH' | hV'
  · exact hH z hH' hw
  · by_cases hev : EvenSite z
    · by_cases hF : z = FLatticePaper.Induction.vFirst
      · subst hF
        exact vFirst_parent hP W hwu hpres hdU
      · by_cases hL : η = 1 ∧ z = frame.vLast
        · obtain ⟨h1, h2⟩ := hL
          subst h1
          subst h2
          exact vLast_parent_plus hP W hwu hpres hdU hdV
        · have hsc := side_cond hη' hL
          exact EvenVSquare.evenV_square hP hW1 W hpres hwu hV' hev hF hw hη hδ
            (hX3 z hV' hev hF hsc hw).1 (hX3 z hV' hev hF hsc hw).2
            (hX1 z hV' hev hF hsc hw) (hX2 z hV' hev hF hsc hw)
            (fun h1 h2 => hcanon z hV' hev hF hsc hw h1 h2)
    · exact hVodd z hV' hev hw

/-- **`hfree` of the sheet's free parent roots, from the native classifier.** A non-nonfree white root has a native translate, and the
deck equivariance transports `ParentSquareOut` (`DeckParentSquare.parentSquareOut_of_native`). -/
theorem hfree_of_classes {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η δ : ℤ}
    (hη : η = -δ) (hδ : δ = 1 ∨ δ = -1) (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (C : CanonicalSignedPolicy frame G η) (W : OldPolicyWitness frame G seed η) (hW : W.retained = C.policy)
    (hdeck : ∀ (i j : ℤ) (z u : Site), W.retained z u →
      W.retained (z - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j))
    (hH : ∀ z ∈ frame.freeH, laplacian G z = 0 → ParentSquareOut G W.retained z)
    (hVodd : ∀ z ∈ frame.freeV, ¬ EvenSite z → laplacian G z = 0 → ParentSquareOut G W.retained z)
    (hX3 : ∀ z ∈ frame.freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      (η = -1 ∨ z ≠ frame.vLast) → laplacian G z = 0 →
      (z.1, z.2 - δ) ∈ frame.freeV ∧ laplacian G (z.1, z.2 - δ) = 0)
    (hX1 : ∀ z ∈ frame.freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      (η = -1 ∨ z ≠ frame.vLast) → laplacian G z = 0 →
      laplacian G (z.1 + δ, z.2) = -1 ∨ (laplacian G (z.1 + δ, z.2) = 0 ∧ Nonfree frame (z.1 + δ, z.2)))
    (hX2 : ∀ z ∈ frame.freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      (η = -1 ∨ z ≠ frame.vLast) → laplacian G z = 0 →
      laplacian G (z.1 + δ, z.2 - δ) = -1 ∨
        (laplacian G (z.1 + δ, z.2 - δ) = 0 ∧ Nonfree frame (z.1 + δ, z.2 - δ)))
    (hcanon : ∀ z ∈ frame.freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      (η = -1 ∨ z ≠ frame.vLast) → laplacian G z = 0 →
      laplacian G (z.1 + δ, z.2) = 0 → laplacian G (z.1 + δ, z.2 - δ) = -1 →
      W.retained (z.1 + δ, z.2) (z.1 + δ, z.2 - δ))
    {z : Site} (hnf : ¬ Nonfree frame z) (hw : laplacian G z = 0) :
    ParentSquareOut G W.retained z :=
  parentSquareOut_of_native frame hP hdeck
    (native_of_classes hη hδ hP hW1 C W hW hdeck hH hVodd hX3 hX1 hX2 hcanon) hnf hw

open FLatticePaper.W1Step FLatticePaper.W1MSheet FLatticePaper.W1NonfreeHsqNonneg

/-- **`W1Forced` of the sheet minimum, end to end from the headline input `hW1`.** The free-root `hfree` of
`W1Forced_of_inputs` is `hfree_of_classes` at the parent point `zTurn (c − shift)` (its laplacian fact from
`lapG_zero_of_nonneg`); the named inputs are the classes, the deck equivariance, the canonical witness `C` with `P.retained = C.policy`,
and the collar input `hcollar`. -/
theorem W1Forced_chain {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : FLatticePaper.Induction.StrongEstimates (conjWord word)) {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed
      (frameAt word).eps)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hn3 : 3 ≤ (frameAt word).child.num)
    (δ : ℤ) (hη : (frameAt word).eps = -δ) (hδ : δ = 1 ∨ δ = -1)
    (C : CanonicalSignedPolicy (frameAt (conjWord word)) (standardField (conjWord word)) (frameAt word).eps)
    (hW : P.retained = C.policy)
    (hdeck : ∀ (i j : ℤ) (z u : Site), P.retained z u →
      P.retained (z - (frameAt (conjWord word)).child.modifiedDeck.combine i j)
        (u - (frameAt (conjWord word)).child.modifiedDeck.combine i j))
    (hH : ∀ z ∈ (frameAt (conjWord word)).freeH, laplacian (standardField (conjWord word)) z = 0 →
      ParentSquareOut (standardField (conjWord word)) P.retained z)
    (hVodd : ∀ z ∈ (frameAt (conjWord word)).freeV, ¬ EvenSite z →
      laplacian (standardField (conjWord word)) z = 0 → ParentSquareOut (standardField (conjWord word)) P.retained z)
    (hX3 : ∀ z ∈ (frameAt (conjWord word)).freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      ((frameAt word).eps = -1 ∨ z ≠ (frameAt (conjWord word)).vLast) →
      laplacian (standardField (conjWord word)) z = 0 →
      (z.1, z.2 - δ) ∈ (frameAt (conjWord word)).freeV ∧
        laplacian (standardField (conjWord word)) (z.1, z.2 - δ) = 0)
    (hX1 : ∀ z ∈ (frameAt (conjWord word)).freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      ((frameAt word).eps = -1 ∨ z ≠ (frameAt (conjWord word)).vLast) →
      laplacian (standardField (conjWord word)) z = 0 →
      laplacian (standardField (conjWord word)) (z.1 + δ, z.2) = -1 ∨
        (laplacian (standardField (conjWord word)) (z.1 + δ, z.2) = 0 ∧
          Nonfree (frameAt (conjWord word)) (z.1 + δ, z.2)))
    (hX2 : ∀ z ∈ (frameAt (conjWord word)).freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      ((frameAt word).eps = -1 ∨ z ≠ (frameAt (conjWord word)).vLast) →
      laplacian (standardField (conjWord word)) z = 0 →
      laplacian (standardField (conjWord word)) (z.1 + δ, z.2 - δ) = -1 ∨
        (laplacian (standardField (conjWord word)) (z.1 + δ, z.2 - δ) = 0 ∧
          Nonfree (frameAt (conjWord word)) (z.1 + δ, z.2 - δ)))
    (hcanon : ∀ z ∈ (frameAt (conjWord word)).freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      ((frameAt word).eps = -1 ∨ z ≠ (frameAt (conjWord word)).vLast) →
      laplacian (standardField (conjWord word)) z = 0 →
      laplacian (standardField (conjWord word)) (z.1 + δ, z.2) = 0 →
      laplacian (standardField (conjWord word)) (z.1 + δ, z.2 - δ) = -1 →
      P.retained (z.1 + δ, z.2) (z.1 + δ, z.2 - δ))
    (hcollar : ∀ c : Site, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → FLatticePaper.W1CollarFrame.CollarFrame (frameAt word) c →
      HsqAt word P c) :
    FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (MW word) :=
  FLatticePaper.W1NonfreeHsqC.W1Forced_of_inputs hw hSE P hs hW1 hn3
    (fun _ h0 hM hnf =>
      hfree_of_classes hη hδ hSE.packet hW1 C P.toOldPolicyWitness hW hdeck hH hVodd hX3 hX1 hX2 hcanon hnf
        (FLatticePaper.W1NonfreeHsqC.lapG_zero_of_nonneg hw hSE h0 hM))
    hcollar

end FLatticePaper.ChainWire

