import FLatticePaper.Plane.Induction.W4Guard
import FLatticePaper.Plane.Induction.ChainWire
import FLatticePaper.Plane.Induction.DeckForced
import FLatticePaper.Plane.Induction.LowerBandStrong
import FLatticePaper.Plane.Induction.FreePolicy

/-! # The rise input of the forced permit, from the canonical game

`W4Guard.noRiseForced_proved` gives `NoRiseForced P` for the conjugate's ranked policy from the conjugate's strong estimates, its trace,
its W1 forcing and the prescription `hPres` at free-closure whites. Here `hPres` is derived from the canonical game `G` whose policy is
`W.retained`: the policy is invariant under the span translates (`ChainWire.deck_of_games`) and prescribed at the free representatives
(`PrescribedAt`). No properness of the conjugate is used (the zero bands come from the conjugate's own packet), so the all-threes
conjugate `3^k` is covered by the same argument. -/

namespace FLatticePaper.RiseInput

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreeClosure FLatticePaper.FreePolicy

/-- The canonical policy is invariant under a span translate, in both directions. -/
theorem retained_span_iff {word : Word} {seed : Site → Site → Prop}
    (W : FLatticePaper.W1Witness.OldPolicyWitness (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    (hW : W.retained = (G.game (frameAt word).eps (frameAt word).eps_unit).policy) {s : Site}
    (hs : s ∈ (frameAt (conjWord word)).child.modifiedDeck.span) (z u : Site) :
    W.retained z u ↔ W.retained (z + s) (u + s) := by
  obtain ⟨a, b, rfl⟩ := hs
  have hη : (frameAt word).eps = 1 ∨ (frameAt word).eps = -1 := (frameAt word).eps_unit
  have key : ∀ x : Site, x - (frameAt (conjWord word)).child.modifiedDeck.combine (-a) (-b) =
      x + (frameAt (conjWord word)).child.modifiedDeck.combine a b := by
    intro x
    ext <;> simp [PeriodDeck.combine] <;> ring
  constructor
  · intro hz
    have h' := FLatticePaper.ChainWire.deck_of_games G hη W hW (-a) (-b) z u hz
    rw [key z, key u] at h'
    exact h'
  · intro hz
    have h' := FLatticePaper.ChainWire.deck_of_games G hη W hW a b _ _ hz
    rw [add_sub_cancel_right, add_sub_cancel_right] at h'
    exact h'

theorem add_shift_iff (j t x p : Site) : j + t = x + t + p ↔ j = x + p := by
  rw [show x + t + p = (x + p) + t by abel]
  exact add_left_inj t

/-- The prescription at a free H representative of a free-closure white, transported along the span translate `t`. -/
theorem retained_freeH_iff {word : Word} {seed : Site → Site → Prop}
    (hSE : StrongEstimates (conjWord word))
    (W : FLatticePaper.W1Witness.OldPolicyWitness (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    (hW : W.retained = (G.game (frameAt word).eps (frameAt word).eps_unit).policy) {c t : Site}
    (ht : t ∈ (frameAt (conjWord word)).child.modifiedDeck.span) (hH : c + t ∈ (frameAt (conjWord word)).freeH)
    (hc : laplacian (standardField (conjWord word)) c = 0) (j : Site) :
    W.retained c j ↔ j = c + (frameAt (conjWord word)).prescribedH (frameAt word).eps (c + t) := by
  have hd : laplacian (standardField (conjWord word)) (c + t) = 0 :=
    (laplacian_span_inv _ _ hSE.packet ht c).trans hc
  have hpr := (G.game (frameAt word).eps (frameAt word).eps_unit).prescribed.1 (c + t) hH hd (j + t)
  rw [← hW] at hpr
  rw [retained_span_iff W G hW ht c j, hpr]
  exact add_shift_iff j t c _

/-- The prescription at a free V representative of a free-closure white, transported along the span translate `t`. -/
theorem retained_freeV_iff {word : Word} {seed : Site → Site → Prop}
    (hSE : StrongEstimates (conjWord word))
    (W : FLatticePaper.W1Witness.OldPolicyWitness (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    (hW : W.retained = (G.game (frameAt word).eps (frameAt word).eps_unit).policy) {c t : Site}
    (ht : t ∈ (frameAt (conjWord word)).child.modifiedDeck.span) (hV : c + t ∈ (frameAt (conjWord word)).freeV)
    (hc : laplacian (standardField (conjWord word)) c = 0) (j : Site) :
    W.retained c j ↔ j = c + (frameAt (conjWord word)).prescribedV (frameAt word).eps (c + t) := by
  have hd : laplacian (standardField (conjWord word)) (c + t) = 0 :=
    (laplacian_span_inv _ _ hSE.packet ht c).trans hc
  have hpr := (G.game (frameAt word).eps (frameAt word).eps_unit).prescribed.2 (c + t) hV hd (j + t)
  rw [← hW] at hpr
  rw [retained_span_iff W G hW ht c j, hpr]
  exact add_shift_iff j t c _

/-- **The prescription on free-closure whites, from the canonical game.** -/
theorem hPres_of_canonical {word : Word} {seed : Site → Site → Prop}
    (hSE : StrongEstimates (conjWord word))
    (W : FLatticePaper.W1Witness.OldPolicyWitness (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    (hW : W.retained = (G.game (frameAt word).eps (frameAt word).eps_unit).policy) :
    ∀ c : Site, freeClosure (frameAt (conjWord word)) c →
      laplacian (standardField (conjWord word)) c = 0 →
      ∀ j : Site, W.retained c j ↔ FreePresc (frameAt (conjWord word)) (frameAt word).eps c j := by
  intro c hfc hc j
  constructor
  · intro h
    obtain ⟨s, hs, hH | hV⟩ := hfc
    · exact ⟨s, hs, Or.inl ⟨hH, (retained_freeH_iff hSE W G hW hs hH hc j).mp h⟩⟩
    · exact ⟨s, hs, Or.inr ⟨hV, (retained_freeV_iff hSE W G hW hs hV hc j).mp h⟩⟩
  · rintro ⟨t, ht, ⟨hH, hj⟩ | ⟨hV, hj⟩⟩
    · exact (retained_freeH_iff hSE W G hW ht hH hc j).mpr hj
    · exact (retained_freeV_iff hSE W G hW ht hV hc j).mpr hj

/-- **The rise input of the canonical policy.** `NoRiseForced` holds for the policy of the canonical game, from the conjugate's strong
estimates, trace and W1 data. -/
theorem noRise_of_canonical {word : Word} {seed : Site → Site → Prop} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    (hTr : FLatticePaper.TraceFromPsi.TraceAt (conjWord word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (W : FLatticePaper.W1Witness.OldPolicyWitness (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    (hW : W.retained = (G.game (frameAt word).eps (frameAt word).eps_unit).policy) :
    FLatticePaper.W4Reduction.NoRiseForced W.toOldPolicyData :=
  FLatticePaper.W4Guard.noRiseForced_proved h hSE hTr hW1 W.toOldPolicyData
    (hPres_of_canonical hSE W G hW)

end FLatticePaper.RiseInput
