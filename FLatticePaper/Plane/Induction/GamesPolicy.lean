import FLatticePaper.Plane.Induction.CanonicalSigned

/-!
# The canonical games with a deck rank give the policy inputs `hpol` (one input for `hpol` and `hcan`)

`GamesWithRank w`: at a word `w`, the canonical signed games `G` of its standard field, and for each sign `η = ±1` a rank `R` with the
deck characters (`R(z + U) = R z + cU`, `R(z + V) = R z + cV`) that decreases strictly along the sign-`η` policy of `G`.

The games alone do not give the characters: `CanonicalPolicy` has a strict rank but no deck characters, and
`rankWithIncrements_of_strict_hull` needs them. So the rank with characters is part of the input.

`policy_of_gamesWithRank`: from `GamesWithRank w` the policy inputs of `hpol` at `w` follow: the quota, the chain claim `chainNonincreasing`
of the games, the price and the rounded slip monotonicity of the policy (`cutGrade F 1 0 1 = price`, `cutGrade F 0 1 η = roundedSlip`), and
the characters and the strict rank.
-/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The games of a word with, for each sign, a strict deck rank of the policy of that sign. -/
def GamesWithRank (w : Word) : Prop :=
  ∃ G : CanonicalSignedGames (frameAt w) (standardField w),
    ∀ η : ℤ, (hη : η = 1 ∨ η = -1) → ∃ (R : Site → ℤ) (cU cV : ℤ),
      (∀ z, R (z + (frameAt w).child.modifiedDeck.kernel) = R z + cU) ∧
      (∀ z, R (z + (frameAt w).child.modifiedDeck.transverse) = R z + cV) ∧
      (∀ x i, (G.game η hη).policy x i → R i < R x)

/-- The policy inputs of `hpol` at a word, from the games with a deck rank. -/
theorem policy_of_gamesWithRank {w : Word} (h : GamesWithRank w) :
    ∀ η : ℤ, (η = 1 ∨ η = -1) → ∃ (policy : Site → Site → Prop) (R : Site → ℤ) (cU cV : ℤ),
      RetainQuota (standardField w) policy ∧
      NonincreasingAlong ((frameAt w).chainPotential (standardField w) η) policy ∧
      NonincreasingAlong ((frameAt w).price (standardField w)) policy ∧
      NonincreasingAlong ((frameAt w).roundedSlip (standardField w) η) policy ∧
      (∀ z, R (z + (frameAt w).child.modifiedDeck.kernel) = R z + cU) ∧
      (∀ z, R (z + (frameAt w).child.modifiedDeck.transverse) = R z + cV) ∧
      (∀ x i, policy x i → R i < R x) := by
  obtain ⟨G, hG⟩ := h
  intro η hη
  obtain ⟨R, cU, cV, hRU, hRV, hstr⟩ := hG η hη
  refine ⟨(G.game η hη).policy, R, cU, cV, (G.game η hη).quota, G.chainNonincreasing η hη, ?_, ?_, hRU, hRV, hstr⟩
  · intro c i hc
    have h1 := (G.game η hη).nonincreasingP c i hc
    rw [cutGrade_one_zero_one, cutGrade_one_zero_one] at h1
    exact h1
  · intro c i hc
    have h1 := (G.game η hη).nonincreasingJ c i hc
    unfold ChildFrame.cutGrade at h1
    simpa using h1

/-- **The phase-one policy with its prescription.** The policy of `policy_of_gamesWithRank` at `η = 1`, namely the canonical
policy of the games, together with its prescription `PrescribedAt` (the field `prescribed` of the canonical signed policy).
`hpol` is unchanged; this is the same policy with the extra property. -/
theorem policy_of_gamesWithRank_prescribed {w : Word} (h : GamesWithRank w) :
    ∃ (policy : Site → Site → Prop) (R : Site → ℤ) (cU cV : ℤ),
      PrescribedAt (frameAt w) (standardField w) 1 policy ∧
      RetainQuota (standardField w) policy ∧
      NonincreasingAlong ((frameAt w).chainPotential (standardField w) 1) policy ∧
      NonincreasingAlong ((frameAt w).price (standardField w)) policy ∧
      NonincreasingAlong ((frameAt w).roundedSlip (standardField w) 1) policy ∧
      (∀ z, R (z + (frameAt w).child.modifiedDeck.kernel) = R z + cU) ∧
      (∀ z, R (z + (frameAt w).child.modifiedDeck.transverse) = R z + cV) ∧
      (∀ x i, policy x i → R i < R x) := by
  obtain ⟨G, hG⟩ := h
  have hη : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  obtain ⟨R, cU, cV, hRU, hRV, hstr⟩ := hG 1 hη
  refine ⟨(G.game 1 hη).policy, R, cU, cV, (G.game 1 hη).prescribed, (G.game 1 hη).quota,
    G.chainNonincreasing 1 hη, ?_, ?_, hRU, hRV, hstr⟩
  · intro c i hc
    have h1 := (G.game 1 hη).nonincreasingP c i hc
    rw [cutGrade_one_zero_one, cutGrade_one_zero_one] at h1
    exact h1
  · intro c i hc
    have h1 := (G.game 1 hη).nonincreasingJ c i hc
    unfold ChildFrame.cutGrade at h1
    simpa using h1

/-- The canonical games of a word, with the deck rank, give the policy inputs at the word. -/
theorem games_of_gamesWithRank {w : Word} (h : GamesWithRank w) :
    Nonempty (CanonicalSignedGames (frameAt w) (standardField w)) := by
  obtain ⟨G, -⟩ := h
  exact ⟨G⟩

end FLatticePaper.Induction
