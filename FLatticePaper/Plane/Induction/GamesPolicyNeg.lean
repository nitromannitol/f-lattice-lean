import FLatticePaper.Plane.Induction.GamesPolicy

/-! The sign `−1` form of `policy_of_gamesWithRank_prescribed`: the canonical game of sign `−1` (carried by `CanonicalSignedGames`
for each unit sign) gives a prescribed policy whose chain potential `Φ_{−1}` does not increase along its retained edges. This is the
phase-zero chain step (`ε = −1`). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- **The sign `−1` policy of a word.** The same data as `policy_of_gamesWithRank_prescribed`, for the sign `η = −1`. -/
theorem policy_of_gamesWithRank_prescribed_neg {w : Word} (h : GamesWithRank w) :
    ∃ (policy : Site → Site → Prop) (R : Site → ℤ) (cU cV : ℤ),
      PrescribedAt (frameAt w) (standardField w) (-1) policy ∧
      RetainQuota (standardField w) policy ∧
      NonincreasingAlong ((frameAt w).chainPotential (standardField w) (-1)) policy ∧
      NonincreasingAlong ((frameAt w).price (standardField w)) policy ∧
      NonincreasingAlong ((frameAt w).roundedSlip (standardField w) (-1)) policy ∧
      (∀ z, R (z + (frameAt w).child.modifiedDeck.kernel) = R z + cU) ∧
      (∀ z, R (z + (frameAt w).child.modifiedDeck.transverse) = R z + cV) ∧
      (∀ x i, policy x i → R i < R x) := by
  obtain ⟨G, hG⟩ := h
  have hη : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  obtain ⟨R, cU, cV, hRU, hRV, hstr⟩ := hG (-1) hη
  refine ⟨(G.game (-1) hη).policy, R, cU, cV, (G.game (-1) hη).prescribed, (G.game (-1) hη).quota,
    G.chainNonincreasing (-1) hη, ?_, ?_, hRU, hRV, hstr⟩
  · intro c i hc
    have h1 := (G.game (-1) hη).nonincreasingP c i hc
    rw [cutGrade_one_zero_one, cutGrade_one_zero_one] at h1
    exact h1
  · intro c i hc
    have h1 := (G.game (-1) hη).nonincreasingJ c i hc
    unfold ChildFrame.cutGrade at h1
    simpa using h1

end FLatticePaper.Induction
