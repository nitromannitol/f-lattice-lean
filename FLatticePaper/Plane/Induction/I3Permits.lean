import FLatticePaper.Plane.Induction.I3Application

/-! Task 38: the sheet permit bridge at the matching phase `eps(word) = ε_u`.

The policy `T c i := policy(Z c)(Z i)` of the earlier word, pulled back by the quarter turn, is a quota for the quarter-turned
field (the Laplacian of `quarterTurnField G` at `c` is that of `G` at `Z c`, the harmonic summand having zero Laplacian). The
monotonicity of the chain potential along the policy puts `T` inside the `Ξ`-permit relation `Ξ i ≤ Ξ c`, so the `Ξ`-permits
have the quota (`PermitLocal`), which is the field `permitA` of `SheetLocalInputs`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem i3_mapSite_eq (x : Site) : QuarterTurn.counterclockwise.mapSite (0, -1) x = i3Z x := by
  unfold QuarterTurn.mapSite QuarterTurn.turn i3Z
  ext <;> simp [sub_eq_add_neg]

/-- The Laplacian of the quarter-turned field is the Laplacian of `G` at the quarter-turned site. -/
theorem i3_laplacian_quarterTurn (G : Field) (c : Site) :
    laplacian (quarterTurnField G) c = laplacian G (i3Z c) := by
  have hh := harmonicGrid_harmonic c
  unfold laplacian at hh ⊢
  unfold quarterTurnField
  simp only [i3_mapSite_eq]
  by_cases hc : EvenSite c
  · simp only [i3_Z_neg_even hc, i3_Z_pos_even hc]
    linarith
  · simp only [i3_Z_neg_odd hc, i3_Z_pos_odd hc]
    linarith

/-- The quota of a policy transports to the quarter-turned field through `Z`. -/
theorem i3_retainQuota_quarterTurn (G : Field) (policy : Site → Site → Prop) (hq : RetainQuota G policy) :
    RetainQuota (quarterTurnField G) (fun c i => policy (i3Z c) (i3Z i)) := by
  constructor
  · intro c hc
    rw [i3_laplacian_quarterTurn] at hc
    obtain ⟨h1, h2⟩ := hq.1 (i3Z c) hc
    by_cases hcE : EvenSite c
    · exact ⟨by show policy (i3Z c) (i3Z (incomingNeg c)); rw [i3_Z_neg_even hcE]; exact h1,
        by show policy (i3Z c) (i3Z (incomingPos c)); rw [i3_Z_pos_even hcE]; exact h2⟩
    · exact ⟨by show policy (i3Z c) (i3Z (incomingNeg c)); rw [i3_Z_neg_odd hcE]; exact h2,
        by show policy (i3Z c) (i3Z (incomingPos c)); rw [i3_Z_pos_odd hcE]; exact h1⟩
  · intro c hc
    rw [i3_laplacian_quarterTurn] at hc
    rcases hq.2 (i3Z c) hc with h | h
    · by_cases hcE : EvenSite c
      · exact Or.inl (by show policy (i3Z c) (i3Z (incomingNeg c)); rw [i3_Z_neg_even hcE]; exact h)
      · exact Or.inr (by show policy (i3Z c) (i3Z (incomingPos c)); rw [i3_Z_pos_odd hcE]; exact h)
    · by_cases hcE : EvenSite c
      · exact Or.inr (by show policy (i3Z c) (i3Z (incomingPos c)); rw [i3_Z_pos_even hcE]; exact h)
      · exact Or.inl (by show policy (i3Z c) (i3Z (incomingNeg c)); rw [i3_Z_neg_odd hcE]; exact h)

/-- **The `Ξ`-permits have the quota at the matching phase**: the policy of the earlier word, pulled back by `Z`, lies in
the permit relation `Ξ i ≤ Ξ c` (its monotonicity), and a quota inside a relation gives the quota of the relation. This is the
field `permitA` of `SheetLocalInputs`. -/
theorem i3_permitA_of_strong {word : Word} (h : StrongEstimates (conjWord word)) :
    PermitLocal (quarterTurnField (standardField (conjWord word)))
      (fun c i => sheetChainPotential word (standardField (conjWord word)) i ≤
        sheetChainPotential word (standardField (conjWord word)) c) := by
  obtain ⟨policy, hq, hmono, -⟩ := h.F2F3_policy (frameAt word).eps (frameAt word).eps_unit
  have hT := i3_retainQuota_quarterTurn _ policy hq
  have hsub : ∀ c i, policy (i3Z c) (i3Z i) →
      sheetChainPotential word (standardField (conjWord word)) i ≤
        sheetChainPotential word (standardField (conjWord word)) c := by
    intro c i hp
    rw [i3_sheet_eq_chainPotential, i3_sheet_eq_chainPotential]
    exact hmono (i3Z c) (i3Z i) hp
  rw [← retainQuota_iff_permitLocal]
  constructor
  · intro c hc
    obtain ⟨a, b⟩ := hT.1 c hc
    exact ⟨hsub c _ a, hsub c _ b⟩
  · intro c hc
    rcases hT.2 c hc with a | b
    · exact Or.inl (hsub c _ a)
    · exact Or.inr (hsub c _ b)

end FLatticePaper.Induction
