import FLatticePaper.Plane.Induction.W1PrivateSquare

/-! # Task 91: the parent square with its rejected output and corner data (the nonfree off-collar `hsq`)

`ParentSquareOut G R z` is the three-step private square of `parentSquare_of_forced`, with: the rejected input `o` of `z` is the unique
retained input of `z`, and each corner `q_i` is black (lap `−1`, both inputs retained by the quota) or a white whose unique retained input is
its successor (`q₀ → q₁`, `q₁ → q₂`, `q₂ → z`). -/

namespace FLatticePaper.W1NonfreeOut

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.W1SheetSquare FLatticePaper.W1PrivateSquare

/-- The three-step private square with the rejected output and the corner data. -/
def ParentSquareOut (G : Field) (R : Site → Site → Prop) (z : Site) : Prop :=
  ∃ q0 q1 q2 o : Site, ∃ a b : ℤ,
    z ∈ squareCorners a b ∧ q0 ∈ squareCorners a b ∧ q1 ∈ squareCorners a b ∧ q2 ∈ squareCorners a b ∧
    (∀ c' ∈ squareCorners a b, c' ≠ z → c' = q0 ∨ c' = q1 ∨ c' = q2) ∧
    q0 ≠ q1 ∧ q1 ≠ q2 ∧ q0 ≠ q2 ∧ (q0 = incomingNeg z ∨ q0 = incomingPos z) ∧ ¬ R z q0 ∧
    Edge q1 q0 ∧ Edge q2 q1 ∧ Edge z q2 ∧ R q0 q1 ∧ R q1 q2 ∧ R q2 z ∧
    (o = incomingNeg z ∨ o = incomingPos z) ∧ o ∉ squareCorners a b ∧ R z o ∧
    (∀ j, R z j → j = o) ∧
    (laplacian G q0 = -1 ∨ (laplacian G q0 = 0 ∧ ∀ j, R q0 j → j = q1)) ∧
    (laplacian G q1 = -1 ∨ (laplacian G q1 = 0 ∧ ∀ j, R q1 j → j = q2)) ∧
    (laplacian G q2 = -1 ∨ (laplacian G q2 = 0 ∧ ∀ j, R q2 j → j = z))

/-- **The parent square with its output and corner data** (task 91). -/
theorem parentSquareOut_of_forced {G : Field} {R : Site → Site → Prop} {c o : Site}
    (hq : RetainQuota G R)
    (hret : ∀ c' i, ForcedEdge G (fun _ _ => False) c' i → R c' i)
    (hfw : ∀ z i, R z i → laplacian G z = 0 → ∀ o', ForcedEdge G (fun _ _ => False) z o' → o' = i)
    (h : ForcedEdge G (fun _ _ => False) c o) : ParentSquareOut G R c := by
  obtain ⟨a, b, inside, hc, hw, ho, hout, hin, hforced⟩ := forced_top_unit h
  -- the retained inputs of a corner `x ≠ c` of the square: its in-square input
  have key : ∀ x ∈ squareCorners a b, x ≠ c → ∀ w ∈ squareCorners a b,
      (w = incomingNeg x ∨ w = incomingPos x) → R x w := by
    intro x hx hxc w hwS hwin
    rcases hin x hx hxc with hb | ⟨hw0, hinS, hinIn⟩
    · have hb2 := hq.1 x hb
      rcases hwin with rfl | rfl
      · exact hb2.1
      · exact hb2.2
    · have hR := hret x (inside x) (hforced x hx hxc hw0)
      have hu := square_input_unique hx hinS hwS hinIn hwin
      rw [hu] at hR
      exact hR
  -- the in-square input `q₀` of `c`, the rejected input (not retained)
  obtain ⟨q0, hq0S, hq0in⟩ := square_corner_input a b hc
  have hq0o : q0 ≠ o := fun e => hout (by rw [← e]; exact hq0S)
  have hq0c : q0 ≠ c := edge_ne (show Edge q0 c from hq0in)
  have hRc0 : ¬ R c q0 := fun hR => hq0o (hfw c q0 hR hw o h).symm
  -- the in-square input `q₁` of `q₀`, retained by `q₀`
  obtain ⟨q1, hq1S, hq1in⟩ := square_corner_input a b hq0S
  have hq1c : q1 ≠ c := fun e => no_two_cycle (show Edge q0 c from hq0in) (e ▸ hq1in)
  have hR01 : R q0 q1 := key q0 hq0S hq0c q1 hq1S hq1in
  -- the in-square input `q₂` of `q₁`, retained by `q₁`
  obtain ⟨q2, hq2S, hq2in⟩ := square_corner_input a b hq1S
  have hq2c : q2 ≠ c := by
    intro e
    have hp : EvenSite q2 ↔ ¬ EvenSite c := by
      rw [edge_parity hq2in, edge_parity hq1in, edge_parity hq0in]
      tauto
    rw [e] at hp
    rcases em (EvenSite c) with h' | h'
    · exact hp.1 h' h'
    · exact h' (hp.2 h')
  have hR12 : R q1 q2 := key q1 hq1S hq1c q2 hq2S hq2in
  have hq1q0 : q1 ≠ q0 := edge_ne hq1in
  have hq2q1 : q2 ≠ q1 := edge_ne hq2in
  have hq2q0 : q2 ≠ q0 := fun e => no_two_cycle hq1in (e ▸ hq2in)
  -- the in-square input of `q₂` is `c`
  have hEc2 : Edge c q2 := by
    obtain ⟨w, hwS, hwin⟩ := square_corner_input a b hq2S
    have hcov := square_exhaust hc hq0S hq1S hq2S hwS (Ne.symm hq0c) (Ne.symm hq1c) (Ne.symm hq2c)
      (Ne.symm hq1q0) (Ne.symm hq2q0) (Ne.symm hq2q1)
    rcases hcov with e | e | e | e
    · rw [e] at hwin
      exact hwin
    · exfalso
      rw [e] at hwin
      have hp := edge_parity hwin
      have hp1 := edge_parity hq1in
      have hp2 := edge_parity hq2in
      have key2 : EvenSite q2 ↔ EvenSite q0 := by
        rw [hp2, hp1, not_not]
      rcases em (EvenSite q0) with h' | h'
      · exact (hp.1 h') (key2.2 h')
      · exact h' (hp.2 (fun h2 => h' (key2.1 h2)))
    · exfalso
      rw [e] at hwin
      exact no_two_cycle hq2in hwin
    · exfalso
      rw [e] at hwin
      exact edge_ne hwin rfl
  have hR2c : R q2 c := key q2 hq2S hq2c c hc hEc2
  have hq0q1 : q0 ≠ q1 := Ne.symm hq1q0
  have hq1q2 : q1 ≠ q2 := Ne.symm hq2q1
  have hq0q2 : q0 ≠ q2 := Ne.symm hq2q0
  refine ⟨q0, q1, q2, o, a, b, hc, hq0S, hq1S, hq2S, ?_, hq0q1, hq1q2, hq0q2, hq0in, hRc0, hq1in, hq2in, hEc2,
    hR01, hR12, hR2c, ho, hout, hret c o h, fun j hj => (hfw c j hj hw o h).symm, ?_, ?_, ?_⟩
  · intro c' hc' hne
    rcases square_exhaust hc hq0S hq1S hq2S hc' (Ne.symm hq0c) (Ne.symm hq1c) (Ne.symm hq2c)
      (Ne.symm hq1q0) (Ne.symm hq2q0) (Ne.symm hq2q1) with e | e | e | e
    · exact absurd e hne
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  · rcases hin q0 hq0S hq0c with hb | ⟨hw0, hinS, hinIn⟩
    · exact Or.inl hb
    · refine Or.inr ⟨hw0, fun j hj => ?_⟩
      have hu := square_input_unique hq0S hinS hq1S hinIn hq1in
      have hj' := hfw q0 j hj hw0 (inside q0) (hforced q0 hq0S hq0c hw0)
      rw [hu] at hj'
      exact hj'.symm
  · rcases hin q1 hq1S hq1c with hb | ⟨hw0, hinS, hinIn⟩
    · exact Or.inl hb
    · refine Or.inr ⟨hw0, fun j hj => ?_⟩
      have hu := square_input_unique hq1S hinS hq2S hinIn hq2in
      have hj' := hfw q1 j hj hw0 (inside q1) (hforced q1 hq1S hq1c hw0)
      rw [hu] at hj'
      exact hj'.symm
  · rcases hin q2 hq2S hq2c with hb | ⟨hw0, hinS, hinIn⟩
    · exact Or.inl hb
    · refine Or.inr ⟨hw0, fun j hj => ?_⟩
      have hu := square_input_unique hq2S hinS hc hinIn hEc2
      have hj' := hfw q2 j hj hw0 (inside q2) (hforced q2 hq2S hq2c hw0)
      rw [hu] at hj'
      exact hj'.symm

end FLatticePaper.W1NonfreeOut
