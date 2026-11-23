import FLatticePaper.Plane.Induction.W1SheetSquare

/-! # Task 88: the three-step private square of a forcing square (the lead's nonfree hpar)

The top unit of an unseeded forced derivation of a white `c` is a unit square `Q ∋ c` whose other corners are black or white with an inside
input in `Q` (`forced_top_unit`). Each corner of `Q` has exactly one input in `Q` (`square_corner_input`), so the inside inputs form the
four-cycle of `Q`: `c ← q₀ ← q₁ ← q₂ ← c` (`q₀` the in-square input of `c`). The rejected input `o` of `c` is outside `Q`, so `q₀` is not
retained by `c` (`forcedWhiteUnique`), and each `qᵢ` keeps its in-square input (black corners keep both inputs by the quota; white corners keep
their forced inside input by `forcedRetained`). This is `ParentSquare` (`parentSquare_of_forced`). -/

namespace FLatticePaper.W1PrivateSquare

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.W1SheetSquare

theorem edge_parity {y x : Site} (h : Edge y x) : EvenSite y ↔ ¬ EvenSite x := by
  obtain ⟨y1, y2⟩ := y
  obtain ⟨x1, x2⟩ := x
  unfold Edge incomingNeg incomingPos EvenSite at *
  split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> omega

theorem edge_ne {y x : Site} (h : Edge y x) : y ≠ x := by
  obtain ⟨y1, y2⟩ := y
  obtain ⟨x1, x2⟩ := x
  intro e
  simp only [Prod.mk.injEq] at e
  unfold Edge incomingNeg incomingPos at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> omega

theorem no_two_cycle {x y : Site} (h1 : Edge y x) (h2 : Edge x y) : False := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  unfold Edge incomingNeg incomingPos EvenSite at h1 h2
  split_ifs at h1 h2 <;> simp only [Prod.mk.injEq] at h1 h2 <;> omega

theorem not_both_inputs_in_square {a b : ℤ} {x : Site} (hx : x ∈ squareCorners a b)
    (hn : incomingNeg x ∈ squareCorners a b) (hp : incomingPos x ∈ squareCorners a b) : False := by
  obtain ⟨x1, x2⟩ := x
  simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hx hn hp
  simp only [incomingNeg, incomingPos] at hn hp
  split_ifs at hn hp <;> simp only [Prod.mk.injEq] at hx hn hp <;> omega

/-- The in-square input of a corner is unique. -/
theorem square_input_unique {a b : ℤ} {x w1 w2 : Site} (hx : x ∈ squareCorners a b)
    (hw1 : w1 ∈ squareCorners a b) (hw2 : w2 ∈ squareCorners a b)
    (h1 : w1 = incomingNeg x ∨ w1 = incomingPos x) (h2 : w2 = incomingNeg x ∨ w2 = incomingPos x) : w1 = w2 := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · rw [h1, h2]
  · exact (not_both_inputs_in_square hx (by rw [← h1]; exact hw1) (by rw [← h2]; exact hw2)).elim
  · exact (not_both_inputs_in_square hx (by rw [← h2]; exact hw2) (by rw [← h1]; exact hw1)).elim
  · rw [h1, h2]

/-- Exhaustion: four distinct corners of a unit square are all its corners. -/
theorem square_exhaust {a b : ℤ} {x y z w c' : Site} (hx : x ∈ squareCorners a b) (hy : y ∈ squareCorners a b)
    (hz : z ∈ squareCorners a b) (hw : w ∈ squareCorners a b) (hc' : c' ∈ squareCorners a b)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    c' = x ∨ c' = y ∨ c' = z ∨ c' = w := by
  classical
  set s : Finset Site := {x, y, z, w} with hs
  have hsub : s ⊆ squareCorners a b := by
    intro p hp
    simp only [hs, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption
  have hcard : s.card = 4 := by
    rw [hs, Finset.card_insert_of_notMem (by simp [hxy, hxz, hxw]),
      Finset.card_insert_of_notMem (by simp [hyz, hyw]), Finset.card_pair hzw]
  have hle : (squareCorners a b).card ≤ 4 := by
    have h1 := Finset.card_insert_le (a, b) ({(a + 1, b), (a, b + 1), (a + 1, b + 1)} : Finset Site)
    have h2 := Finset.card_insert_le (a + 1, b) ({(a, b + 1), (a + 1, b + 1)} : Finset Site)
    have h3 := Finset.card_insert_le (a, b + 1) ({(a + 1, b + 1)} : Finset Site)
    have h4 := Finset.card_singleton (a + 1, b + 1)
    unfold squareCorners
    omega
  have heq : s = squareCorners a b := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hm : c' ∈ s := by rw [heq]; exact hc'
  simpa [hs, Finset.mem_insert, Finset.mem_singleton] using hm

/-- The top unit of an unseeded forced derivation of `c`. -/
theorem forced_top_unit {G : Field} {c o : Site} (h : ForcedEdge G (fun _ _ => False) c o) :
    ∃ a b : ℤ, ∃ inside : Site → Site, c ∈ squareCorners a b ∧ laplacian G c = 0 ∧
      (o = incomingNeg c ∨ o = incomingPos c) ∧ o ∉ squareCorners a b ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian G c' = -1 ∨
        (laplacian G c' = 0 ∧ inside c' ∈ squareCorners a b ∧
          (inside c' = incomingNeg c' ∨ inside c' = incomingPos c'))) ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian G c' = 0 → ForcedEdge G (fun _ _ => False) c' (inside c')) := by
  cases h with
  | seed hs => exact False.elim hs
  | @unit a b _ _ inside hc hw ho hout hin hforced => exact ⟨a, b, inside, hc, hw, ho, hout, hin, hforced⟩

set_option maxHeartbeats 400000 in
/-- **The three-step private square of a forcing square** (task 88). For an unseeded forced white `c` with the rejected input `o` (from
`ForcedEdge`), the quota, the forced edges retained, and the forced whites' uniqueness, the parent square data `ParentSquare` holds at `c`. -/
theorem parentSquare_of_forced {G : Field} {R : Site → Site → Prop} {c o : Site}
    (hq : RetainQuota G R)
    (hret : ∀ c' i, ForcedEdge G (fun _ _ => False) c' i → R c' i)
    (hfw : ∀ z i, R z i → laplacian G z = 0 → ∀ o', ForcedEdge G (fun _ _ => False) z o' → o' = i)
    (h : ForcedEdge G (fun _ _ => False) c o) : ParentSquare R c := by
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
  refine ⟨q0, q1, q2, a, b, hc, hq0S, hq1S, hq2S, ?_, hq0q1, hq1q2, hq0q2, hq0in, hRc0, hq1in, hq2in, hEc2,
    hR01, hR12, hR2c⟩
  · intro c' hc' hne
    rcases square_exhaust hc hq0S hq1S hq2S hc' (Ne.symm hq0c) (Ne.symm hq1c) (Ne.symm hq2c)
      (Ne.symm hq1q0) (Ne.symm hq2q0) (Ne.symm hq2q1) with e | e | e | e
    · exact absurd e hne
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)

end FLatticePaper.W1PrivateSquare
