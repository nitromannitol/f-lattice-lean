import FLatticePaper.Tiles.GlueFull
import FLatticePaper.Tiles.SwapRegsShape
import FLatticePaper.Tiles.SwapNonvac
import FLatticePaper.Tiles.SwapRegionClauses
import FLatticePaper.Tiles.SwapVacuousSpec

/-! # `SwapBaseInput` from the nonvacuous clauses and the vacuous families

The register shapes (`regsAt_fst_shape`, `regsAt_snd_shape`) and the last letter of the word fix which clause applies to which
family. The odd pair (0,1) and the even pairs (0,3), (1,2) use the first register `u1` (`w = u1 d 3^m`); the odd pairs (3,4),
(2,5) and the even pair (4,5) use the second register `u2` (`w = u2 d' 2^m`). The clauses of the nonvacuous families are
`SwapNonvac.clause_N1..N4` and `SwapRegionClauses.clause_N5, N6`; the vacuous ones are the fields of `SwapVacuous`. -/

namespace FLatticePaper.Tiles.SwapBaseInputAssembly

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.JointFamily FLatticePaper.Tiles.GlueFull
open FLatticePaper.Tiles.TileCompatInputs FLatticePaper.Tiles.WeakStepPaper FLatticePaper.Tiles.SurgicalWeak
open FLatticePaper.Tiles.SwapVacuousSpec FLatticePaper.Tiles.SwapRegsShape FLatticePaper.Tiles.SwapNonvac
open FLatticePaper.Tiles.SwapRegionClauses FLatticePaper.Tiles.Standard

/-- A base word is empty, or all three, or all two (with a positive length in the last two cases). -/
theorem base_cases {u : Word} (hu : IsBase u) :
    u = [] ∨ (∃ k : ℕ, 1 ≤ k ∧ u = List.replicate k Digit.three) ∨
      (∃ k : ℕ, 1 ≤ k ∧ u = List.replicate k Digit.two) := by
  rcases hu with h | h | h
  · exact Or.inl h
  · rcases Nat.eq_zero_or_pos u.length with h0 | h0
    · exact Or.inl (List.eq_nil_of_length_eq_zero h0)
    · exact Or.inr (Or.inl ⟨u.length, h0, List.eq_replicate_iff.2 ⟨rfl, h⟩⟩)
  · rcases Nat.eq_zero_or_pos u.length with h0 | h0
    · exact Or.inl (List.eq_nil_of_length_eq_zero h0)
    · exact Or.inr (Or.inr ⟨u.length, h0, List.eq_replicate_iff.2 ⟨rfl, h⟩⟩)

/-- The word `u ++ [d] ++ 2^m`-type shapes with a last letter `three` are not corrected by the last-letter test. -/
theorem last_three_of_rep_three (u : Word) (d : Digit) (m : ℕ) (hm : 1 ≤ m) (w : Word)
    (hw : w = u ++ [d] ++ List.replicate m Digit.three) : w.getLast? = some Digit.three := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [hw, List.replicate_succ', ← List.append_assoc, List.getLast?_append]
  simp

theorem last_two_of_rep_two (u : Word) (d : Digit) (m : ℕ) (hm : 1 ≤ m) (w : Word)
    (hw : w = u ++ [d] ++ List.replicate m Digit.two) : w.getLast? = some Digit.two := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [hw, List.replicate_succ', ← List.append_assoc, List.getLast?_append]
  simp

theorem isBase_of_all_two {w : Word} (h : ∀ x ∈ w, x = Digit.two) : IsBase w :=
  Or.inr (Or.inr h)

theorem isBase_of_all_three {w : Word} (h : ∀ x ∈ w, x = Digit.three) : IsBase w :=
  Or.inr (Or.inl h)

/-- Clause O01 (the odd pair (0,1)): `IsBase u1`, `w` not corrected at three. -/
theorem odd01 (V : SwapVacuous) (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (w u1 u2 : Word)
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f w.length) (hw : ¬ IsBase w)
    (hreg : regsAt w = (some u1, some u2)) (hc : ¬ CorrectedAfterThree w) (hb : IsBase u1) :
    PairCompat (FLatticePaper.Tiles.GlueFull.oddFull f w) 0 1 := by
  obtain ⟨d, m, hd, hshape⟩ := regsAt_fst_shape w u1 (by rw [hreg])
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [List.replicate_zero, List.append_nil] at hshape
    rcases hd with rfl | rfl
    · rcases base_cases hb with h | ⟨k, hk, h⟩ | ⟨k, hk, h⟩
      · subst h
        exact (V.V5 D f w hS (by simp [hshape]) hG).1
      · subst h
        exact (V.V3 D f k w hS hk (by simp [hshape]) hG).1
      · subst h
        exact (V.V4 D f k w hS hk (by simp [hshape]) hG).1
    · rcases base_cases hb with h | ⟨k, hk, h⟩ | ⟨k, hk, h⟩
      · subst h
        exfalso
        apply hw
        rw [hshape]
        exact isBase_of_all_two (by intro x hx; simpa using hx)
      · subst h
        obtain ⟨m', rfl⟩ : ∃ m', k = m' + 1 := ⟨k - 1, by omega⟩
        exact clause_N1 D hS f w m' (by simp [hshape]) hG
      · subst h
        exfalso
        apply hw
        rw [hshape]
        exact isBase_of_all_two (by
          intro x hx
          rw [List.mem_append] at hx
          rcases hx with hx | hx
          · exact List.eq_of_mem_replicate hx
          · simpa using hx)
  · exfalso
    apply hc
    exact ⟨hw, last_three_of_rep_three u1 d m hm w hshape⟩

/-- Clauses O34 and O25 (the odd pairs (3,4), (2,5) on the even tile of `u2`): `IsBase u2`, `w` not corrected at three. -/
theorem odd34_25 (V : SwapVacuous) (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (w u1 u2 : Word)
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f w.length) (hw : ¬ IsBase w)
    (hreg : regsAt w = (some u1, some u2)) (hc : ¬ CorrectedAfterThree w) (hb : IsBase u2) :
    PairCompat (FLatticePaper.Tiles.GlueFull.oddFull f w) 3 4 ∧
      PairCompat (FLatticePaper.Tiles.GlueFull.oddFull f w) 2 5 := by
  obtain ⟨d, m, hd, hshape⟩ := regsAt_snd_shape w u2 (by rw [hreg])
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [List.replicate_zero, List.append_nil] at hshape
    rcases hd with rfl | rfl
    · rcases base_cases hb with h | ⟨k, hk, h⟩ | ⟨k, hk, h⟩
      · subst h
        exact ⟨(V.V5 D f w hS (by simp [hshape]) hG).2.1, clause_N2 D hS f w 0 (by simp [hshape]) hG⟩
      · subst h
        exact ⟨(V.V3 D f k w hS hk (by simp [hshape]) hG).2.1, clause_N2 D hS f w k (by simp [hshape]) hG⟩
      · subst h
        exact ⟨(V.V4 D f k w hS hk (by simp [hshape]) hG).2.1, clause_N5 D hS f w k hk (by simp [hshape]) hG⟩
    · exact absurd ⟨hw, by simp [hshape]⟩ hc
  · by_cases hex : d = Digit.three ∧ m = 1 ∧ ∀ x ∈ u2, x = Digit.three
    · obtain ⟨rfl, rfl, hall⟩ := hex
      obtain ⟨k, hk⟩ : ∃ k, u2 = List.replicate k Digit.three := ⟨u2.length, List.eq_replicate_iff.2 ⟨rfl, hall⟩⟩
      subst hk
      have hw' : w = List.replicate (k + 1) Digit.three ++ [Digit.two] := by
        rw [hshape]
        simp [List.replicate_succ', List.append_assoc]
      exact V.V1 D f k w hS hw' hG
    · exact V.V2 D f u2 d m w hS hb hd hm hex hshape hG

/-- Clauses (0,3) and (1,2) of the even child (the odd tile of `u1`): `IsBase u1`, `w` not corrected at two. -/
theorem even03_12 (V : SwapVacuous) (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (w u1 u2 : Word)
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f w.length) (hw : ¬ IsBase w)
    (hreg : regsAt w = (some u1, some u2)) (hc : ¬ CorrectedAfterTwo w) (hb : IsBase u1) :
    PairCompat (FLatticePaper.Tiles.GlueFull.evenFull f w) 0 3 ∧
      PairCompat (FLatticePaper.Tiles.GlueFull.evenFull f w) 1 2 := by
  obtain ⟨d, m, hd, hshape⟩ := regsAt_fst_shape w u1 (by rw [hreg])
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [List.replicate_zero, List.append_nil] at hshape
    rcases hd with rfl | rfl
    · rcases base_cases hb with h | ⟨k, hk, h⟩ | ⟨k, hk, h⟩
      · subst h
        exact ⟨(V.V5 D f w hS (by simp [hshape]) hG).2.2.1, clause_N4 D hS f w 0 (by simp [hshape]) hG⟩
      · subst h
        exact ⟨(V.V3 D f k w hS hk (by simp [hshape]) hG).2.2.1, clause_N6 D hS f w k hk (by simp [hshape]) hG⟩
      · subst h
        exact ⟨(V.V4 D f k w hS hk (by simp [hshape]) hG).2.2.1, clause_N4 D hS f w k (by simp [hshape]) hG⟩
    · exact absurd ⟨hw, by simp [hshape]⟩ hc
  · by_cases hex : d = Digit.two ∧ m = 1 ∧ ∀ x ∈ u1, x = Digit.two
    · obtain ⟨rfl, rfl, hall⟩ := hex
      obtain ⟨k, hk⟩ : ∃ k, u1 = List.replicate k Digit.two := ⟨u1.length, List.eq_replicate_iff.2 ⟨rfl, hall⟩⟩
      subst hk
      have hw' : w = List.replicate (k + 1) Digit.two ++ [Digit.three] := by
        rw [hshape]
        simp [List.replicate_succ', List.append_assoc]
      exact V.V6 D f k w hS hw' hG
    · exact V.V7 D f u1 d m w hS hb hd hm hex hshape hG

/-- Clause (4,5) of the even child (the even tile of `u2`): `IsBase u2`, `w` not corrected at two. -/
theorem even45 (V : SwapVacuous) (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (w u1 u2 : Word)
    (hG : FLatticePaper.Tiles.JointInduction.GoodBelow D f w.length) (hw : ¬ IsBase w)
    (hreg : regsAt w = (some u1, some u2)) (hc : ¬ CorrectedAfterTwo w) (hb : IsBase u2) :
    PairCompat (FLatticePaper.Tiles.GlueFull.evenFull f w) 4 5 := by
  obtain ⟨d, m, hd, hshape⟩ := regsAt_snd_shape w u2 (by rw [hreg])
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [List.replicate_zero, List.append_nil] at hshape
    rcases hd with rfl | rfl
    · rcases base_cases hb with h | ⟨k, hk, h⟩ | ⟨k, hk, h⟩
      · subst h
        exact (V.V5 D f w hS (by simp [hshape]) hG).2.2.2
      · subst h
        exact (V.V3 D f k w hS hk (by simp [hshape]) hG).2.2.2
      · subst h
        exact (V.V4 D f k w hS hk (by simp [hshape]) hG).2.2.2
    · rcases base_cases hb with h | ⟨k, hk, h⟩ | ⟨k, hk, h⟩
      · subst h
        exact absurd (show IsBase w from by
          rw [hshape]
          exact isBase_of_all_three (by intro x hx; simpa using hx)) hw
      · subst h
        exact absurd (show IsBase w from by
          rw [hshape]
          refine isBase_of_all_three (fun x hx => ?_)
          rcases List.mem_append.1 hx with h | h
          · exact List.eq_of_mem_replicate h
          · simpa using h) hw
      · subst h
        obtain ⟨m', rfl⟩ : ∃ m', k = m' + 1 := ⟨k - 1, by omega⟩
        exact clause_N3 D hS f w m' (by simp [hshape]) hG
  · exact (hc ⟨hw, last_two_of_rep_two u2 d m hm w hshape⟩).elim

/-- `SwapBaseInput` from the vacuous families and the nonvacuous clauses. -/
theorem swapBaseInput_of (V : SwapVacuous) (D : JointData) : SwapBaseInput D := by
  unfold SwapBaseInput
  intro hS f w u1 u2 hG hw hreg
  exact ⟨fun hc => ⟨fun hb1 => odd01 V D hS f w u1 u2 hG hw hreg hc hb1,
      fun hb2 => odd34_25 V D hS f w u1 u2 hG hw hreg hc hb2⟩,
    fun hc => ⟨fun hb1 => even03_12 V D hS f w u1 u2 hG hw hreg hc hb1,
      fun hb2 => even45 V D hS f w u1 u2 hG hw hreg hc hb2⟩⟩

end FLatticePaper.Tiles.SwapBaseInputAssembly
