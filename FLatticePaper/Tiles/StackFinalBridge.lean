import FLatticePaper.Tiles.StackFinal
import FLatticePaper.Tiles.StackTruth

/-! Summary bridges for the final union `F` of `lamO o ℓ (q + 1)` and the relative cells `finRel`. The only fact used
about `F` is its membership: `x ∈ F ↔ x ∈ lamO o ℓ (q+1) ∨ x - posO q+1 ∈ finRel (second letter)`. -/

namespace FLatticePaper.Tiles

theorem oldBitAt_eq (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) (i j : ℕ) (hi : i < 8) (hj : j < 6) :
    oldBitAt o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i j =
      decide (((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) ∈ lamO o ℓ (q + 1)) := by
  have hbd := lamO_bounds' o ℓ q hq
  have hsy0 := plusStep_snd_nonneg' o (ℓ (q + 1))
  have hA2 : (posO o ℓ (q + 1)).2 = (posO o ℓ q).2 + (plusStepO o (ℓ (q + 1))).2 := by
    rw [posO_new']
    simp only [Prod.snd_add]
  have hA1 : (posO o ℓ (q + 1)).1 = (posO o ℓ q).1 + (plusStepO o (ℓ (q + 1))).1 := by
    rw [posO_new']
    simp only [Prod.fst_add]
  simp only [oldBitAt]
  cases hr : rowIdx ((i : ℤ) - 4 + (plusStepO o (ℓ (q + 1))).2) with
  | none =>
    have hPout : ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) ∉
        lamO o ℓ (q + 1) := by
      intro h
      have h1 : (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4) ≤ (posO o ℓ q).2 + 3 := (hbd _ h).1
      have h2 := rowIdx_none hr
      omega
    cases hc : colIdx ((j : ℤ) - 2 + (plusStepO o (ℓ (q + 1))).1) <;>
      simp only [decide_eq_false hPout]
  | some k =>
    cases hc : colIdx ((j : ℤ) - 2 + (plusStepO o (ℓ (q + 1))).1) with
    | none =>
      have hPout : ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) ∉
          lamO o ℓ (q + 1) := by
        intro h
        have hb := hbd _ h
        have hcol := colIdx_none hc
        cases o with
        | horizontal =>
          have h1 := hb.2.1 rfl
          simp only at h1
          have h2 := (plusStep_fst_facts .horizontal (ℓ (q + 1))).1 rfl
          omega
        | vertical =>
          have h1 := hb.2.2 rfl
          simp only at h1
          have h2 := (plusStep_fst_facts .vertical (ℓ (q + 1))).2 rfl
          omega
      simp only [decide_eq_false hPout]
    | some l =>
      dsimp only
      have hr' := rowIdx_some hr
      have hc' := colIdx_some hc
      have hk8 : k < 8 := by omega
      have hl6 : l < 6 := by omega
      rw [stateOf_bits_getD o ℓ q k l hk8 hl6]
      have hpt : ((posO o ℓ q).1 + ((l : ℤ) - 2), (posO o ℓ q).2 + ((k : ℤ) - 4)) =
          ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) := by
        refine Prod.ext ?_ ?_
        · dsimp only
          omega
        · dsimp only
          omega
      rw [hpt]

theorem bits_bridgeF (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) (F : Finset Site)
    (hF : ∀ x, x ∈ F ↔ x ∈ lamO o ℓ (q + 1) ∨ x - posO o ℓ (q + 1) ∈ finRel o (stateOf o ℓ (q + 1)).secondL)
    (i j : ℕ) (hi : i < 8) (hj : j < 6) :
    newBitF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i j =
      decide (((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) ∈ F) := by
  unfold newBitF
  rw [oldBitAt_eq o ℓ q hq i j hi hj]
  have hrel : ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) -
      posO o ℓ (q + 1) = (((j : ℤ) - 2), ((i : ℤ) - 4)) := by
    ext <;> simp
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, anyRel_iff_mem, hF, hrel, iff_self]

theorem ne_bridgeF (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) (F : Finset Site)
    (hF : ∀ x, x ∈ F ↔ x ∈ lamO o ℓ (q + 1) ∨ x - posO o ℓ (q + 1) ∈ finRel o (stateOf o ℓ (q + 1)).secondL)
    (i : ℕ) (hi : i < 8) :
    newNeF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i = decide (RowSet F ((posO o ℓ (q + 1)).2 + ((i : ℤ) - 4))) := by
  have hbd := lamO_bounds' o ℓ q hq
  have hsy0 := plusStep_snd_nonneg' o (ℓ (q + 1))
  have hA2 : (posO o ℓ (q + 1)).2 = (posO o ℓ q).2 + (plusStepO o (ℓ (q + 1))).2 := by
    rw [posO_new']
    simp only [Prod.snd_add]
  have hLeft : RowSet F ((posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) ↔
      (∃ p ∈ lamO o ℓ (q + 1), p.2 = (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) ∨
      (∃ c ∈ finRel o (stateOf o ℓ (q + 1)).secondL, c.2 = (i : ℤ) - 4) := by
    constructor
    · rintro ⟨p, hp, hpy⟩
      rcases (hF p).1 hp with h | h
      · exact Or.inl ⟨p, h, hpy⟩
      · refine Or.inr ⟨p - posO o ℓ (q + 1), h, ?_⟩
        simp only [Prod.snd_sub]
        omega
    · rintro (⟨p, hp, hpy⟩ | ⟨c, hc, hcy⟩)
      · exact ⟨p, (hF p).2 (Or.inl hp), hpy⟩
      · refine ⟨c + posO o ℓ (q + 1), (hF _).2 (Or.inr ?_), ?_⟩
        · rw [add_sub_cancel_right]
          exact hc
        · simp only [Prod.snd_add]
          omega
  rw [Bool.eq_iff_iff]
  unfold newNeF
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, hLeft]
  cases hr : rowIdx ((i : ℤ) - 4 + (plusStepO o (ℓ (q + 1))).2) with
  | none =>
    have hnone : ¬ ∃ p ∈ lamO o ℓ (q + 1), p.2 = (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4) := by
      rintro ⟨p, hp, hpy⟩
      have h1 : p.2 ≤ (posO o ℓ q).2 + 3 := (hbd p hp).1
      have h2 := rowIdx_none hr
      omega
    dsimp only
    simp only [hnone, false_or, Bool.false_eq_true, iff_self]
  | some k =>
    have hr' := rowIdx_some hr
    have hk8 : k < 8 := by omega
    have hk4 : (posO o ℓ q).2 + ((k : ℤ) - 4) = (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4) := by omega
    dsimp only
    rw [stateOf_ne_getD o ℓ q k hk8]
    simp only [decide_eq_true_eq, Finset.filter_nonempty_iff, hk4, iff_self]

end FLatticePaper.Tiles
