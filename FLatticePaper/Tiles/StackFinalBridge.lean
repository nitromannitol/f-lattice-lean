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

/-! The finite facts about the relative cells of the final pieces. -/

theorem finRel_bounds (o : Orientation) (l1 : Letter) :
    ∀ c ∈ finRel o l1, -2 ≤ c.1 ∧ c.1 ≤ 3 ∧ -3 ≤ c.2 ∧ c.2 ≤ 3 := by
  cases o <;> cases l1 <;> decide

theorem finRel_zero (o : Orientation) (l1 : Letter) : ((0 : ℤ), (0 : ℤ)) ∈ finRel o l1 := by
  cases o <;> cases l1 <;> decide

theorem finRel_one (o : Orientation) (l1 : Letter) : ((0 : ℤ), (1 : ℤ)) ∈ finRel o l1 := by
  cases o <;> cases l1 <;> decide

theorem finRel_lower (o : Orientation) (l1 : Letter) :
    ∀ d ∈ finRel o l1, d.2 ≤ 0 → ∀ z ∈ Finset.Icc d.2 0, ∃ e ∈ finRel o l1, e.2 = z := by
  cases o <;> cases l1 <;> decide

theorem finRel_upper (o : Orientation) (l1 : Letter) :
    ∀ d ∈ finRel o l1, 0 ≤ d.2 → ∀ z ∈ Finset.Icc 0 d.2, ∃ e ∈ finRel o l1, e.2 = z := by
  cases o <;> cases l1 <;> decide

/-- A cell of the final union outside the old union lies in the window columns. -/
theorem old_of_not_windowF (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (F : Finset Site)
    (hF : ∀ x, x ∈ F ↔ x ∈ lamO o ℓ (q + 1) ∨ x - posO o ℓ (q + 1) ∈ finRel o (stateOf o ℓ (q + 1)).secondL)
    (p : Site) (hp : p ∈ F)
    (hcol : ¬ (-2 ≤ p.1 - (posO o ℓ (q + 1)).1 ∧ p.1 - (posO o ℓ (q + 1)).1 ≤ 3)) :
    p ∈ lamO o ℓ (q + 1) := by
  rcases (hF p).1 hp with h | h
  · exact h
  · exfalso
    apply hcol
    have hb := finRel_bounds o _ _ h
    simp only [Prod.fst_sub] at hb
    omega

theorem pair_succ_iffF (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (F : Finset Site)
    (hF : ∀ x, x ∈ F ↔ x ∈ lamO o ℓ (q + 1) ∨ x - posO o ℓ (q + 1) ∈ finRel o (stateOf o ℓ (q + 1)).secondL)
    (dy : ℤ) :
    (∃ x, (x, (posO o ℓ (q + 1)).2 + dy) ∈ F ∧ (x, (posO o ℓ (q + 1)).2 + dy + 1) ∈ F) ↔
    (∃ x, (x, (posO o ℓ (q + 1)).2 + dy) ∈ lamO o ℓ (q + 1) ∧
      (x, (posO o ℓ (q + 1)).2 + dy + 1) ∈ lamO o ℓ (q + 1)) ∨
    (∃ j : ℕ, j < 6 ∧
      ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + dy) ∈ F ∧
      ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + dy + 1) ∈ F) := by
  constructor
  · rintro ⟨x, h1, h2⟩
    by_cases hc : -2 ≤ x - (posO o ℓ (q + 1)).1 ∧ x - (posO o ℓ (q + 1)).1 ≤ 3
    · obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = x - (posO o ℓ (q + 1)).1 + 2 :=
        ⟨(x - (posO o ℓ (q + 1)).1 + 2).toNat, Int.toNat_of_nonneg (by omega)⟩
      have hjx : (posO o ℓ (q + 1)).1 + ((j : ℤ) - 2) = x := by omega
      refine Or.inr ⟨j, by omega, ?_, ?_⟩
      · rw [hjx]
        exact h1
      · rw [hjx]
        exact h2
    · left
      exact ⟨x, old_of_not_windowF o ℓ q F hF _ h1 hc, old_of_not_windowF o ℓ q F hF _ h2 hc⟩
  · rintro (⟨x, h1, h2⟩ | ⟨j, _, h1, h2⟩)
    · exact ⟨x, (hF _).2 (Or.inl h1), (hF _).2 (Or.inl h2)⟩
    · exact ⟨_, h1, h2⟩
/-- The pair-share bridge of the final union. -/
theorem sh_bridgeF (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) (F : Finset Site)
    (hF : ∀ x, x ∈ F ↔ x ∈ lamO o ℓ (q + 1) ∨ x - posO o ℓ (q + 1) ∈ finRel o (stateOf o ℓ (q + 1)).secondL)
    (k : ℕ) (hk : k < 7) :
    newShF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) k =
      decide (((F.image Prod.fst).filter (fun x => (x, (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4)) ∈ F ∧
        (x, (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4) + 1) ∈ F)).Nonempty) := by
  have hbd := lamO_bounds' o ℓ q hq
  have hsy0 := plusStep_snd_nonneg' o (ℓ (q + 1))
  have hA2 : (posO o ℓ (q + 1)).2 = (posO o ℓ q).2 + (plusStepO o (ℓ (q + 1))).2 := by
    rw [posO_new']
    simp only [Prod.snd_add]
  have hwin : ∀ j : ℕ, j < 6 → (newBitF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) k j = true ↔
      ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4)) ∈ F) := by
    intro j hj
    rw [bits_bridgeF o ℓ q hq F hF k j (by omega) hj, decide_eq_true_eq]
  have hwin' : ∀ j : ℕ, j < 6 → (newBitF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) (k + 1) j = true ↔
      ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4) + 1) ∈ F) := by
    intro j hj
    have e : ((k + 1 : ℕ) : ℤ) - 4 = (k : ℤ) - 4 + 1 := by push_cast; ring
    simp only [bits_bridgeF o ℓ q hq F hF (k + 1) j (by omega) hj, e, decide_eq_true_eq, ← add_assoc, iff_self]
  have hWin : (∃ x, x < 6 ∧ newBitF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) k x = true ∧
      newBitF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) (k + 1) x = true) ↔
      (∃ j : ℕ, j < 6 ∧
        ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4)) ∈ F ∧
        ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4) + 1) ∈ F) := by
    constructor
    · rintro ⟨x, hx, h1, h2⟩
      exact ⟨x, hx, (hwin x hx).1 h1, (hwin' x hx).1 h2⟩
    · rintro ⟨x, hx, h1, h2⟩
      exact ⟨x, hx, (hwin x hx).2 h1, (hwin' x hx).2 h2⟩
  rw [Bool.eq_iff_iff]
  unfold newShF
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    Finset.filter_nonempty_iff, img_pair_iff]
  rw [pair_succ_iffF o ℓ q F hF ((k : ℤ) - 4), hWin]
  cases hp : pairIdx ((k : ℤ) - 4 + (plusStepO o (ℓ (q + 1))).2) with
  | none =>
    have hnone : ¬ ∃ x, (x, (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4)) ∈ lamO o ℓ (q + 1) ∧
        (x, (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4) + 1) ∈ lamO o ℓ (q + 1) := by
      rintro ⟨x, _, h2⟩
      have h2' : (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4) + 1 ≤ (posO o ℓ q).2 + 3 := (hbd _ h2).1
      have h3 := pairIdx_none hp
      omega
    dsimp only
    simp only [hnone, false_or, Bool.false_eq_true, iff_self]
  | some m =>
    have hp' := pairIdx_some hp
    have hm7 : m < 7 := by omega
    have hY : (posO o ℓ q).2 + ((m : ℤ) - 4) = (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4) := by omega
    dsimp only
    rw [stateOf_sh_getD o ℓ q m hm7]
    simp only [decide_eq_true_eq, Finset.filter_nonempty_iff, img_pair_iff, hY, iff_self]

end FLatticePaper.Tiles
