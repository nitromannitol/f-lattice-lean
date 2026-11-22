import FLatticePaper.Tiles.StackBridge

/-! The bridge: the summary of the union of `q + 2` letters is the transition of the summary of `q + 1` letters. -/

namespace FLatticePaper.Tiles

theorem rel_bounds (o : Orientation) (a : Letter) (ep : Bool) :
    ∀ r ∈ relCells o a ep, -2 ≤ r.1 ∧ r.1 ≤ 3 ∧ -3 ≤ r.2 ∧ r.2 ≤ 3 := by
  cases o <;> cases a <;> cases ep <;> decide

/-- The window bounds of the old union, orientation-free form. -/
theorem lamO_bounds' (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) :
    ∀ x ∈ lamO o ℓ (q + 1),
      x.2 ≤ (posO o ℓ q).2 + 3 ∧
      (o = Orientation.horizontal → x.1 ≤ (posO o ℓ q).1 + 3) ∧
      (o = Orientation.vertical → (posO o ℓ q).1 ≤ x.1) := by
  intro x hx
  cases o with
  | horizontal =>
    obtain ⟨h1, h2⟩ := lamO_bounds_h ℓ q hq x hx
    exact ⟨h1, (fun _ => h2), (fun h => by cases h)⟩
  | vertical =>
    obtain ⟨h1, h2⟩ := lamO_bounds_v ℓ q hq x hx
    exact ⟨h1, (fun h => by cases h), (fun _ => h2)⟩

/-- The new anchor is the old one plus the plus step of the new letter. -/
theorem posO_new' (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) :
    posO o ℓ (q + 1) = posO o ℓ q + plusStepO o (ℓ (q + 1)) := rfl

theorem getD_map_range {β : Type} (f : ℕ → β) (n k : ℕ) (d : β) (hk : k < n) :
    ((List.range n).map f).getD k d = f k := by
  simp [List.getD_eq_getElem?_getD, hk]

/-- The row-nonempty flags of the actual summary. -/
theorem stateOf_ne_getD (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (k : ℕ) (hk : k < 8) :
    (stateOf o ℓ (q + 1)).ne.getD k false =
      decide (((lamO o ℓ (q + 1)).filter (fun p => p.2 = (posO o ℓ q).2 + ((k : ℤ) - 4))).Nonempty) := by
  unfold stateOf
  simp only [Nat.add_sub_cancel]
  exact getD_map_range _ 8 k false hk

/-- The window bits of the actual summary. -/
theorem stateOf_bits_getD (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (k l : ℕ) (hk : k < 8) (hl : l < 6) :
    ((stateOf o ℓ (q + 1)).bits.getD k []).getD l false =
      decide (((posO o ℓ q).1 + ((l : ℤ) - 2), (posO o ℓ q).2 + ((k : ℤ) - 4)) ∈ lamO o ℓ (q + 1)) := by
  unfold stateOf
  simp only [Nat.add_sub_cancel]
  rw [getD_map_range _ 8 k [] hk]
  exact getD_map_range _ 6 l false hl

/-- The pair flags of the actual summary. -/
theorem stateOf_sh_getD (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (k : ℕ) (hk : k < 7) :
    (stateOf o ℓ (q + 1)).sh.getD k false =
      decide ((((lamO o ℓ (q + 1)).image Prod.fst).filter (fun x =>
        (x, (posO o ℓ q).2 + ((k : ℤ) - 4)) ∈ lamO o ℓ (q + 1) ∧
        (x, (posO o ℓ q).2 + ((k : ℤ) - 4) + 1) ∈ lamO o ℓ (q + 1))).Nonempty) := by
  unfold stateOf
  simp only [Nat.add_sub_cancel]
  exact getD_map_range _ 7 k false hk

/-- The enlargement flag of the new tile, as seen from the summary. -/
theorem enlarge_eq (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) :
    enlargeNew o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) = flagO o ℓ (q + 1) := by
  unfold enlargeNew stateOf flagO
  simp only [Nat.add_sub_cancel]

/-- Rows of the old union with a row-index outside the window carry no cells. -/
theorem row_four_empty (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) (x : Site)
    (hx : x ∈ lamO o ℓ (q + 1)) : x.2 ≤ (posO o ℓ q).2 + 3 :=
  (lamO_bounds' o ℓ q hq x hx).1

theorem rowIdx_some {dy : ℤ} {k : ℕ} (h : rowIdx dy = some k) : -4 ≤ dy ∧ dy ≤ 3 ∧ (k : ℤ) = dy + 4 := by
  unfold rowIdx at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  omega

theorem rowIdx_none {dy : ℤ} (h : rowIdx dy = none) : ¬ (-4 ≤ dy ∧ dy ≤ 3) := by
  intro hc
  unfold rowIdx at h
  rw [if_pos hc] at h
  simp at h

theorem colIdx_some {c : ℤ} {k : ℕ} (h : colIdx c = some k) : -2 ≤ c ∧ c ≤ 3 ∧ (k : ℤ) = c + 2 := by
  unfold colIdx at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  omega

theorem colIdx_none {c : ℤ} (h : colIdx c = none) : ¬ (-2 ≤ c ∧ c ≤ 3) := by
  intro hc
  unfold colIdx at h
  rw [if_pos hc] at h
  simp at h

theorem plusStep_snd_nonneg' (o : Orientation) (l : Letter) : 0 ≤ (plusStepO o l).2 := by
  cases o <;> cases l <;> decide

/-- Horizontal plus steps move right by at least one column; vertical ones move left by at most one. -/
theorem plusStep_fst_facts (o : Orientation) (l : Letter) :
    (o = Orientation.horizontal → 1 ≤ (plusStepO o l).1) ∧ (o = Orientation.vertical → (plusStepO o l).1 ≤ 0) := by
  cases o <;> cases l <;> decide

theorem anyRel_iff_mem (L : List Site) (t : Site) :
    (L.any (fun p => decide (p = t))) = true ↔ t ∈ L := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hxt⟩
    have hxt' : x = t := of_decide_eq_true hxt
    subst hxt'
    exact hx
  · intro ht
    exact ⟨t, ht, by simp⟩

/-- The window bit of the new union at row `i`, column `j`. -/
theorem bits_bridge (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) (i j : ℕ) (hi : i < 8) (hj : j < 6) :
    newBit o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i j =
      decide (((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) ∈ lamO o ℓ (q + 2)) := by
  have hbd := lamO_bounds' o ℓ q hq
  have hsy0 := plusStep_snd_nonneg' o (ℓ (q + 1))
  have hsxf := plusStep_fst_facts o (ℓ (q + 1))
  obtain ⟨P, hP⟩ : ∃ P : Site, P = ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) :=
    ⟨_, rfl⟩
  rw [← hP]
  have hP1 : P.1 = (posO o ℓ q).1 + ((plusStepO o (ℓ (q + 1))).1 + ((j : ℤ) - 2)) := by
    rw [hP, posO_new']
    simp only [Prod.fst_add]
    omega
  have hP2 : P.2 = (posO o ℓ q).2 + ((plusStepO o (ℓ (q + 1))).2 + ((i : ℤ) - 4)) := by
    rw [hP, posO_new']
    simp only [Prod.snd_add]
    omega
  have hkey := mem_lamO_succ o ℓ q hq P
  have hrel : P - posO o ℓ (q + 1) = (((j : ℤ) - 2), ((i : ℤ) - 4)) := by
    rw [hP]
    ext <;> simp
  rw [hrel] at hkey
  unfold newBit
  simp only [enlarge_eq]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  rw [hkey, anyRel_iff_mem]
  cases hr : rowIdx ((i : ℤ) - 4 + (plusStepO o (ℓ (q + 1))).2) with
  | none =>
    have hPout : P ∉ lamO o ℓ (q + 1) := by
      intro h
      have h1 := (hbd P h).1
      have h2 := rowIdx_none hr
      omega
    cases hc : colIdx ((j : ℤ) - 2 + (plusStepO o (ℓ (q + 1))).1) <;>
      (dsimp only; simp only [hPout, false_or, Bool.false_eq_true, iff_self])
  | some k =>
    cases hc : colIdx ((j : ℤ) - 2 + (plusStepO o (ℓ (q + 1))).1) with
    | none =>
      have hPout : P ∉ lamO o ℓ (q + 1) := by
        intro h
        have hb := hbd P h
        have hcol := colIdx_none hc
        cases o with
        | horizontal =>
          have h1 := hb.2.1 rfl
          have h2 := hsxf.1 rfl
          omega
        | vertical =>
          have h1 := hb.2.2 rfl
          have h2 := hsxf.2 rfl
          omega
      dsimp only
      simp only [hPout, false_or, Bool.false_eq_true, iff_self]
    | some l =>
      have hr' := rowIdx_some hr
      have hc' := colIdx_some hc
      have hk8 : k < 8 := by omega
      have hl6 : l < 6 := by omega
      have hpt : ((posO o ℓ q).1 + ((l : ℤ) - 2), (posO o ℓ q).2 + ((k : ℤ) - 4)) = P := by
        refine Prod.ext ?_ ?_
        · dsimp only
          omega
        · dsimp only
          omega
      dsimp only
      rw [stateOf_bits_getD o ℓ q k l hk8 hl6, hpt]
      simp only [decide_eq_true_eq, iff_self]

theorem pairIdx_some {dy : ℤ} {m : ℕ} (h : pairIdx dy = some m) : -4 ≤ dy ∧ dy ≤ 2 ∧ (m : ℤ) = dy + 4 := by
  unfold pairIdx at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  omega

theorem pairIdx_none {dy : ℤ} (h : pairIdx dy = none) : ¬ (-4 ≤ dy ∧ dy ≤ 2) := by
  intro hc
  unfold pairIdx at h
  rw [if_pos hc] at h
  simp at h

theorem img_pair_iff (L : Finset Site) (Y : ℤ) :
    (∃ x ∈ L.image Prod.fst, (x, Y) ∈ L ∧ (x, Y + 1) ∈ L) ↔ ∃ x, (x, Y) ∈ L ∧ (x, Y + 1) ∈ L := by
  constructor
  · rintro ⟨x, _, h⟩
    exact ⟨x, h⟩
  · rintro ⟨x, h⟩
    exact ⟨x, Finset.mem_image.2 ⟨(x, Y), h.1, rfl⟩, h⟩

theorem rel_col_window (o : Orientation) (a : Letter) (ep : Bool) (r : Site) (hr : r ∈ relCells o a ep) :
    -2 ≤ r.1 ∧ r.1 ≤ 3 := by
  have := rel_bounds o a ep r hr
  omega

/-- A point of the new union outside the window columns already lies in the old union. -/
theorem old_of_not_window (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) (p : Site)
    (hp : p ∈ lamO o ℓ (q + 2))
    (hcol : ¬ (-2 ≤ p.1 - (posO o ℓ (q + 1)).1 ∧ p.1 - (posO o ℓ (q + 1)).1 ≤ 3)) :
    p ∈ lamO o ℓ (q + 1) := by
  rcases (mem_lamO_succ o ℓ q hq p).1 hp with h | h
  · exact h
  · exfalso
    apply hcol
    have hb := rel_col_window o (ℓ (q + 1)) (flagO o ℓ (q + 1)) (p - posO o ℓ (q + 1)) h
    simp only [Prod.fst_sub] at hb
    exact hb

/-- A shared pair of the new union is either an old shared pair or a shared pair inside the window. -/
theorem pair_succ_iff (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) (dy : ℤ) :
    (∃ x, (x, (posO o ℓ (q + 1)).2 + dy) ∈ lamO o ℓ (q + 2) ∧
      (x, (posO o ℓ (q + 1)).2 + dy + 1) ∈ lamO o ℓ (q + 2)) ↔
    (∃ x, (x, (posO o ℓ (q + 1)).2 + dy) ∈ lamO o ℓ (q + 1) ∧
      (x, (posO o ℓ (q + 1)).2 + dy + 1) ∈ lamO o ℓ (q + 1)) ∨
    (∃ j : ℕ, j < 6 ∧
      ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + dy) ∈ lamO o ℓ (q + 2) ∧
      ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + dy + 1) ∈ lamO o ℓ (q + 2)) := by
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
      exact ⟨x, old_of_not_window o ℓ q hq _ h1 hc, old_of_not_window o ℓ q hq _ h2 hc⟩
  · rintro (⟨x, h1, h2⟩ | ⟨j, _, h1, h2⟩)
    · exact ⟨x, (mem_lamO_succ o ℓ q hq _).2 (Or.inl h1), (mem_lamO_succ o ℓ q hq _).2 (Or.inl h2)⟩
    · exact ⟨_, h1, h2⟩

/-- The row-nonempty flag of the actual summary. -/
theorem ne_bridge (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) (i : ℕ) (hi : i < 8) :
    (stateOf o ℓ (q + 2)).ne.getD i false = newNe o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i := by
  have hbd := lamO_bounds' o ℓ q hq
  have hsy0 := plusStep_snd_nonneg' o (ℓ (q + 1))
  have hA2 : (posO o ℓ (q + 1)).2 = (posO o ℓ q).2 + (plusStepO o (ℓ (q + 1))).2 := by
    rw [posO_new']
    simp only [Prod.snd_add]
  have hL : (stateOf o ℓ (q + 2)).ne.getD i false = decide (((lamO o ℓ (q + 2)).filter
      (fun p => p.2 = (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4))).Nonempty) :=
    stateOf_ne_getD o ℓ (q + 1) i hi
  have hLeft : (∃ x ∈ lamO o ℓ (q + 2), x.2 = (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) ↔
      (∃ x ∈ lamO o ℓ (q + 1), x.2 = (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) ∨
      (∃ c ∈ relCells o (ℓ (q + 1)) (flagO o ℓ (q + 1)), c.2 = (i : ℤ) - 4) := by
    constructor
    · rintro ⟨x, hx, hxy⟩
      rcases (mem_lamO_succ o ℓ q hq x).1 hx with h | h
      · exact Or.inl ⟨x, h, hxy⟩
      · refine Or.inr ⟨x - posO o ℓ (q + 1), h, ?_⟩
        simp only [Prod.snd_sub]
        omega
    · rintro (⟨x, hx, hxy⟩ | ⟨c, hc, hcy⟩)
      · exact ⟨x, (mem_lamO_succ o ℓ q hq x).2 (Or.inl hx), hxy⟩
      · refine ⟨c + posO o ℓ (q + 1), (mem_lamO_succ o ℓ q hq _).2 (Or.inr ?_), ?_⟩
        · rw [add_sub_cancel_right]
          exact hc
        · simp only [Prod.snd_add]
          omega
  rw [hL, Bool.eq_iff_iff]
  unfold newNe
  simp only [enlarge_eq, Bool.or_eq_true, decide_eq_true_eq, Finset.filter_nonempty_iff, List.any_eq_true]
  rw [hLeft]
  cases hr : rowIdx ((i : ℤ) - 4 + (plusStepO o (ℓ (q + 1))).2) with
  | none =>
    have hnone : ¬ ∃ x ∈ lamO o ℓ (q + 1), x.2 = (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4) := by
      rintro ⟨x, hx, hxy⟩
      have h1 := (hbd x hx).1
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

/-- The pair-share flag of the actual summary. -/
theorem sh_bridge (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) (k : ℕ) (hk : k < 7) :
    (stateOf o ℓ (q + 2)).sh.getD k false = newSh o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) k := by
  have hbd := lamO_bounds' o ℓ q hq
  have hsy0 := plusStep_snd_nonneg' o (ℓ (q + 1))
  have hA2 : (posO o ℓ (q + 1)).2 = (posO o ℓ q).2 + (plusStepO o (ℓ (q + 1))).2 := by
    rw [posO_new']
    simp only [Prod.snd_add]
  have hL : (stateOf o ℓ (q + 2)).sh.getD k false = decide ((((lamO o ℓ (q + 2)).image Prod.fst).filter
      (fun x => (x, (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4)) ∈ lamO o ℓ (q + 2) ∧
        (x, (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4) + 1) ∈ lamO o ℓ (q + 2))).Nonempty) :=
    stateOf_sh_getD o ℓ (q + 1) k hk
  have hwin : ∀ j : ℕ, j < 6 → (newBit o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) k j = true ↔
      ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4)) ∈ lamO o ℓ (q + 2)) := by
    intro j hj
    simp only [bits_bridge o ℓ q hq k j (by omega) hj, decide_eq_true_eq, iff_self]
  have hwin' : ∀ j : ℕ, j < 6 → (newBit o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) (k + 1) j = true ↔
      ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4) + 1) ∈ lamO o ℓ (q + 2)) := by
    intro j hj
    have e : ((k + 1 : ℕ) : ℤ) - 4 = (k : ℤ) - 4 + 1 := by push_cast; ring
    simp only [bits_bridge o ℓ q hq (k + 1) j (by omega) hj, e, decide_eq_true_eq, ← add_assoc, iff_self]
  have hWin : (∃ x, x < 6 ∧ newBit o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) k x = true ∧
      newBit o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) (k + 1) x = true) ↔
      (∃ j : ℕ, j < 6 ∧
        ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4)) ∈ lamO o ℓ (q + 2) ∧
        ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4) + 1) ∈ lamO o ℓ (q + 2)) := by
    constructor
    · rintro ⟨x, hx, h1, h2⟩
      exact ⟨x, hx, (hwin x hx).1 h1, (hwin' x hx).1 h2⟩
    · rintro ⟨x, hx, h1, h2⟩
      exact ⟨x, hx, (hwin x hx).2 h1, (hwin' x hx).2 h2⟩
  rw [hL, Bool.eq_iff_iff]
  unfold newSh
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    Finset.filter_nonempty_iff, img_pair_iff]
  rw [pair_succ_iff o ℓ q hq ((k : ℤ) - 4), hWin]
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
