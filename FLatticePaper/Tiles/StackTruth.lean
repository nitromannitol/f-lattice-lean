import FLatticePaper.Tiles.StackBridge2
import FLatticePaper.Tiles.StackGap
import FLatticePaper.Tiles.StackedStringConnected

/-! The truth lemmas for the local union `lamO o ℓ m`: row convexity, row linking and contiguity of the rows,
by induction on the number of letters. Each step uses the Boolean summary through the bridge equalities and the
checks `okS2` (decided on all reachable summaries). -/

namespace FLatticePaper.Tiles

/-! ### The union depends only on the letters it uses -/

theorem posO_congr (o : Orientation) (ℓ ℓ' : ℕ → Letter) (k : ℕ) :
    (∀ j, 1 ≤ j → j ≤ k → ℓ j = ℓ' j) → posO o ℓ k = posO o ℓ' k := by
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    rw [posO_succ o ℓ k, posO_succ o ℓ' k, ih (fun j h1 h2 => h j h1 (by omega)),
      h (k + 1) (by omega) le_rfl]

theorem flagO_congr (o : Orientation) (ℓ ℓ' : ℕ → Letter) (k : ℕ) (h : ∀ j, j ≤ k → ℓ j = ℓ' j) :
    flagO o ℓ k = flagO o ℓ' k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [flagO, h k (by omega), h (k + 1) le_rfl]

theorem lamO_congr (o : Orientation) (ℓ ℓ' : ℕ → Letter) (m : ℕ) (h : ∀ j, j < m → ℓ j = ℓ' j) :
    lamO o ℓ m = lamO o ℓ' m := by
  unfold lamO
  have hA : (Finset.range m).biUnion (fun k => pieceAt (ℓ k) (flagO o ℓ k) (posO o ℓ k)) =
      (Finset.range m).biUnion (fun k => pieceAt (ℓ' k) (flagO o ℓ' k) (posO o ℓ' k)) := by
    apply Finset.biUnion_congr rfl
    intro k hk
    have hk' : k < m := Finset.mem_range.1 hk
    rw [h k hk', flagO_congr o ℓ ℓ' k (fun j hj => h j (by omega)),
      posO_congr o ℓ ℓ' k (fun j _ hj => h j (by omega))]
  have hB : (Finset.Ico 2 m).biUnion (fun k => pieceAt (ℓ k) (flagO o ℓ k) (posO o ℓ k + shadowO o (ℓ k))) =
      (Finset.Ico 2 m).biUnion (fun k => pieceAt (ℓ' k) (flagO o ℓ' k) (posO o ℓ' k + shadowO o (ℓ' k))) := by
    apply Finset.biUnion_congr rfl
    intro k hk
    have hk' : k < m := (Finset.mem_Ico.1 hk).2
    rw [h k hk', flagO_congr o ℓ ℓ' k (fun j hj => h j (by omega)),
      posO_congr o ℓ ℓ' k (fun j _ hj => h j (by omega))]
  have hD : (if 2 ≤ m then pieceAt (ℓ 1) false (posO o ℓ 1 + shadowO o (ℓ 1)) else ∅) =
      (if 2 ≤ m then pieceAt (ℓ' 1) false (posO o ℓ' 1 + shadowO o (ℓ' 1)) else ∅) := by
    by_cases hm : 2 ≤ m
    · rw [if_pos hm, if_pos hm, h 1 (by omega), posO_congr o ℓ ℓ' 1 (fun j _ hj => h j (by omega))]
    · rw [if_neg hm, if_neg hm]
  rw [hA, hB, hD]

theorem stateOf_congr (o : Orientation) (ℓ ℓ' : ℕ → Letter) (m : ℕ) (hm : 2 ≤ m)
    (h : ∀ j, j < m → ℓ j = ℓ' j) : stateOf o ℓ m = stateOf o ℓ' m := by
  unfold stateOf
  rw [lamO_congr o ℓ ℓ' m h, posO_congr o ℓ ℓ' (m - 1) (fun j _ hj => h j (by omega)),
    h (m - 1) (by omega), h 1 (by omega)]

/-! ### The base case and the reachable summaries, for both orientations -/

theorem reach_base_all (o : Orientation) :
    ∀ a ∈ [Letter.p, Letter.q], ∀ b ∈ [Letter.p, Letter.q], stateOf o (ell2 a b) 2 ∈ reachList o := by
  cases o
  · exact reach_base_h
  · exact reach_base_v

theorem okS2_all (o : Orientation) : ∀ s ∈ reachList o, ∀ a ∈ [Letter.p, Letter.q], okS2 o s a = true := by
  cases o
  · exact okS2_h
  · exact okS2_v

theorem reach_trans_all (o : Orientation) :
    ∀ s ∈ reachList o, ∀ a ∈ [Letter.p, Letter.q], transWS o s a ∈ reachList o := by
  cases o
  · exact fun s hs a ha => (reach_closed_h s hs a ha).2
  · exact fun s hs a ha => (reach_closed_v s hs a ha).2

/-! ### Rows -/

/-- The row `y` meets `S`. -/
def RowSet (S : Finset Site) (y : ℤ) : Prop := ∃ p ∈ S, p.2 = y

instance (S : Finset Site) (y : ℤ) : Decidable (RowSet S y) := by
  unfold RowSet
  infer_instance

/-- The rows of `S` form an interval, containing the rows `B.2` and `B.2 + 1`. -/
def RowsInterval (S : Finset Site) (B : Site) : Prop :=
  RowSet S B.2 ∧ RowSet S (B.2 + 1) ∧
    ∀ a ∈ S, ∀ b ∈ S, a.2 ≤ b.2 → ∀ y ∈ Finset.Icc a.2 b.2, RowSet S y

instance (S : Finset Site) (B : Site) : Decidable (RowsInterval S B) := by
  unfold RowsInterval
  infer_instance

/-- The invariant of the induction, for the union of `q + 1` letters with anchor `posO q`. -/
structure GoodAt (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) : Prop where
  reach : stateOf o ℓ (q + 1) ∈ reachList o
  conv : RowConvex (lamO o ℓ (q + 1))
  link : RowsLinked (lamO o ℓ (q + 1))
  ivl : RowsInterval (lamO o ℓ (q + 1)) (posO o ℓ q)

theorem good_base_decide (o : Orientation) :
    ∀ a ∈ [Letter.p, Letter.q], ∀ b ∈ [Letter.p, Letter.q],
      RowConvex (lamO o (ell2 a b) 2) ∧ RowsLinked (lamO o (ell2 a b) 2) ∧
        RowsInterval (lamO o (ell2 a b) 2) (posO o (ell2 a b) 1) := by
  cases o <;> decide +kernel

theorem good_base (o : Orientation) (ℓ : ℕ → Letter) : GoodAt o ℓ 1 := by
  have hc : ∀ j, j < 2 → ℓ j = ell2 (ℓ 0) (ℓ 1) j := by
    intro j hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> simp [ell2]
  have hmem0 : ℓ 0 ∈ [Letter.p, Letter.q] := by cases ℓ 0 <;> simp
  have hmem1 : ℓ 1 ∈ [Letter.p, Letter.q] := by cases ℓ 1 <;> simp
  have hd := good_base_decide o (ℓ 0) hmem0 (ℓ 1) hmem1
  have hL : lamO o ℓ 2 = lamO o (ell2 (ℓ 0) (ℓ 1)) 2 := lamO_congr o ℓ _ 2 hc
  have hP : posO o ℓ 1 = posO o (ell2 (ℓ 0) (ℓ 1)) 1 :=
    posO_congr o ℓ _ 1 (fun j _ hj => hc j (by omega))
  refine ⟨?_, ?_, ?_, ?_⟩
  · show stateOf o ℓ 2 ∈ reachList o
    rw [stateOf_congr o ℓ _ 2 le_rfl hc]
    exact reach_base_all o (ℓ 0) hmem0 (ℓ 1) hmem1
  · show RowConvex (lamO o ℓ 2)
    rw [hL]
    exact hd.1
  · show RowsLinked (lamO o ℓ 2)
    rw [hL]
    exact hd.2.1
  · show RowsInterval (lamO o ℓ 2) (posO o ℓ 1)
    rw [hP, hL]
    exact hd.2.2

/-! ### The new rows, and the old cells inside the new window -/

/-- A cell of the new union that is not old lies in the new window. -/
theorem new_bounds (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) (p : Site)
    (hp : p ∈ lamO o ℓ (q + 2)) (hn : p ∉ lamO o ℓ (q + 1)) :
    (posO o ℓ (q + 1)).1 - 2 ≤ p.1 ∧ p.1 ≤ (posO o ℓ (q + 1)).1 + 3 ∧
      (posO o ℓ (q + 1)).2 - 3 ≤ p.2 ∧ p.2 ≤ (posO o ℓ (q + 1)).2 + 3 := by
  rcases (mem_lamO_succ o ℓ q hq p).1 hp with h | h
  · exact absurd h hn
  · have hb := rel_bounds o (ℓ (q + 1)) (flagO o ℓ (q + 1)) _ h
    simp only [Prod.fst_sub, Prod.snd_sub] at hb
    omega

theorem gapFree_spec {l : List Bool} (h : gapFree l = true) {j1 j2 j3 : ℕ} (h12 : j1 < j2) (h23 : j2 < j3)
    (h3 : j3 < 6) (b1 : l.getD j1 false = true) (b3 : l.getD j3 false = true) :
    l.getD j2 false = true := by
  unfold gapFree at h
  have e1 := (List.all_eq_true.1 h) j1 (List.mem_range.2 (by omega))
  have e2 := (List.all_eq_true.1 e1) j2 (List.mem_range.2 (by omega))
  have e3 := (List.all_eq_true.1 e2) j3 (List.mem_range.2 h3)
  cases hb : l.getD j2 false
  · rw [decide_eq_true h12, decide_eq_true h23, b1, b3, hb] at e3
    exact absurd e3 (by decide)
  · rfl

/-- A cell of the old union at a new-window position is an old window bit. -/
theorem oldBitAt_spec (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (i j : ℕ)
    (h : oldBitAt o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i j = true) :
    ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) ∈ lamO o ℓ (q + 1) := by
  simp only [oldBitAt] at h
  cases hr : rowIdx ((i : ℤ) - 4 + (plusStepO o (ℓ (q + 1))).2) with
  | none =>
    rw [hr] at h
    simp at h
  | some k =>
    cases hc : colIdx ((j : ℤ) - 2 + (plusStepO o (ℓ (q + 1))).1) with
    | none =>
      rw [hr, hc] at h
      simp at h
    | some l =>
      rw [hr, hc] at h
      have hr' := rowIdx_some hr
      have hc' := colIdx_some hc
      have hk8 : k < 8 := by omega
      have hl6 : l < 6 := by omega
      dsimp only at h
      rw [stateOf_bits_getD o ℓ q k l hk8 hl6] at h
      have hpt : ((posO o ℓ q).1 + ((l : ℤ) - 2), (posO o ℓ q).2 + ((k : ℤ) - 4)) =
          ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) := by
        rw [posO_new']
        refine Prod.ext ?_ ?_
        · dsimp only
          simp only [Prod.fst_add]
          omega
        · dsimp only
          simp only [Prod.snd_add]
          omega
      rw [← hpt]
      exact of_decide_eq_true h

/-- A nonempty old row which receives a new cell has an old cell in the new window (the gap check). -/
theorem gapOk_common (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) (i : ℕ) (hi : i < 8)
    (hgap : gapOk o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i = true)
    (p : Site) (hp : p ∈ lamO o ℓ (q + 1)) (hpy : p.2 = (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4))
    (c : Site) (hc : c ∈ relCells o (ℓ (q + 1)) (flagO o ℓ (q + 1))) (hcy : c.2 = (i : ℤ) - 4) :
    ∃ j : ℕ, j < 6 ∧ oldBitAt o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i j = true := by
  have hbd := lamO_bounds' o ℓ q hq
  have hsy0 := plusStep_snd_nonneg' o (ℓ (q + 1))
  have hA2 : (posO o ℓ (q + 1)).2 = (posO o ℓ q).2 + (plusStepO o (ℓ (q + 1))).2 := by
    rw [posO_new']
    simp only [Prod.snd_add]
  have hr : rowIdx ((i : ℤ) - 4 + (plusStepO o (ℓ (q + 1))).2) ≠ none := by
    intro hnone
    have h1 := rowIdx_none hnone
    have h2 := (hbd p hp).1
    omega
  obtain ⟨k, hk⟩ : ∃ k, rowIdx ((i : ℤ) - 4 + (plusStepO o (ℓ (q + 1))).2) = some k := by
    cases h : rowIdx ((i : ℤ) - 4 + (plusStepO o (ℓ (q + 1))).2) with
    | none => exact absurd h hr
    | some k => exact ⟨k, rfl⟩
  have hkr := rowIdx_some hk
  have hk8 : k < 8 := by omega
  have hne : (stateOf o ℓ (q + 1)).ne.getD k false = true := by
    rw [stateOf_ne_getD o ℓ q k hk8]
    exact decide_eq_true ⟨p, Finset.mem_filter.2 ⟨hp, by omega⟩⟩
  have hnN : (relCells o (ℓ (q + 1)) (flagO o ℓ (q + 1))).any (fun c => decide (c.2 = (i : ℤ) - 4)) = true :=
    List.any_eq_true.2 ⟨c, hc, decide_eq_true hcy⟩
  have hrow : oldRowIn o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i = true := by
    unfold gapOk at hgap
    simp only [enlarge_eq, hk, hne, hnN, Bool.and_self, Bool.not_true, Bool.false_or] at hgap
    exact hgap
  obtain ⟨j, hjm, hb⟩ := List.any_eq_true.1 hrow
  exact ⟨j, List.mem_range.1 hjm, hb⟩

/-- Row convexity inside the new window, from the gap-free window bits. -/
theorem window_conv (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) (i : ℕ) (hi : i < 8)
    (hfree : gapFree (newRowBits o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i) = true)
    (u v : Site) (hu : u ∈ lamO o ℓ (q + 2)) (hv : v ∈ lamO o ℓ (q + 2))
    (hu2 : u.2 = (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) (hv2 : v.2 = (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4))
    (hu1 : (posO o ℓ (q + 1)).1 - 2 ≤ u.1 ∧ u.1 ≤ (posO o ℓ (q + 1)).1 + 3)
    (hv1 : (posO o ℓ (q + 1)).1 - 2 ≤ v.1 ∧ v.1 ≤ (posO o ℓ (q + 1)).1 + 3)
    (x : ℤ) (hx1 : u.1 ≤ x) (hx2 : x ≤ v.1) :
    (x, (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) ∈ lamO o ℓ (q + 2) := by
  have hcol : ∀ z : ℤ, (posO o ℓ (q + 1)).1 - 2 ≤ z → z ≤ (posO o ℓ (q + 1)).1 + 3 →
      ∃ j : ℕ, j < 6 ∧ (posO o ℓ (q + 1)).1 + ((j : ℤ) - 2) = z := by
    intro z h1 h2
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = z - (posO o ℓ (q + 1)).1 + 2 :=
      ⟨(z - (posO o ℓ (q + 1)).1 + 2).toNat, Int.toNat_of_nonneg (by omega)⟩
    exact ⟨j, by omega, by omega⟩
  have hbit : ∀ j : ℕ, j < 6 → (newBit o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i j = true ↔
      ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) ∈ lamO o ℓ (q + 2)) := by
    intro j hj
    simp only [bits_bridge o ℓ q hq i j hi hj, decide_eq_true_eq]
  have hbitN : ∀ j : ℕ, j < 6 →
      ((newRowBits o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i).getD j false = true ↔
        newBit o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i j = true) := by
    intro j hj
    unfold newRowBits
    rw [getD_map_range _ 6 j false hj]
  obtain ⟨j1, hj1, e1⟩ := hcol u.1 hu1.1 hu1.2
  obtain ⟨j3, hj3, e3⟩ := hcol v.1 hv1.1 hv1.2
  obtain ⟨j2, hj2, e2⟩ := hcol x (by omega) (by omega)
  have hpu : ((posO o ℓ (q + 1)).1 + ((j1 : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) = u :=
    Prod.ext e1 hu2.symm
  have hpv : ((posO o ℓ (q + 1)).1 + ((j3 : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) = v :=
    Prod.ext e3 hv2.symm
  have hb1 : (newRowBits o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i).getD j1 false = true :=
    (hbitN j1 hj1).2 ((hbit j1 hj1).2 (by rw [hpu]; exact hu))
  have hb3 : (newRowBits o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i).getD j3 false = true :=
    (hbitN j3 hj3).2 ((hbit j3 hj3).2 (by rw [hpv]; exact hv))
  have hbx : (newRowBits o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i).getD j2 false = true := by
    rcases Nat.eq_or_lt_of_le (show j1 ≤ j2 by omega) with h | h
    · rw [← h]
      exact hb1
    rcases Nat.eq_or_lt_of_le (show j2 ≤ j3 by omega) with h' | h'
    · rw [h']
      exact hb3
    exact gapFree_spec hfree h h' hj3 hb1 hb3
  have hfin := (hbit j2 hj2).1 ((hbitN j2 hj2).1 hbx)
  rw [e2] at hfin
  exact hfin

/-- Row convexity of the new union, from the row convexity of the old one and the checks of the step. -/
theorem rowConvex_step (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q)
    (hS : RowConvex (lamO o ℓ (q + 1)))
    (hok : okS2 o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) = true) :
    RowConvex (lamO o ℓ (q + 2)) := by
  have hrows : ∀ i : ℕ, i < 8 → gapFree (newRowBits o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i) = true ∧
      gapOk o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i = true := by
    intro i hi
    have hall := List.all_eq_true.1 ((Bool.and_eq_true _ _).mp hok).1 i (List.mem_range.2 hi)
    unfold rowOk2 at hall
    have h2 := (Bool.and_eq_true _ _).mp hall
    exact ⟨h2.2, h2.1⟩
  have mono : ∀ p, p ∈ lamO o ℓ (q + 1) → p ∈ lamO o ℓ (q + 2) :=
    fun p hp => (mem_lamO_succ o ℓ q hq p).2 (Or.inl hp)
  intro a ha b hb hab x hx
  obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.1 hx
  by_cases hAB : a ∈ lamO o ℓ (q + 1) ∧ b ∈ lamO o ℓ (q + 1)
  · exact mono _ (hS a hAB.1 b hAB.2 hab x hx)
  -- some point is new: its row lies in the new window
  have hwinrow : (posO o ℓ (q + 1)).2 - 3 ≤ a.2 ∧ a.2 ≤ (posO o ℓ (q + 1)).2 + 3 := by
    by_cases haS : a ∈ lamO o ℓ (q + 1)
    · have hbn : b ∉ lamO o ℓ (q + 1) := fun h => hAB ⟨haS, h⟩
      have := new_bounds o ℓ q hq b hb hbn
      omega
    · have := new_bounds o ℓ q hq a ha haS
      omega
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = a.2 - (posO o ℓ (q + 1)).2 + 4 :=
    ⟨(a.2 - (posO o ℓ (q + 1)).2 + 4).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hi8 : i < 8 := by omega
  have hiy : a.2 = (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4) := by omega
  have hiyb : b.2 = (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4) := hab.symm.trans hiy
  obtain ⟨hgf, hgo⟩ := hrows i hi8
  -- a relative cell of the new tile in this row
  have hc : ∃ c ∈ relCells o (ℓ (q + 1)) (flagO o ℓ (q + 1)), c.2 = (i : ℤ) - 4 := by
    by_cases haS : a ∈ lamO o ℓ (q + 1)
    · have hbn : b ∉ lamO o ℓ (q + 1) := fun h => hAB ⟨haS, h⟩
      rcases (mem_lamO_succ o ℓ q hq b).1 hb with h | h
      · exact absurd h hbn
      · refine ⟨b - posO o ℓ (q + 1), h, ?_⟩
        simp only [Prod.snd_sub]
        omega
    · rcases (mem_lamO_succ o ℓ q hq a).1 ha with h | h
      · exact absurd h haS
      · refine ⟨a - posO o ℓ (q + 1), h, ?_⟩
        simp only [Prod.snd_sub]
        omega
  obtain ⟨c, hcm, hcy⟩ := hc
  by_cases hO : ∃ p ∈ lamO o ℓ (q + 1), p.2 = a.2
  · obtain ⟨p0, hp0, hp0y⟩ := hO
    obtain ⟨j, hj, hbj⟩ := gapOk_common o ℓ q hq i hi8 hgo p0 hp0 (by rw [hp0y]; exact hiy) c hcm hcy
    have hcS : ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) ∈
        lamO o ℓ (q + 1) := oldBitAt_spec o ℓ q i j hbj
    have hcS' := mono _ hcS
    have hcw : (posO o ℓ (q + 1)).1 - 2 ≤ (posO o ℓ (q + 1)).1 + ((j : ℤ) - 2) ∧
        (posO o ℓ (q + 1)).1 + ((j : ℤ) - 2) ≤ (posO o ℓ (q + 1)).1 + 3 := by
      omega
    by_cases haS : a ∈ lamO o ℓ (q + 1)
    · have hbn : b ∉ lamO o ℓ (q + 1) := fun h => hAB ⟨haS, h⟩
      have hbw := new_bounds o ℓ q hq b hb hbn
      by_cases hxc : x ≤ (posO o ℓ (q + 1)).1 + ((j : ℤ) - 2)
      · have hm := hS a haS _ hcS hiy x (Finset.mem_Icc.2 ⟨hx1, hxc⟩)
        exact mono _ hm
      · rw [hiy]
        exact window_conv o ℓ q hq i hi8 hgf _ b hcS' hb rfl hiyb hcw ⟨hbw.1, hbw.2.1⟩ x
          (not_le.mp hxc).le hx2
    · by_cases hbS : b ∈ lamO o ℓ (q + 1)
      · have haw := new_bounds o ℓ q hq a ha haS
        by_cases hxc : (posO o ℓ (q + 1)).1 + ((j : ℤ) - 2) ≤ x
        · have hm := hS _ hcS b hbS (hiy.symm.trans hab) x (Finset.mem_Icc.2 ⟨hxc, hx2⟩)
          have hm' : (x, a.2) ∈ lamO o ℓ (q + 1) := by
            rw [hiy]
            exact hm
          exact mono _ hm'
        · rw [hiy]
          exact window_conv o ℓ q hq i hi8 hgf a _ ha hcS' hiy rfl ⟨haw.1, haw.2.1⟩ hcw x hx1
            (not_le.mp hxc).le
      · -- both cells are new
        have haw := new_bounds o ℓ q hq a ha haS
        have hbw := new_bounds o ℓ q hq b hb hbS
        rw [hiy]
        exact window_conv o ℓ q hq i hi8 hgf a b ha hb hiy hiyb ⟨haw.1, haw.2.1⟩ ⟨hbw.1, hbw.2.1⟩ x hx1 hx2
  · -- no old cell in this row: both cells are new
    have haS : a ∉ lamO o ℓ (q + 1) := fun h => hO ⟨a, h, rfl⟩
    have hbS : b ∉ lamO o ℓ (q + 1) := fun h => hO ⟨b, h, hab.symm⟩
    have haw := new_bounds o ℓ q hq a ha haS
    have hbw := new_bounds o ℓ q hq b hb hbS
    rw [hiy]
    exact window_conv o ℓ q hq i hi8 hgf a b ha hb hiy hiyb ⟨haw.1, haw.2.1⟩ ⟨hbw.1, hbw.2.1⟩ x hx1 hx2

/-! ### Rows of the new tile, and the contiguity and linking steps -/

theorem plusStep_snd_le2 (o : Orientation) (l : Letter) : (plusStepO o l).2 ≤ 2 := by
  cases o <;> cases l <;> decide

theorem zero_mem_rel (o : Orientation) (a : Letter) (ep : Bool) : ((0 : ℤ), (0 : ℤ)) ∈ relCells o a ep := by
  cases o <;> cases a <;> cases ep <;> decide

theorem one_mem_rel (o : Orientation) (a : Letter) (ep : Bool) : ((0 : ℤ), (1 : ℤ)) ∈ relCells o a ep := by
  cases o <;> cases a <;> cases ep <;> decide

theorem relRows_lower (o : Orientation) (a : Letter) (ep : Bool) :
    ∀ d ∈ relCells o a ep, d.2 ≤ 0 → ∀ z ∈ Finset.Icc d.2 0, ∃ e ∈ relCells o a ep, e.2 = z := by
  cases o <;> cases a <;> cases ep <;> decide

theorem relRows_upper (o : Orientation) (a : Letter) (ep : Bool) :
    ∀ d ∈ relCells o a ep, 0 ≤ d.2 → ∀ z ∈ Finset.Icc 0 d.2, ∃ e ∈ relCells o a ep, e.2 = z := by
  cases o <;> cases a <;> cases ep <;> decide

/-- A new cell's row is listed in the summary: the row of the new union is nonempty at index `j`. -/
theorem newNe_of_rowSet (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) (j : ℕ) (hj : j < 8)
    (z : ℤ) (hz : RowSet (lamO o ℓ (q + 2)) z) (hzj : z = (posO o ℓ (q + 1)).2 + ((j : ℤ) - 4)) :
    newNe o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) j = true := by
  obtain ⟨p, hp, hpz⟩ := hz
  rw [← ne_bridge o ℓ q hq j hj]
  exact (stateOf_ne_getD o ℓ (q + 1) j hj).trans (decide_eq_true ⟨p, Finset.mem_filter.2 ⟨hp, by omega⟩⟩)

theorem rowsInterval_step (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q)
    (hI : RowsInterval (lamO o ℓ (q + 1)) (posO o ℓ q)) :
    RowsInterval (lamO o ℓ (q + 2)) (posO o ℓ (q + 1)) := by
  obtain ⟨⟨p1, hp1, hp1y⟩, ⟨p2, hp2, hp2y⟩, hconv⟩ := hI
  have hsy0 := plusStep_snd_nonneg' o (ℓ (q + 1))
  have hsy2 := plusStep_snd_le2 o (ℓ (q + 1))
  have hA2 : (posO o ℓ (q + 1)).2 = (posO o ℓ q).2 + (plusStepO o (ℓ (q + 1))).2 := by
    rw [posO_new']
    simp only [Prod.snd_add]
  have hmono : ∀ p ∈ lamO o ℓ (q + 1), p ∈ lamO o ℓ (q + 2) :=
    fun p hp => (mem_lamO_succ o ℓ q hq p).2 (Or.inl hp)
  have hz0 : posO o ℓ (q + 1) - posO o ℓ (q + 1) = ((0 : ℤ), (0 : ℤ)) :=
    Prod.ext (sub_self _) (sub_self _)
  have hA0 : posO o ℓ (q + 1) ∈ lamO o ℓ (q + 2) :=
    (mem_lamO_succ o ℓ q hq _).2 (Or.inr (by rw [hz0]; exact zero_mem_rel _ _ _))
  have hA1 : posO o ℓ (q + 1) + ((0 : ℤ), (1 : ℤ)) ∈ lamO o ℓ (q + 2) :=
    (mem_lamO_succ o ℓ q hq _).2 (Or.inr (by rw [add_sub_cancel_left]; exact one_mem_rel _ _ _))
  refine ⟨⟨posO o ℓ (q + 1), hA0, rfl⟩, ⟨posO o ℓ (q + 1) + ((0 : ℤ), (1 : ℤ)), hA1, rfl⟩, ?_⟩
  intro a ha b hb hab y hy
  obtain ⟨hy1, hy2⟩ := Finset.mem_Icc.1 hy
  by_cases hyB : y ≤ (posO o ℓ q).2 + 1 ∧ (posO o ℓ q).2 ≤ y
  · rcases (show y = (posO o ℓ q).2 ∨ y = (posO o ℓ q).2 + 1 by omega) with h | h
    · exact ⟨p1, hmono p1 hp1, by rw [hp1y]; exact h.symm⟩
    · exact ⟨p2, hmono p2 hp2, by rw [hp2y]; exact h.symm⟩
  by_cases hlow : y < (posO o ℓ q).2
  · by_cases haS : a ∈ lamO o ℓ (q + 1)
    · obtain ⟨p, hp, hpy⟩ := hconv a haS p1 hp1 (by omega) y (Finset.mem_Icc.2 ⟨hy1, by omega⟩)
      exact ⟨p, hmono p hp, hpy⟩
    · have haw := new_bounds o ℓ q hq a ha haS
      have hd := ((mem_lamO_succ o ℓ q hq a).1 ha).resolve_left haS
      have hdy : (a - posO o ℓ (q + 1)).2 = a.2 - (posO o ℓ (q + 1)).2 := Prod.snd_sub _ _
      obtain ⟨e, he, hey⟩ := relRows_lower o (ℓ (q + 1)) (flagO o ℓ (q + 1)) _ hd (by omega)
        (y - (posO o ℓ (q + 1)).2) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      refine ⟨posO o ℓ (q + 1) + e, (mem_lamO_succ o ℓ q hq _).2 (Or.inr ?_), ?_⟩
      · rw [add_sub_cancel_left]
        exact he
      · show (posO o ℓ (q + 1)).2 + e.2 = y
        rw [hey]
        omega
  · have hup : (posO o ℓ q).2 + 2 ≤ y ∨ (posO o ℓ q).2 + 1 < y := by omega
    by_cases hbS : b ∈ lamO o ℓ (q + 1)
    · obtain ⟨p, hp, hpy⟩ := hconv p2 hp2 b hbS (by omega) y (Finset.mem_Icc.2 ⟨by omega, hy2⟩)
      exact ⟨p, hmono p hp, hpy⟩
    · have hbw := new_bounds o ℓ q hq b hb hbS
      have hd := ((mem_lamO_succ o ℓ q hq b).1 hb).resolve_left hbS
      have hdy : (b - posO o ℓ (q + 1)).2 = b.2 - (posO o ℓ (q + 1)).2 := Prod.snd_sub _ _
      obtain ⟨e, he, hey⟩ := relRows_upper o (ℓ (q + 1)) (flagO o ℓ (q + 1)) _ hd (by omega)
        (y - (posO o ℓ (q + 1)).2) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      refine ⟨posO o ℓ (q + 1) + e, (mem_lamO_succ o ℓ q hq _).2 (Or.inr ?_), ?_⟩
      · rw [add_sub_cancel_left]
        exact he
      · show (posO o ℓ (q + 1)).2 + e.2 = y
        rw [hey]
        omega

theorem rowsLinked_step (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q)
    (hL : RowsLinked (lamO o ℓ (q + 1)))
    (hI0 : RowsInterval (lamO o ℓ (q + 1)) (posO o ℓ q))
    (hI : RowsInterval (lamO o ℓ (q + 2)) (posO o ℓ (q + 1)))
    (hok : okS2 o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) = true) :
    RowsLinked (lamO o ℓ (q + 2)) := by
  obtain ⟨⟨p1, hp1, hp1y⟩, _, _⟩ := hI0
  have hsy0 := plusStep_snd_nonneg' o (ℓ (q + 1))
  have hsy2 := plusStep_snd_le2 o (ℓ (q + 1))
  have hA2 : (posO o ℓ (q + 1)).2 = (posO o ℓ q).2 + (plusStepO o (ℓ (q + 1))).2 := by
    rw [posO_new']
    simp only [Prod.snd_add]
  have hmono : ∀ p ∈ lamO o ℓ (q + 1), p ∈ lamO o ℓ (q + 2) :=
    fun p hp => (mem_lamO_succ o ℓ q hq p).2 (Or.inl hp)
  have hbd2 := lamO_bounds' o ℓ (q + 1) (by omega)
  intro a ha b hb hab y hy
  obtain ⟨hy1, hy2⟩ := Finset.mem_Ico.1 hy
  have hyS : RowSet (lamO o ℓ (q + 2)) y :=
    hI.2.2 a ha b hb hab y (Finset.mem_Icc.2 ⟨hy1, by omega⟩)
  have hyS1 : RowSet (lamO o ℓ (q + 2)) (y + 1) :=
    hI.2.2 a ha b hb hab (y + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have hb2 := (hbd2 b hb).1
  by_cases hwin : (posO o ℓ (q + 1)).2 - 4 ≤ y
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = y - (posO o ℓ (q + 1)).2 + 4 :=
      ⟨(y - (posO o ℓ (q + 1)).2 + 4).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hk7 : k < 7 := by omega
    have hk8 : k < 8 := by omega
    have hk1 : k + 1 < 8 := by omega
    have hpair := List.all_eq_true.1 ((Bool.and_eq_true _ _).mp hok).2 k (List.mem_range.2 hk7)
    unfold pairOk at hpair
    have hnk : newNe o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) k = true :=
      newNe_of_rowSet o ℓ q hq k hk8 y hyS (by omega)
    have hnk1 : newNe o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) (k + 1) = true :=
      newNe_of_rowSet o ℓ q hq (k + 1) hk1 (y + 1) hyS1 (by push_cast; omega)
    simp only [hnk, hnk1, Bool.and_self, Bool.not_true, Bool.false_or] at hpair
    have hshT : (stateOf o ℓ (q + 2)).sh.getD k false = true :=
      (sh_bridge o ℓ q hq k hk7).trans hpair
    have hshD := (stateOf_sh_getD o ℓ (q + 1) k hk7).symm.trans hshT
    obtain ⟨x, hx⟩ := of_decide_eq_true hshD
    obtain ⟨_, hx1, hx2⟩ := Finset.mem_filter.1 hx
    have hyk : (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4) = y := by omega
    rw [hyk] at hx1 hx2
    exact ⟨x, Finset.mem_image.2 ⟨(x, y), hx1, rfl⟩, hx1, hx2⟩
  · have haS : a ∈ lamO o ℓ (q + 1) := by
      by_contra haS
      have haw := new_bounds o ℓ q hq a ha haS
      omega
    obtain ⟨x, hxI, h1, h2⟩ := hL a haS p1 hp1 (by omega) y (Finset.mem_Ico.2 ⟨hy1, by omega⟩)
    obtain ⟨c, hc, hcx⟩ := Finset.mem_image.1 hxI
    exact ⟨x, Finset.mem_image.2 ⟨c, hmono c hc, hcx⟩, hmono _ h1, hmono _ h2⟩

/-- The invariant of the induction, for every number of letters at least two. -/
theorem goodAt_all (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) : GoodAt o ℓ q := by
  induction q, hq using Nat.le_induction with
  | base => exact good_base o ℓ
  | succ q hq ih =>
    have hres : stateOf o ℓ (q + 1) ∈ reachList o := ih.reach
    have hanyl : ℓ (q + 1) ∈ [Letter.p, Letter.q] := by cases ℓ (q + 1) <;> simp
    have hok := okS2_all o _ hres _ hanyl
    have hI' := rowsInterval_step o ℓ q hq ih.ivl
    refine ⟨?_, ?_, ?_, hI'⟩
    · show stateOf o ℓ (q + 2) ∈ reachList o
      rw [stateOf_succ o ℓ q hq]
      exact reach_trans_all o _ hres _ hanyl
    · exact rowConvex_step o ℓ q hq ih.conv hok
    · exact rowsLinked_step o ℓ q hq ih.link ih.ivl hI' hok

theorem lamO_convex_linked (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) :
    RowConvex (lamO o ℓ (q + 1)) ∧ RowsLinked (lamO o ℓ (q + 1)) :=
  ⟨(goodAt_all o ℓ q hq).conv, (goodAt_all o ℓ q hq).link⟩

end FLatticePaper.Tiles
