import FLatticePaper.Tiles.StackFinalBridge
import FLatticePaper.Tiles.StackTruth

/-! Truth of the final union `F` (membership `x ∈ F ↔ x ∈ lamO o ℓ (q+1) ∨ x - A ∈ finRel`), from the truth of
`lamO o ℓ (q+1)` and the decided window checks `rowOkF`, `pairOkF`. -/

namespace FLatticePaper.Tiles

theorem new_boundsF (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (F : Finset Site)
    (hF : ∀ x, x ∈ F ↔ x ∈ lamO o ℓ (q + 1) ∨ x - posO o ℓ (q + 1) ∈ finRel o (stateOf o ℓ (q + 1)).secondL)
    (p : Site) (hp : p ∈ F) (hn : p ∉ lamO o ℓ (q + 1)) :
    (posO o ℓ (q + 1)).1 - 2 ≤ p.1 ∧ p.1 ≤ (posO o ℓ (q + 1)).1 + 3 ∧
      (posO o ℓ (q + 1)).2 - 3 ≤ p.2 ∧ p.2 ≤ (posO o ℓ (q + 1)).2 + 3 := by
  rcases (hF p).1 hp with h | h
  · exact absurd h hn
  · have hb := finRel_bounds o _ _ h
    simp only [Prod.fst_sub, Prod.snd_sub] at hb
    omega

theorem F_top (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) (F : Finset Site)
    (hF : ∀ x, x ∈ F ↔ x ∈ lamO o ℓ (q + 1) ∨ x - posO o ℓ (q + 1) ∈ finRel o (stateOf o ℓ (q + 1)).secondL)
    (p : Site) (hp : p ∈ F) : p.2 ≤ (posO o ℓ (q + 1)).2 + 3 := by
  have hsy0 := plusStep_snd_nonneg' o (ℓ (q + 1))
  have hA2 : (posO o ℓ (q + 1)).2 = (posO o ℓ q).2 + (plusStepO o (ℓ (q + 1))).2 := by
    rw [posO_new']
    simp only [Prod.snd_add]
  rcases (hF p).1 hp with h | h
  · have := (lamO_bounds' o ℓ q hq p h).1
    omega
  · have hb := finRel_bounds o _ _ h
    simp only [Prod.snd_sub] at hb
    omega

/-- A new cell of the final union: its position in the window is the old anchor's window. -/
theorem gapOkF_common (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q)
    (i : ℕ) (hi : i < 8)
    (hgap : gapOkF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i = true)
    (p : Site) (hp : p ∈ lamO o ℓ (q + 1)) (hpy : p.2 = (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4))
    (c : Site) (hc : c ∈ finRel o (stateOf o ℓ (q + 1)).secondL) (hcy : c.2 = (i : ℤ) - 4) :
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
  have hnN : (finRel o (stateOf o ℓ (q + 1)).secondL).any (fun c => decide (c.2 = (i : ℤ) - 4)) = true :=
    List.any_eq_true.2 ⟨c, hc, decide_eq_true hcy⟩
  have hrow : oldRowIn o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i = true := by
    unfold gapOkF at hgap
    simp only [hk, hne, hnN, Bool.and_self, Bool.not_true, Bool.false_or] at hgap
    exact hgap
  obtain ⟨j, hjm, hb⟩ := List.any_eq_true.1 hrow
  exact ⟨j, List.mem_range.1 hjm, hb⟩

theorem window_convF (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) (F : Finset Site)
    (hF : ∀ x, x ∈ F ↔ x ∈ lamO o ℓ (q + 1) ∨ x - posO o ℓ (q + 1) ∈ finRel o (stateOf o ℓ (q + 1)).secondL)
    (i : ℕ) (hi : i < 8)
    (hfree : gapFree (newRowBitsF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i) = true)
    (u v : Site) (hu : u ∈ F) (hv : v ∈ F)
    (hu2 : u.2 = (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) (hv2 : v.2 = (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4))
    (hu1 : (posO o ℓ (q + 1)).1 - 2 ≤ u.1 ∧ u.1 ≤ (posO o ℓ (q + 1)).1 + 3)
    (hv1 : (posO o ℓ (q + 1)).1 - 2 ≤ v.1 ∧ v.1 ≤ (posO o ℓ (q + 1)).1 + 3)
    (x : ℤ) (hx1 : u.1 ≤ x) (hx2 : x ≤ v.1) :
    (x, (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) ∈ F := by
  have hcol : ∀ z : ℤ, (posO o ℓ (q + 1)).1 - 2 ≤ z → z ≤ (posO o ℓ (q + 1)).1 + 3 →
      ∃ j : ℕ, j < 6 ∧ (posO o ℓ (q + 1)).1 + ((j : ℤ) - 2) = z := by
    intro z h1 h2
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = z - (posO o ℓ (q + 1)).1 + 2 :=
      ⟨(z - (posO o ℓ (q + 1)).1 + 2).toNat, Int.toNat_of_nonneg (by omega)⟩
    exact ⟨j, by omega, by omega⟩
  have hbit : ∀ j : ℕ, j < 6 → (newBitF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i j = true ↔
      ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) ∈ F) := by
    intro j hj
    simp only [bits_bridgeF o ℓ q hq F hF i j hi hj, decide_eq_true_eq]
  have hbitN : ∀ j : ℕ, j < 6 →
      ((newRowBitsF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i).getD j false = true ↔
        newBitF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i j = true) := by
    intro j hj
    unfold newRowBitsF
    rw [getD_map_range _ 6 j false hj]
  obtain ⟨j1, hj1, e1⟩ := hcol u.1 hu1.1 hu1.2
  obtain ⟨j3, hj3, e3⟩ := hcol v.1 hv1.1 hv1.2
  obtain ⟨j2, hj2, e2⟩ := hcol x (by omega) (by omega)
  have hpu : ((posO o ℓ (q + 1)).1 + ((j1 : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) = u :=
    Prod.ext e1 hu2.symm
  have hpv : ((posO o ℓ (q + 1)).1 + ((j3 : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) = v :=
    Prod.ext e3 hv2.symm
  have hb1 : (newRowBitsF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i).getD j1 false = true :=
    (hbitN j1 hj1).2 ((hbit j1 hj1).2 (by rw [hpu]; exact hu))
  have hb3 : (newRowBitsF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i).getD j3 false = true :=
    (hbitN j3 hj3).2 ((hbit j3 hj3).2 (by rw [hpv]; exact hv))
  have hbx : (newRowBitsF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i).getD j2 false = true := by
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
theorem rowConvexF (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) (F : Finset Site)
    (hF : ∀ x, x ∈ F ↔ x ∈ lamO o ℓ (q + 1) ∨ x - posO o ℓ (q + 1) ∈ finRel o (stateOf o ℓ (q + 1)).secondL)
    (hS : RowConvex (lamO o ℓ (q + 1)))
    (hok : ∀ i : ℕ, i < 8 → rowOkF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i = true) :
    RowConvex F := by
  have hrows : ∀ i : ℕ, i < 8 → gapFree (newRowBitsF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i) = true ∧
      gapOkF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i = true := by
    intro i hi
    have h2 := (Bool.and_eq_true _ _).mp (hok i hi)
    exact ⟨h2.2, h2.1⟩
  have mono : ∀ p, p ∈ lamO o ℓ (q + 1) → p ∈ F := fun p hp => (hF p).2 (Or.inl hp)
  intro a ha b hb hab x hx
  obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.1 hx
  by_cases hAB : a ∈ lamO o ℓ (q + 1) ∧ b ∈ lamO o ℓ (q + 1)
  · exact mono _ (hS a hAB.1 b hAB.2 hab x hx)
  have hwinrow : (posO o ℓ (q + 1)).2 - 3 ≤ a.2 ∧ a.2 ≤ (posO o ℓ (q + 1)).2 + 3 := by
    by_cases haS : a ∈ lamO o ℓ (q + 1)
    · have hbn : b ∉ lamO o ℓ (q + 1) := fun h => hAB ⟨haS, h⟩
      have := new_boundsF o ℓ q F hF b hb hbn
      omega
    · have := new_boundsF o ℓ q F hF a ha haS
      omega
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = a.2 - (posO o ℓ (q + 1)).2 + 4 :=
    ⟨(a.2 - (posO o ℓ (q + 1)).2 + 4).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hi8 : i < 8 := by omega
  have hiy : a.2 = (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4) := by omega
  have hiyb : b.2 = (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4) := hab.symm.trans hiy
  obtain ⟨hgf, hgo⟩ := hrows i hi8
  have hc : ∃ c ∈ finRel o (stateOf o ℓ (q + 1)).secondL, c.2 = (i : ℤ) - 4 := by
    by_cases haS : a ∈ lamO o ℓ (q + 1)
    · have hbn : b ∉ lamO o ℓ (q + 1) := fun h => hAB ⟨haS, h⟩
      rcases (hF b).1 hb with h | h
      · exact absurd h hbn
      · refine ⟨b - posO o ℓ (q + 1), h, ?_⟩
        simp only [Prod.snd_sub]
        omega
    · rcases (hF a).1 ha with h | h
      · exact absurd h haS
      · refine ⟨a - posO o ℓ (q + 1), h, ?_⟩
        simp only [Prod.snd_sub]
        omega
  obtain ⟨c, hcm, hcy⟩ := hc
  by_cases hO : ∃ p ∈ lamO o ℓ (q + 1), p.2 = a.2
  · obtain ⟨p0, hp0, hp0y⟩ := hO
    obtain ⟨j, hj, hbj⟩ := gapOkF_common o ℓ q hq i hi8 hgo p0 hp0 (by rw [hp0y]; exact hiy) c hcm hcy
    have hcS : ((posO o ℓ (q + 1)).1 + ((j : ℤ) - 2), (posO o ℓ (q + 1)).2 + ((i : ℤ) - 4)) ∈
        lamO o ℓ (q + 1) := oldBitAt_spec o ℓ q i j hbj
    have hcS' := mono _ hcS
    have hcw : (posO o ℓ (q + 1)).1 - 2 ≤ (posO o ℓ (q + 1)).1 + ((j : ℤ) - 2) ∧
        (posO o ℓ (q + 1)).1 + ((j : ℤ) - 2) ≤ (posO o ℓ (q + 1)).1 + 3 := by
      omega
    by_cases haS : a ∈ lamO o ℓ (q + 1)
    · have hbn : b ∉ lamO o ℓ (q + 1) := fun h => hAB ⟨haS, h⟩
      have hbw := new_boundsF o ℓ q F hF b hb hbn
      by_cases hxc : x ≤ (posO o ℓ (q + 1)).1 + ((j : ℤ) - 2)
      · have hm := hS a haS _ hcS hiy x (Finset.mem_Icc.2 ⟨hx1, hxc⟩)
        exact mono _ hm
      · rw [hiy]
        exact window_convF o ℓ q hq F hF i hi8 hgf _ b hcS' hb rfl hiyb hcw ⟨hbw.1, hbw.2.1⟩ x
          (not_le.mp hxc).le hx2
    · by_cases hbS : b ∈ lamO o ℓ (q + 1)
      · have haw := new_boundsF o ℓ q F hF a ha haS
        by_cases hxc : (posO o ℓ (q + 1)).1 + ((j : ℤ) - 2) ≤ x
        · have hm := hS _ hcS b hbS (hiy.symm.trans hab) x (Finset.mem_Icc.2 ⟨hxc, hx2⟩)
          have hm' : (x, a.2) ∈ lamO o ℓ (q + 1) := by
            rw [hiy]
            exact hm
          exact mono _ hm'
        · rw [hiy]
          exact window_convF o ℓ q hq F hF i hi8 hgf a _ ha hcS' hiy rfl ⟨haw.1, haw.2.1⟩ hcw x hx1
            (not_le.mp hxc).le
      · have haw := new_boundsF o ℓ q F hF a ha haS
        have hbw := new_boundsF o ℓ q F hF b hb hbS
        rw [hiy]
        exact window_convF o ℓ q hq F hF i hi8 hgf a b ha hb hiy hiyb ⟨haw.1, haw.2.1⟩
          ⟨hbw.1, hbw.2.1⟩ x hx1 hx2
  · have haS : a ∉ lamO o ℓ (q + 1) := fun h => hO ⟨a, h, rfl⟩
    have hbS : b ∉ lamO o ℓ (q + 1) := fun h => hO ⟨b, h, hab.symm⟩
    have haw := new_boundsF o ℓ q F hF a ha haS
    have hbw := new_boundsF o ℓ q F hF b hb hbS
    rw [hiy]
    exact window_convF o ℓ q hq F hF i hi8 hgf a b ha hb hiy hiyb ⟨haw.1, haw.2.1⟩
      ⟨hbw.1, hbw.2.1⟩ x hx1 hx2

theorem rowsIntervalF (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (F : Finset Site)
    (hF : ∀ x, x ∈ F ↔ x ∈ lamO o ℓ (q + 1) ∨ x - posO o ℓ (q + 1) ∈ finRel o (stateOf o ℓ (q + 1)).secondL)
    (hI : RowsInterval (lamO o ℓ (q + 1)) (posO o ℓ q)) :
    RowsInterval F (posO o ℓ (q + 1)) := by
  obtain ⟨⟨p1, hp1, hp1y⟩, ⟨p2, hp2, hp2y⟩, hconv⟩ := hI
  have hsy0 := plusStep_snd_nonneg' o (ℓ (q + 1))
  have hsy2 := plusStep_snd_le2 o (ℓ (q + 1))
  have hA2 : (posO o ℓ (q + 1)).2 = (posO o ℓ q).2 + (plusStepO o (ℓ (q + 1))).2 := by
    rw [posO_new']
    simp only [Prod.snd_add]
  have hmono : ∀ p ∈ lamO o ℓ (q + 1), p ∈ F := fun p hp => (hF p).2 (Or.inl hp)
  have hz0 : posO o ℓ (q + 1) - posO o ℓ (q + 1) = ((0 : ℤ), (0 : ℤ)) :=
    Prod.ext (sub_self _) (sub_self _)
  have hA0 : posO o ℓ (q + 1) ∈ F :=
    (hF _).2 (Or.inr (by rw [hz0]; exact finRel_zero _ _))
  have hA1 : posO o ℓ (q + 1) + ((0 : ℤ), (1 : ℤ)) ∈ F :=
    (hF _).2 (Or.inr (by rw [add_sub_cancel_left]; exact finRel_one _ _))
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
    · have haw := new_boundsF o ℓ q F hF a ha haS
      have hd := ((hF a).1 ha).resolve_left haS
      have hdy : (a - posO o ℓ (q + 1)).2 = a.2 - (posO o ℓ (q + 1)).2 := Prod.snd_sub _ _
      obtain ⟨e, he, hey⟩ := finRel_lower o _ _ hd (by omega) (y - (posO o ℓ (q + 1)).2)
        (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      refine ⟨posO o ℓ (q + 1) + e, (hF _).2 (Or.inr ?_), ?_⟩
      · rw [add_sub_cancel_left]
        exact he
      · show (posO o ℓ (q + 1)).2 + e.2 = y
        rw [hey]
        omega
  · have hup : (posO o ℓ q).2 + 2 ≤ y ∨ (posO o ℓ q).2 + 1 < y := by omega
    by_cases hbS : b ∈ lamO o ℓ (q + 1)
    · obtain ⟨p, hp, hpy⟩ := hconv p2 hp2 b hbS (by omega) y (Finset.mem_Icc.2 ⟨by omega, hy2⟩)
      exact ⟨p, hmono p hp, hpy⟩
    · have hbw := new_boundsF o ℓ q F hF b hb hbS
      have hd := ((hF b).1 hb).resolve_left hbS
      have hdy : (b - posO o ℓ (q + 1)).2 = b.2 - (posO o ℓ (q + 1)).2 := Prod.snd_sub _ _
      obtain ⟨e, he, hey⟩ := finRel_upper o _ _ hd (by omega) (y - (posO o ℓ (q + 1)).2)
        (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      refine ⟨posO o ℓ (q + 1) + e, (hF _).2 (Or.inr ?_), ?_⟩
      · rw [add_sub_cancel_left]
        exact he
      · show (posO o ℓ (q + 1)).2 + e.2 = y
        rw [hey]
        omega

theorem rowsLinkedF (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) (F : Finset Site)
    (hF : ∀ x, x ∈ F ↔ x ∈ lamO o ℓ (q + 1) ∨ x - posO o ℓ (q + 1) ∈ finRel o (stateOf o ℓ (q + 1)).secondL)
    (hL : RowsLinked (lamO o ℓ (q + 1)))
    (hI0 : RowsInterval (lamO o ℓ (q + 1)) (posO o ℓ q))
    (hI : RowsInterval F (posO o ℓ (q + 1)))
    (hpair : ∀ k : ℕ, k < 7 → pairOkF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) k = true) :
    RowsLinked F := by
  obtain ⟨⟨p1, hp1, hp1y⟩, _, _⟩ := hI0
  have hsy0 := plusStep_snd_nonneg' o (ℓ (q + 1))
  have hsy2 := plusStep_snd_le2 o (ℓ (q + 1))
  have hA2 : (posO o ℓ (q + 1)).2 = (posO o ℓ q).2 + (plusStepO o (ℓ (q + 1))).2 := by
    rw [posO_new']
    simp only [Prod.snd_add]
  have hmono : ∀ p ∈ lamO o ℓ (q + 1), p ∈ F := fun p hp => (hF p).2 (Or.inl hp)
  intro a ha b hb hab y hy
  obtain ⟨hy1, hy2⟩ := Finset.mem_Ico.1 hy
  have hyS : RowSet F y := hI.2.2 a ha b hb hab y (Finset.mem_Icc.2 ⟨hy1, by omega⟩)
  have hyS1 : RowSet F (y + 1) := hI.2.2 a ha b hb hab (y + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have hb2 := F_top o ℓ q hq F hF b hb
  by_cases hwin : (posO o ℓ (q + 1)).2 - 4 ≤ y
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = y - (posO o ℓ (q + 1)).2 + 4 :=
      ⟨(y - (posO o ℓ (q + 1)).2 + 4).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hk7 : k < 7 := by omega
    have hk8 : k < 8 := by omega
    have hk1 : k + 1 < 8 := by omega
    have hpk := hpair k hk7
    unfold pairOkF at hpk
    have hnk : newNeF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) k = true := by
      rw [ne_bridgeF o ℓ q hq F hF k hk8]
      have e : (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4) = y := by omega
      exact decide_eq_true (by rw [e]; exact hyS)
    have hnk1 : newNeF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) (k + 1) = true := by
      rw [ne_bridgeF o ℓ q hq F hF (k + 1) hk1]
      have e : (posO o ℓ (q + 1)).2 + (((k + 1 : ℕ) : ℤ) - 4) = y + 1 := by
        push_cast
        omega
      exact decide_eq_true (by rw [e]; exact hyS1)
    simp only [hnk, hnk1, Bool.and_self, Bool.not_true, Bool.false_or] at hpk
    have h1 : decide (((F.image Prod.fst).filter (fun x => (x, (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4)) ∈ F ∧
        (x, (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4) + 1) ∈ F)).Nonempty) = true := by
      rw [← sh_bridgeF o ℓ q hq F hF k hk7]
      exact hpk
    obtain ⟨x, hx⟩ := of_decide_eq_true h1
    obtain ⟨_, hx1, hx2⟩ := Finset.mem_filter.1 hx
    have hyk : (posO o ℓ (q + 1)).2 + ((k : ℤ) - 4) = y := by omega
    rw [hyk] at hx1 hx2
    exact ⟨x, Finset.mem_image.2 ⟨(x, y), hx1, rfl⟩, hx1, hx2⟩
  · have haS : a ∈ lamO o ℓ (q + 1) := by
      by_contra haS
      have haw := new_boundsF o ℓ q F hF a ha haS
      omega
    obtain ⟨x, hxI, h1, h2⟩ := hL a haS p1 hp1 (by omega) y (Finset.mem_Ico.2 ⟨hy1, by omega⟩)
    obtain ⟨c, hc, hcx⟩ := Finset.mem_image.1 hxI
    exact ⟨x, Finset.mem_image.2 ⟨c, hmono c hc, hcx⟩, hmono _ h1, hmono _ h2⟩

theorem goodF (o : Orientation) (ℓ : ℕ → Letter) (q : ℕ) (hq : 1 ≤ q) (F : Finset Site)
    (hF : ∀ x, x ∈ F ↔ x ∈ lamO o ℓ (q + 1) ∨ x - posO o ℓ (q + 1) ∈ finRel o (stateOf o ℓ (q + 1)).secondL)
    (hG : GoodAt o ℓ q)
    (hok : ∀ i : ℕ, i < 8 → rowOkF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) i = true)
    (hpair : ∀ k : ℕ, k < 7 → pairOkF o (stateOf o ℓ (q + 1)) (ℓ (q + 1)) k = true) :
    RowConvex F ∧ RowsLinked F := by
  have hI := rowsIntervalF o ℓ q F hF hG.ivl
  exact ⟨rowConvexF o ℓ q hq F hF hG.conv hok, rowsLinkedF o ℓ q hq F hF hG.link hG.ivl hI hpair⟩

end FLatticePaper.Tiles
