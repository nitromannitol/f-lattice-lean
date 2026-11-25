import FLatticePaper.Plane.Induction.TwosTileCoverB

/-! The range of the deck rank at native points (sign +1), and `hvar` for `twosRank_strict`.

`deckAt a 1 X Y` is `pickFirst` of the free offers of the nine aliases of `(X, Y)` followed by the bulk offers. The free offers
take values in `[0, 2a+1]` on their free sites. The bulk offer of the first alias is `bulkR` at `(X, Y)` itself (a native point),
and it is used only when no alias is free; then `p − U` is not free, and `bulkR` lies in `[0, 2a+1]` on such native points.
So `deckAt` lies in `[0, 2a+1]` at every native point, and `rhoTwos` at a tile point is such a value. -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper
open scoped Classical

theorem tr_freeH_range {a x y : ℤ} (ha : 4 ≤ a) (hF : FreeHSite a x y) :
    0 ≤ freeH a 1 x y ∧ freeH a 1 x y ≤ 2 * a + 1 := by
  unfold FreeHSite at hF
  simp only [freeH]
  split_ifs <;> omega

theorem tr_freeV_range {a x y : ℤ} (hF : FreeVSite a x y) :
    0 ≤ freeV a 1 x y ∧ freeV a 1 x y ≤ 2 * a + 1 := by
  unfold FreeVSite at hF
  simp only [freeV]
  split_ifs <;> omega

theorem tr_bulk_range {a x y : ℤ} (ha : 4 ≤ a) (he : a % 2 = 0) (hN : NativeT a x y)
    (hnf : ¬ FreeSite a (x - (a + 1)) (y - (a - 1))) :
    0 ≤ bulkR a 1 x y ∧ bulkR a 1 x y ≤ 2 * a + 1 := by
  unfold NativeT at hN
  unfold FreeSite FreeHSite FreeVSite at hnf
  simp only [bulkR]
  split_ifs <;> omega

theorem tr_pickFirst_spec (P : ℤ → Prop) (L : List (Prop × ℤ)) : ∀ d : ℤ,
    (∀ x ∈ L, x.1 → P x.2) → ((∃ x ∈ L, x.1) ∨ P d) → P (pickFirst L d) := by
  induction L with
  | nil =>
    intro d _ h
    rcases h with ⟨x, hx, -⟩ | h
    · exact absurd hx (List.not_mem_nil)
    · exact h
  | cons x rest ih =>
    intro d hL h
    obtain ⟨g, v⟩ := x
    by_cases hg : g
    · rw [pickFirst, if_pos hg]
      exact hL (g, v) (by simp) hg
    · rw [pickFirst, if_neg hg]
      apply ih d
      · intro y hy hyg
        exact hL y (List.mem_cons_of_mem _ hy) hyg
      · rcases h with ⟨y, hy, hyg⟩ | h
        · rcases List.mem_cons.mp hy with rfl | hy'
          · exact absurd hyg hg
          · exact Or.inl ⟨y, hy', hyg⟩
        · exact Or.inr h

theorem tr_pickFirst_none (L : List (Prop × ℤ)) (d : ℤ) (h : ∀ x ∈ L, ¬ x.1) :
    pickFirst L d = d := by
  induction L with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨g, v⟩ := x
    have hg : ¬ g := h (g, v) (by simp)
    have hr : ∀ y ∈ rest, ¬ y.1 := fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [pickFirst, if_neg hg]
    exact ih hr

theorem tr_pickFirst_append (L1 L2 : List (Prop × ℤ)) (d : ℤ) :
    pickFirst (L1 ++ L2) d = pickFirst L1 (pickFirst L2 d) := by
  induction L1 with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨g, v⟩ := x
    by_cases hg : g
    · rw [List.cons_append, pickFirst, if_pos hg, pickFirst, if_pos hg]
    · rw [List.cons_append, pickFirst, if_neg hg, pickFirst, if_neg hg, ih]

/-- The deck value at a native point (sign +1) lies in `[0, 2a+1]`. -/
theorem tr_deck_range {a X Y : ℤ} (ha : 4 ≤ a) (he : a % 2 = 0) (hN : NativeT a X Y) :
    0 ≤ deckAt a 1 X Y ∧ deckAt a 1 X Y ≤ 2 * a + 1 := by
  unfold deckAt
  dsimp only
  rw [tr_pickFirst_append]
  have hbulk : pickFirst ((aliasAddrs a X Y).map (fun u => (NativeT a u.1 u.2, bulkR a 1 u.1 u.2)))
      (-1000) = bulkR a 1 X Y := by
    simp [aliasAddrs, pickFirst, hN]
  rw [hbulk]
  by_cases hfree : ∃ u ∈ aliasAddrs a X Y, FreeSite a u.1 u.2
  · obtain ⟨u, hu, hF⟩ := hfree
    have hex : (∃ x ∈ (aliasAddrs a X Y).flatMap (fun u => [(FreeHSite a u.1 u.2, freeH a 1 u.1 u.2),
        (FreeVSite a u.1 u.2, freeV a 1 u.1 u.2)]), x.1) ∨ (0 ≤ bulkR a 1 X Y ∧ bulkR a 1 X Y ≤ 2 * a + 1) := by
      left
      rcases hF with hH | hV
      · exact ⟨(FreeHSite a u.1 u.2, freeH a 1 u.1 u.2), List.mem_flatMap.mpr ⟨u, hu, by simp⟩, hH⟩
      · exact ⟨(FreeVSite a u.1 u.2, freeV a 1 u.1 u.2), List.mem_flatMap.mpr ⟨u, hu, by simp⟩, hV⟩
    have hL : ∀ x ∈ (aliasAddrs a X Y).flatMap (fun u => [(FreeHSite a u.1 u.2, freeH a 1 u.1 u.2),
        (FreeVSite a u.1 u.2, freeV a 1 u.1 u.2)]), x.1 → (0 ≤ x.2 ∧ x.2 ≤ 2 * a + 1) := by
      intro x hx hxg
      obtain ⟨w, -, hw⟩ := List.mem_flatMap.mp hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact tr_freeH_range ha hxg
      · exact tr_freeV_range hxg
    exact tr_pickFirst_spec (fun v => 0 ≤ v ∧ v ≤ 2 * a + 1) _ _ hL hex
  · have hnone : ∀ x ∈ (aliasAddrs a X Y).flatMap (fun u => [(FreeHSite a u.1 u.2, freeH a 1 u.1 u.2),
        (FreeVSite a u.1 u.2, freeV a 1 u.1 u.2)]), ¬ x.1 := by
      intro x hx hxg
      obtain ⟨w, hw, hwx⟩ := List.mem_flatMap.mp hx
      apply hfree
      refine ⟨w, hw, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hwx
      rcases hwx with rfl | rfl
      · exact Or.inl hxg
      · exact Or.inr hxg
    rw [tr_pickFirst_none _ _ hnone]
    have hmem : (X - (a + 1), Y - (a - 1)) ∈ aliasAddrs a X Y := by
      unfold aliasAddrs
      exact List.mem_map.mpr ⟨(1, 0), by simp, by simp⟩
    have hnf : ¬ FreeSite a (X - (a + 1)) (Y - (a - 1)) := fun h => hfree ⟨_, hmem, h⟩
    exact tr_bulk_range ha he hN hnf

/-- The deck rank of sign +1 at a site is in `[0, 2a+1]` (`a = 2k+4`). -/
theorem tr_rho_range (k : ℕ) (c : Site) :
    0 ≤ rhoTwos (2 * (k : ℤ) + 4) 1 c ∧ rhoTwos (2 * (k : ℤ) + 4) 1 c ≤ 2 * (2 * (k : ℤ) + 4) + 1 := by
  have hT : (0 : ℤ) < 2 * (2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 4 * (2 * (k : ℤ) + 4) - 2 := by
    nlinarith
  have hc0 : 0 ≤ classKey (2 * (k : ℤ) + 4) c := by
    unfold classKey
    exact Int.emod_nonneg _ hT.ne'
  have hcT : classKey (2 * (k : ℤ) + 4) c <
      2 * (2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 4 * (2 * (k : ℤ) + 4) - 2 := by
    unfold classKey
    exact Int.emod_lt_of_pos _ hT
  obtain ⟨hTP, -⟩ := tc_tilePoint_spec k hc0 hcT
  unfold rhoTwos
  exact tr_deck_range (by omega) (by omega) hTP.1

/-- **hvar:** the deck rank of sign +1 varies by less than `2(2k+5)+3` (`a = 2k+4`). -/
theorem tr_hvar (k : ℕ) (z w : Site) :
    rhoTwos (2 * (k : ℤ) + 4) 1 z - rhoTwos (2 * (k : ℤ) + 4) 1 w < 2 * (2 * (k : ℤ) + 5) + 3 := by
  have h1 := tr_rho_range k z
  have h2 := tr_rho_range k w
  omega

end FLatticePaper.TwosEPolicy
