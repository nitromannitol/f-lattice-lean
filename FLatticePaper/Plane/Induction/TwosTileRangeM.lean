import FLatticePaper.Plane.Induction.TwosTileRange

/-! The range of the deck rank of sign `-1` at native points, and `hvarM` for `twosRankOf_strict` at sign `-1`.

The sign `-1` offers take values in `[0, 2a+2]` on their free sites (`freeH`, `freeV` with `η = -1`), and the bulk offer is
`bulkR` with `η = -1`. The bulk offer is used only when no alias is free; it lies in `[0, 2a+2]` there (it may leave the
window only at a free site: at `(1,0)` and at the free alias `(X-U, ...)`), so the bulk lemma takes the two non-freeness facts
`¬ FreeSite (X, Y)` and `¬ FreeSite (X-U, Y-(a-1))`. Hence `deckAt` lies in `[0, 2a+2]` at every native point. -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper
open scoped Classical

theorem trm_freeH_range {a x y : ℤ} (ha : 4 ≤ a) (hF : FreeHSite a x y) :
    0 ≤ freeH a (-1) x y ∧ freeH a (-1) x y ≤ 2 * a + 2 := by
  unfold FreeHSite at hF
  simp only [freeH]
  split_ifs <;> omega

theorem trm_freeV_range {a x y : ℤ} (ha : 4 ≤ a) (hF : FreeVSite a x y) :
    0 ≤ freeV a (-1) x y ∧ freeV a (-1) x y ≤ 2 * a + 2 := by
  unfold FreeVSite at hF
  simp only [freeV, if_neg (show ¬ ((-1 : ℤ) = 1) by norm_num)]
  split_ifs <;> omega

set_option maxHeartbeats 400000 in
/-- The bulk value of sign `-1` at a native point lies in `[0, 2a+2]`, except at the two free points `(1,0)` and `(a, 2a-1)`. -/
theorem trm_bulk_core {a x y : ℤ} (ha : 4 ≤ a) (he : a % 2 = 0) (hN : NativeT a x y)
    (h1 : ¬ (x = 1 ∧ y = 0)) (h2 : ¬ (x = a ∧ y = 2 * a - 1)) :
    0 ≤ bulkR a (-1) x y ∧ bulkR a (-1) x y ≤ 2 * a + 2 := by
  unfold NativeT at hN
  simp only [bulkR]
  split_ifs <;> omega

/-- The deck value of sign `-1` at a native point lies in `[0, 2a+2]`. -/
theorem trm_deck_range {a X Y : ℤ} (ha : 4 ≤ a) (he : a % 2 = 0) (hN : NativeT a X Y) :
    0 ≤ deckAt a (-1) X Y ∧ deckAt a (-1) X Y ≤ 2 * a + 2 := by
  unfold deckAt
  dsimp only
  rw [tr_pickFirst_append]
  have hbulk : pickFirst ((aliasAddrs a X Y).map (fun u => (NativeT a u.1 u.2, bulkR a (-1) u.1 u.2)))
      (-1000) = bulkR a (-1) X Y := by
    simp [aliasAddrs, pickFirst, hN]
  rw [hbulk]
  by_cases hfree : ∃ u ∈ aliasAddrs a X Y, FreeSite a u.1 u.2
  · obtain ⟨u, hu, hF⟩ := hfree
    have hex : ∃ x ∈ (aliasAddrs a X Y).flatMap (fun u => [(FreeHSite a u.1 u.2, freeH a (-1) u.1 u.2),
        (FreeVSite a u.1 u.2, freeV a (-1) u.1 u.2)]), x.1 := by
      rcases hF with hH | hV
      · exact ⟨(FreeHSite a u.1 u.2, freeH a (-1) u.1 u.2), List.mem_flatMap.mpr ⟨u, hu, by simp⟩, hH⟩
      · exact ⟨(FreeVSite a u.1 u.2, freeV a (-1) u.1 u.2), List.mem_flatMap.mpr ⟨u, hu, by simp⟩, hV⟩
    have hL : ∀ x ∈ (aliasAddrs a X Y).flatMap (fun u => [(FreeHSite a u.1 u.2, freeH a (-1) u.1 u.2),
        (FreeVSite a u.1 u.2, freeV a (-1) u.1 u.2)]), x.1 → (0 ≤ x.2 ∧ x.2 ≤ 2 * a + 2) := by
      intro x hx hxg
      obtain ⟨w, -, hw⟩ := List.mem_flatMap.mp hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact trm_freeH_range ha hxg
      · exact trm_freeV_range ha hxg
    exact tr_pickFirst_spec (fun v => 0 ≤ v ∧ v ≤ 2 * a + 2) _ _ hL (Or.inl hex)
  · have hnone : ∀ x ∈ (aliasAddrs a X Y).flatMap (fun u => [(FreeHSite a u.1 u.2, freeH a (-1) u.1 u.2),
        (FreeVSite a u.1 u.2, freeV a (-1) u.1 u.2)]), ¬ x.1 := by
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
    have hmem0 : (X, Y) ∈ aliasAddrs a X Y := by
      unfold aliasAddrs
      exact List.mem_map.mpr ⟨(0, 0), by simp, by simp⟩
    have hnf : ¬ FreeSite a (X - (a + 1)) (Y - (a - 1)) := fun h => hfree ⟨_, hmem, h⟩
    have hnf0 : ¬ FreeSite a X Y := fun h => hfree ⟨_, hmem0, h⟩
    have h1 : ¬ (X = 1 ∧ Y = 0) := fun e => hnf0 (Or.inl (Or.inl e))
    have h2 : ¬ (X = a ∧ Y = 2 * a - 1) := fun e => hnf (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩))
    exact trm_bulk_core ha he hN h1 h2

/-- The deck rank of sign `-1` at a site is in `[0, 2a+2]` (`a = 2k+4`). -/
theorem trm_rho_range (k : ℕ) (c : Site) :
    0 ≤ rhoTwos (2 * (k : ℤ) + 4) (-1) c ∧ rhoTwos (2 * (k : ℤ) + 4) (-1) c ≤ 2 * (2 * (k : ℤ) + 4) + 2 := by
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
  exact trm_deck_range (by omega) (by omega) hTP.1

/-- **hvarM:** the deck rank of sign `-1` varies by less than `2(2k+5)+3` (`a = 2k+4`). -/
theorem tr_hvarM (k : ℕ) (z w : Site) :
    rhoTwos (2 * (k : ℤ) + 4) (-1) z - rhoTwos (2 * (k : ℤ) + 4) (-1) w < 2 * (2 * (k : ℤ) + 5) + 3 := by
  have h1 := trm_rho_range k z
  have h2 := trm_rho_range k w
  omega

end FLatticePaper.TwosEPolicy
