import FLatticePaper.Plane.Induction.TwosSpecialRho
import FLatticePaper.Plane.Induction.TwosDeckEta

/-! Twos flatness, the deck value at the special point `(a, 2a-1)` for sign `-1`.

The window of `deck_special_1` (sign `+1`) is the same list with `η = -1`: its guards do not depend on the sign, so the first true
guard is again the `V`-entry of the address `(-1, a)`, whose value for sign `-1` at height `y = a` is `2` (`freeV_minus_mid`).
The archive value is `2` (the closed bulk formula gives `2a+4` there, so this point is special, as for sign `+1`). -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

/-- The sign `-1` value of the vertical free offer at height `y = a` is `2`. -/
theorem freeV_minus_mid {a : ℤ} (ha : 4 ≤ a) (x y : ℤ) (hy : y = a) : freeV a (-1) x y = 2 := by
  unfold freeV
  dsimp only
  have h1 : y ≠ 0 := by omega
  have h2 : ¬ y < a := by omega
  rw [if_neg (show ¬ ((-1 : ℤ) = 1) by norm_num), if_neg h1, if_neg h2, if_pos hy]

set_option maxHeartbeats 400000 in
/-- The deck value at the special point `(a, 2a-1)` for sign `-1` is `2`. -/
theorem deck_special_minus {a : ℤ} (ha : 4 ≤ a) : deckAt a (-1) a (2 * a - 1) = 2 := by
  have hL1 : ∀ q ∈ ([(FreeHSite a (a - (0) * (a + 1) + 2 * (0)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (0)), freeH a (-1) (a - (0) * (a + 1) + 2 * (0)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (0))),
      (FreeVSite a (a - (0) * (a + 1) + 2 * (0)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (0)), freeV a (-1) (a - (0) * (a + 1) + 2 * (0)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (0))),
      (FreeHSite a (a - (0) * (a + 1) + 2 * (-1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (-1)), freeH a (-1) (a - (0) * (a + 1) + 2 * (-1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (-1))),
      (FreeVSite a (a - (0) * (a + 1) + 2 * (-1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (-1)), freeV a (-1) (a - (0) * (a + 1) + 2 * (-1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (-1))),
      (FreeHSite a (a - (0) * (a + 1) + 2 * (1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (1)), freeH a (-1) (a - (0) * (a + 1) + 2 * (1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (1))),
      (FreeVSite a (a - (0) * (a + 1) + 2 * (1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (1)), freeV a (-1) (a - (0) * (a + 1) + 2 * (1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (1))),
      (FreeHSite a (a - (-1) * (a + 1) + 2 * (0)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (0)), freeH a (-1) (a - (-1) * (a + 1) + 2 * (0)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (0))),
      (FreeVSite a (a - (-1) * (a + 1) + 2 * (0)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (0)), freeV a (-1) (a - (-1) * (a + 1) + 2 * (0)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (0))),
      (FreeHSite a (a - (-1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (-1)), freeH a (-1) (a - (-1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (-1))),
      (FreeVSite a (a - (-1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (-1)), freeV a (-1) (a - (-1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (-1))),
      (FreeHSite a (a - (-1) * (a + 1) + 2 * (1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (1)), freeH a (-1) (a - (-1) * (a + 1) + 2 * (1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (1))),
      (FreeVSite a (a - (-1) * (a + 1) + 2 * (1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (1)), freeV a (-1) (a - (-1) * (a + 1) + 2 * (1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (1))),
      (FreeHSite a (a - (1) * (a + 1) + 2 * (0)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (0)), freeH a (-1) (a - (1) * (a + 1) + 2 * (0)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (0)))]), ¬ q.1 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (dsimp only; simp only [FreeHSite, FreeVSite]; omega)
  have hdeck : deckAt a (-1) a (2 * a - 1) = pickFirst (([(FreeHSite a (a - (0) * (a + 1) + 2 * (0)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (0)), freeH a (-1) (a - (0) * (a + 1) + 2 * (0)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (0))),
      (FreeVSite a (a - (0) * (a + 1) + 2 * (0)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (0)), freeV a (-1) (a - (0) * (a + 1) + 2 * (0)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (0))),
      (FreeHSite a (a - (0) * (a + 1) + 2 * (-1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (-1)), freeH a (-1) (a - (0) * (a + 1) + 2 * (-1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (-1))),
      (FreeVSite a (a - (0) * (a + 1) + 2 * (-1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (-1)), freeV a (-1) (a - (0) * (a + 1) + 2 * (-1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (-1))),
      (FreeHSite a (a - (0) * (a + 1) + 2 * (1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (1)), freeH a (-1) (a - (0) * (a + 1) + 2 * (1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (1))),
      (FreeVSite a (a - (0) * (a + 1) + 2 * (1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (1)), freeV a (-1) (a - (0) * (a + 1) + 2 * (1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (1))),
      (FreeHSite a (a - (-1) * (a + 1) + 2 * (0)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (0)), freeH a (-1) (a - (-1) * (a + 1) + 2 * (0)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (0))),
      (FreeVSite a (a - (-1) * (a + 1) + 2 * (0)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (0)), freeV a (-1) (a - (-1) * (a + 1) + 2 * (0)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (0))),
      (FreeHSite a (a - (-1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (-1)), freeH a (-1) (a - (-1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (-1))),
      (FreeVSite a (a - (-1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (-1)), freeV a (-1) (a - (-1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (-1))),
      (FreeHSite a (a - (-1) * (a + 1) + 2 * (1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (1)), freeH a (-1) (a - (-1) * (a + 1) + 2 * (1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (1))),
      (FreeVSite a (a - (-1) * (a + 1) + 2 * (1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (1)), freeV a (-1) (a - (-1) * (a + 1) + 2 * (1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (1))),
      (FreeHSite a (a - (1) * (a + 1) + 2 * (0)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (0)), freeH a (-1) (a - (1) * (a + 1) + 2 * (0)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (0)))]) ++ ((FreeVSite a (a - (1) * (a + 1) + 2 * (0)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (0)), freeV a (-1) (a - (1) * (a + 1) + 2 * (0)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (0))) :: ([(FreeHSite a (a - (1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (-1)), freeH a (-1) (a - (1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (-1))),
      (FreeVSite a (a - (1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (-1)), freeV a (-1) (a - (1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (-1))),
      (FreeHSite a (a - (1) * (a + 1) + 2 * (1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (1)), freeH a (-1) (a - (1) * (a + 1) + 2 * (1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (1))),
      (FreeVSite a (a - (1) * (a + 1) + 2 * (1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (1)), freeV a (-1) (a - (1) * (a + 1) + 2 * (1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (1))),
      (NativeT a (a - (0) * (a + 1) + 2 * (0)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (0)), bulkR a (-1) (a - (0) * (a + 1) + 2 * (0)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (0))),
      (NativeT a (a - (0) * (a + 1) + 2 * (-1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (-1)), bulkR a (-1) (a - (0) * (a + 1) + 2 * (-1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (-1))),
      (NativeT a (a - (0) * (a + 1) + 2 * (1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (1)), bulkR a (-1) (a - (0) * (a + 1) + 2 * (1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (1))),
      (NativeT a (a - (-1) * (a + 1) + 2 * (0)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (0)), bulkR a (-1) (a - (-1) * (a + 1) + 2 * (0)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (0))),
      (NativeT a (a - (-1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (-1)), bulkR a (-1) (a - (-1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (-1))),
      (NativeT a (a - (-1) * (a + 1) + 2 * (1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (1)), bulkR a (-1) (a - (-1) * (a + 1) + 2 * (1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (1))),
      (NativeT a (a - (1) * (a + 1) + 2 * (0)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (0)), bulkR a (-1) (a - (1) * (a + 1) + 2 * (0)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (0))),
      (NativeT a (a - (1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (-1)), bulkR a (-1) (a - (1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (-1))),
      (NativeT a (a - (1) * (a + 1) + 2 * (1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (1)), bulkR a (-1) (a - (1) * (a + 1) + 2 * (1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (1)))]))) (-1000) := rfl
  rw [hdeck, pickFirst_hit _ _ _ _ _ hL1 (by simp only [FreeVSite]; omega)]
  exact freeV_minus_mid ha _ _ (by ring)

end FLatticePaper.TwosEPolicy

end
