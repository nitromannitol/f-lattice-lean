import FLatticePaper.Plane.Induction.TwosRhoCases

/-! Twos flatness, the deck value at the special point `(a, 2a-1)` (sign `+1`). The deck `deckAt` picks the first true guard of
its window list (`pickFirst`). For `(a, 2a-1)` the first true guard is the `V`-entry of the window address `(a - (a+1) + 0, a)`,
that is the free `V` site `(-1, a)`; the thirteen entries before it are false. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

/-- `pickFirst` over a prefix of false guards followed by a true entry returns that entry's value. -/
theorem pickFirst_hit (L1 L2 : List (Prop × ℤ)) (p : Prop) (v d : ℤ) (h1 : ∀ q ∈ L1, ¬ q.1) (hp : p) :
    pickFirst (L1 ++ (p, v) :: L2) d = v := by
  induction L1 with
  | nil => simp [pickFirst, hp]
  | cons q L1' ih =>
    obtain ⟨g, w⟩ := q
    have hg : ¬ g := h1 (g, w) (by simp)
    simp only [List.cons_append, pickFirst, if_neg hg]
    exact ih (fun r hr => h1 r (by simp [hr]))

set_option maxHeartbeats 400000 in
/-- The deck value at the special point `(a, 2a-1)` is `1`. -/
theorem deck_special_1 {a : ℤ} (ha : 4 ≤ a) : deckAt a 1 a (2 * a - 1) = 1 := by
  have hL1 : ∀ q ∈ ([(FreeHSite a (a - (0) * (a + 1) + 2 * (0)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (0)), freeH a 1 (a - (0) * (a + 1) + 2 * (0)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (0))),
      (FreeVSite a (a - (0) * (a + 1) + 2 * (0)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (0)), freeV a 1 (a - (0) * (a + 1) + 2 * (0)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (0))),
      (FreeHSite a (a - (0) * (a + 1) + 2 * (-1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (-1)), freeH a 1 (a - (0) * (a + 1) + 2 * (-1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (-1))),
      (FreeVSite a (a - (0) * (a + 1) + 2 * (-1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (-1)), freeV a 1 (a - (0) * (a + 1) + 2 * (-1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (-1))),
      (FreeHSite a (a - (0) * (a + 1) + 2 * (1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (1)), freeH a 1 (a - (0) * (a + 1) + 2 * (1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (1))),
      (FreeVSite a (a - (0) * (a + 1) + 2 * (1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (1)), freeV a 1 (a - (0) * (a + 1) + 2 * (1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (1))),
      (FreeHSite a (a - (-1) * (a + 1) + 2 * (0)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (0)), freeH a 1 (a - (-1) * (a + 1) + 2 * (0)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (0))),
      (FreeVSite a (a - (-1) * (a + 1) + 2 * (0)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (0)), freeV a 1 (a - (-1) * (a + 1) + 2 * (0)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (0))),
      (FreeHSite a (a - (-1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (-1)), freeH a 1 (a - (-1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (-1))),
      (FreeVSite a (a - (-1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (-1)), freeV a 1 (a - (-1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (-1))),
      (FreeHSite a (a - (-1) * (a + 1) + 2 * (1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (1)), freeH a 1 (a - (-1) * (a + 1) + 2 * (1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (1))),
      (FreeVSite a (a - (-1) * (a + 1) + 2 * (1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (1)), freeV a 1 (a - (-1) * (a + 1) + 2 * (1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (1))),
      (FreeHSite a (a - (1) * (a + 1) + 2 * (0)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (0)), freeH a 1 (a - (1) * (a + 1) + 2 * (0)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (0)))]), ¬ q.1 := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (dsimp only; simp only [FreeHSite, FreeVSite]; omega)
  have hdeck : deckAt a 1 a (2 * a - 1) = pickFirst (([(FreeHSite a (a - (0) * (a + 1) + 2 * (0)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (0)), freeH a 1 (a - (0) * (a + 1) + 2 * (0)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (0))),
      (FreeVSite a (a - (0) * (a + 1) + 2 * (0)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (0)), freeV a 1 (a - (0) * (a + 1) + 2 * (0)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (0))),
      (FreeHSite a (a - (0) * (a + 1) + 2 * (-1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (-1)), freeH a 1 (a - (0) * (a + 1) + 2 * (-1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (-1))),
      (FreeVSite a (a - (0) * (a + 1) + 2 * (-1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (-1)), freeV a 1 (a - (0) * (a + 1) + 2 * (-1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (-1))),
      (FreeHSite a (a - (0) * (a + 1) + 2 * (1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (1)), freeH a 1 (a - (0) * (a + 1) + 2 * (1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (1))),
      (FreeVSite a (a - (0) * (a + 1) + 2 * (1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (1)), freeV a 1 (a - (0) * (a + 1) + 2 * (1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (1))),
      (FreeHSite a (a - (-1) * (a + 1) + 2 * (0)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (0)), freeH a 1 (a - (-1) * (a + 1) + 2 * (0)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (0))),
      (FreeVSite a (a - (-1) * (a + 1) + 2 * (0)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (0)), freeV a 1 (a - (-1) * (a + 1) + 2 * (0)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (0))),
      (FreeHSite a (a - (-1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (-1)), freeH a 1 (a - (-1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (-1))),
      (FreeVSite a (a - (-1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (-1)), freeV a 1 (a - (-1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (-1))),
      (FreeHSite a (a - (-1) * (a + 1) + 2 * (1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (1)), freeH a 1 (a - (-1) * (a + 1) + 2 * (1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (1))),
      (FreeVSite a (a - (-1) * (a + 1) + 2 * (1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (1)), freeV a 1 (a - (-1) * (a + 1) + 2 * (1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (1))),
      (FreeHSite a (a - (1) * (a + 1) + 2 * (0)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (0)), freeH a 1 (a - (1) * (a + 1) + 2 * (0)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (0)))]) ++ ((FreeVSite a (a - (1) * (a + 1) + 2 * (0)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (0)), freeV a 1 (a - (1) * (a + 1) + 2 * (0)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (0))) :: ([(FreeHSite a (a - (1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (-1)), freeH a 1 (a - (1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (-1))),
      (FreeVSite a (a - (1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (-1)), freeV a 1 (a - (1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (-1))),
      (FreeHSite a (a - (1) * (a + 1) + 2 * (1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (1)), freeH a 1 (a - (1) * (a + 1) + 2 * (1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (1))),
      (FreeVSite a (a - (1) * (a + 1) + 2 * (1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (1)), freeV a 1 (a - (1) * (a + 1) + 2 * (1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (1))),
      (NativeT a (a - (0) * (a + 1) + 2 * (0)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (0)), bulkR a 1 (a - (0) * (a + 1) + 2 * (0)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (0))),
      (NativeT a (a - (0) * (a + 1) + 2 * (-1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (-1)), bulkR a 1 (a - (0) * (a + 1) + 2 * (-1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (-1))),
      (NativeT a (a - (0) * (a + 1) + 2 * (1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (1)), bulkR a 1 (a - (0) * (a + 1) + 2 * (1)) (2 * a - 1 - (0) * (a - 1) - 2 * a * (1))),
      (NativeT a (a - (-1) * (a + 1) + 2 * (0)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (0)), bulkR a 1 (a - (-1) * (a + 1) + 2 * (0)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (0))),
      (NativeT a (a - (-1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (-1)), bulkR a 1 (a - (-1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (-1))),
      (NativeT a (a - (-1) * (a + 1) + 2 * (1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (1)), bulkR a 1 (a - (-1) * (a + 1) + 2 * (1)) (2 * a - 1 - (-1) * (a - 1) - 2 * a * (1))),
      (NativeT a (a - (1) * (a + 1) + 2 * (0)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (0)), bulkR a 1 (a - (1) * (a + 1) + 2 * (0)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (0))),
      (NativeT a (a - (1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (-1)), bulkR a 1 (a - (1) * (a + 1) + 2 * (-1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (-1))),
      (NativeT a (a - (1) * (a + 1) + 2 * (1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (1)), bulkR a 1 (a - (1) * (a + 1) + 2 * (1)) (2 * a - 1 - (1) * (a - 1) - 2 * a * (1)))]))) (-1000) := rfl
  rw [hdeck, pickFirst_hit _ _ _ _ _ hL1 (by simp only [FreeVSite]; omega)]
  rw [freeV_hi (by omega)]
  omega

end FLatticePaper.TwosEPolicy
