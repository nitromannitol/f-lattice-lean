import FLatticePaper.Plane.Induction.TwosFreeAssembly
import FLatticePaper.Plane.Induction.TwosFreeCases

/-! Twos flatness, the free centres (sign `+1`): the values of `freeDisp` on each free class, and the free flat drop. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

theorem fd_H1 {a : ℤ} : freeDisp a 1 1 0 = (0, -1) := by
  unfold freeDisp
  rw [if_pos (show FreeHSite a 1 0 from Or.inl ⟨rfl, rfl⟩), if_pos ⟨rfl, rfl⟩]

theorem fd_Heven {a x : ℤ} (h2 : 2 ≤ x) (h3 : x ≤ a) : freeDisp a 1 x (x - 2) = (1, 0) := by
  unfold freeDisp
  rw [if_pos (show FreeHSite a x (x - 2) from Or.inr (Or.inl ⟨h2, h3, rfl⟩)), if_neg (by omega),
    if_pos (by unfold EvenSite; dsimp only; omega)]

theorem fd_V00 {a : ℤ} : freeDisp a 1 0 0 = (1, 0) := by
  unfold freeDisp
  rw [if_neg (by unfold FreeHSite; omega), if_pos ⟨rfl, rfl⟩]

theorem fd_Veven {a y : ℤ} (h1 : 1 ≤ y) (h2 : y < a) (he : y % 2 = 0) : freeDisp a 1 0 y = (1, 0) := by
  unfold freeDisp
  rw [if_neg (by unfold FreeHSite; omega), if_neg (by omega), if_pos (by unfold EvenSite; dsimp only; omega)]

theorem fd_Vodd {a y : ℤ} (h1 : 1 ≤ y) (h2 : y < a) (ho : y % 2 = 1) : freeDisp a 1 0 y = (0, -1) := by
  unfold freeDisp
  rw [if_neg (by unfold FreeHSite; omega), if_neg (by omega), if_neg (by unfold EvenSite; dsimp only; omega)]

theorem fd_m1odd {a y : ℤ} (h1 : a < y) (h2 : y < 2 * a) (ho : y % 2 = 1) : freeDisp a 1 (-1) y = (1, 0) := by
  unfold freeDisp
  rw [if_neg (by unfold FreeHSite; omega), if_neg (by omega), if_pos (by unfold EvenSite; dsimp only; omega)]

theorem fd_m1even {a y : ℤ} (h1 : a < y) (h2 : y < 2 * a) (he : y % 2 = 0) : freeDisp a 1 (-1) y = (0, -1) := by
  unfold freeDisp
  rw [if_neg (by unfold FreeHSite; omega), if_neg (by omega), if_neg (by unfold EvenSite; dsimp only; omega)]

end FLatticePaper.TwosEPolicy
