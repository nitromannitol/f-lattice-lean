import FLatticePaper.Plane.Induction.W1OffCollarCases
import FLatticePaper.Plane.Induction.W1Constructor

/-! # The strict box of the opposite point `y`

For `ε = +1` the opposite point is `y = z − K` with `K = (d, n)`; since `t(K) = 0` and `s(K) = T`, the strict box of the centre `z`
is the box of `y`: `t(y) = t(z)`, `s(y) = s(z) − T`. For `ε = −1` the point is `y = z`. The sites `y` and `z` have the same parity
because `d + n` is even. -/

namespace FLatticePaper.OppYBox

open FLatticePaper FLatticePaper.W1 FLatticePaper.W1OffCollarCases

theorem ybox_plus {n d : ℤ} (hL : (d + n) % 2 = 0) (y : Site)
    (h : FLatticePaper.W1.StrictInterior n d (y + (d, n))) :
    (EvenSite y ∧ d + n - 1 - w1T n d ≤ w1t n d y ∧ w1t n d y ≤ 1 ∧
        2 * n - w1T n d + 1 ≤ w1s n d y ∧ w1s n d y ≤ -1) ∨
      (¬ EvenSite y ∧ d - w1T n d + 1 ≤ w1t n d y ∧ w1t n d y ≤ n - 1 ∧
        d + n - 1 - w1T n d ≤ w1s n d y ∧ w1s n d y ≤ 1 - d + n) := by
  have hp : EvenSite (y + (d, n)) ↔ EvenSite y := by
    unfold EvenSite
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have ht : w1t n d (y + (d, n)) = w1t n d y := by
    unfold w1t
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have hs : w1s n d (y + (d, n)) = w1s n d y + w1T n d := by
    unfold w1s w1T
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  rw [strict_grades, hp, ht, hs] at h
  rcases h with ⟨he, h1, h2, h3, h4⟩ | ⟨hno, h1, h2, h3, h4⟩
  · exact Or.inl ⟨he, by omega, by omega, by omega, by omega⟩
  · exact Or.inr ⟨hno, by omega, by omega, by omega, by omega⟩

theorem ybox_minus {n d : ℤ} (y : Site) (h : FLatticePaper.W1.StrictInterior n d y) :
    (EvenSite y ∧ d + n - 1 - w1T n d ≤ w1t n d y ∧ w1t n d y ≤ 1 ∧
        2 * n + 1 ≤ w1s n d y ∧ w1s n d y ≤ w1T n d - 1) ∨
      (¬ EvenSite y ∧ d - w1T n d + 1 ≤ w1t n d y ∧ w1t n d y ≤ n - 1 ∧
        d + n - 1 ≤ w1s n d y ∧ w1s n d y ≤ w1T n d + 1 - d + n) := by
  rw [strict_grades] at h
  rcases h with ⟨he, h1, h2, h3, h4⟩ | ⟨hno, h1, h2, h3, h4⟩
  · exact Or.inl ⟨he, by omega, by omega, by omega, by omega⟩
  · exact Or.inr ⟨hno, by omega, by omega, by omega, by omega⟩

end FLatticePaper.OppYBox
