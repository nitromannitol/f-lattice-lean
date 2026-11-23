import FLatticePaper.Plane.Induction.TwosInduction
import FLatticePaper.Plane.Induction.StandardField

/-! Task 72 / Q20 scope: the child gap `d − n` of a word is `2` exactly at the two-power words `2^k`, and at least `4` at every
other proper word (the census agrees to length seven).

With `δ_o = D_o − N_o` and `δ_e = D_e − N_e` for the parent pair, the digits act as
`one: (δ_o + δ_e, 2δ_o + δ_e)`, `two: (δ_o + δ_e, δ_e)`, `three: (δ_o, 2δ_o + δ_e)`, from the root `(1, 0)`, and the child
gap is `2δ_o + δ_e`. The register `δ_e` never decreases, and it is at least `2` after the first digit other than `two`. -/

namespace FLatticePaper.ChildGap

open Farey FLatticePaper FLatticePaper.Induction

/-- The odd gap `D_o − N_o` of a parent pair. -/
def dO (p : Parents) : ℤ := p.odd.den - p.odd.num

/-- The even gap `D_e − N_e` of a parent pair. -/
def dE (p : Parents) : ℤ := p.even.den - p.even.num

theorem dO_step_one (p : Parents) : dO (p.step .one) = dO p + dE p := by
  simp only [dO, dE, Parents.step, Parents.current, Parents.combine]
  ring

theorem dE_step_one (p : Parents) : dE (p.step .one) = 2 * dO p + dE p := by
  simp only [dO, dE, Parents.step, Parents.current, Parents.combine]
  ring

theorem dO_step_two (p : Parents) : dO (p.step .two) = dO p + dE p := by
  simp only [dO, dE, Parents.step, Parents.current, Parents.combine]
  ring

theorem dE_step_two (p : Parents) : dE (p.step .two) = dE p := by
  simp only [dO, dE, Parents.step, Parents.current, Parents.combine]

theorem dO_step_three (p : Parents) : dO (p.step .three) = dO p := by
  simp only [dO, Parents.step]

theorem dE_step_three (p : Parents) : dE (p.step .three) = 2 * dO p + dE p := by
  simp only [dO, dE, Parents.step, Parents.current, Parents.combine]
  ring

/-- Along any walk the odd gap stays at least `1` and the even gap stays nonnegative and never decreases. -/
theorem walk_inv : ∀ (w : Word) (p : Parents), 1 ≤ dO p → 0 ≤ dE p →
    1 ≤ dO (p.walk w) ∧ 0 ≤ dE (p.walk w) ∧ dE p ≤ dE (p.walk w)
  | [], _, h1, h2 => ⟨h1, h2, le_refl _⟩
  | x :: w, p, h1, h2 => by
    rw [Parents.walk_cons]
    cases x with
    | one =>
      have := walk_inv w (p.step .one) (by rw [dO_step_one]; omega) (by rw [dE_step_one]; omega)
      refine ⟨this.1, this.2.1, ?_⟩
      have h3 : dE p ≤ dE (p.step .one) := by rw [dE_step_one]; omega
      exact le_trans h3 this.2.2
    | two =>
      have := walk_inv w (p.step .two) (by rw [dO_step_two]; omega) (by rw [dE_step_two]; omega)
      refine ⟨this.1, this.2.1, ?_⟩
      have h3 : dE p ≤ dE (p.step .two) := by rw [dE_step_two]
      exact le_trans h3 this.2.2
    | three =>
      have := walk_inv w (p.step .three) (by rw [dO_step_three]; omega) (by rw [dE_step_three]; omega)
      refine ⟨this.1, this.2.1, ?_⟩
      have h3 : dE p ≤ dE (p.step .three) := by rw [dE_step_three]; omega
      exact le_trans h3 this.2.2

/-- A walk through the digit `two` alone keeps `δ_e = 0` and `δ_o = 1` from the root. -/
theorem walk_two : ∀ (w : Word) (p : Parents), (∀ x ∈ w, x = Digit.two) → dE p = 0 → dO p = 1 →
    dE (p.walk w) = 0 ∧ dO (p.walk w) = 1
  | [], _, _, h1, h2 => ⟨h1, h2⟩
  | x :: w, p, hw, h1, h2 => by
    rw [Parents.walk_cons]
    have hx : x = Digit.two := hw x (List.mem_cons_self)
    subst hx
    have := walk_two w (p.step .two) (fun y hy => hw y (List.mem_cons_of_mem _ hy))
      (by rw [dE_step_two]; exact h1) (by rw [dO_step_two]; omega)
    exact this

/-- After a digit other than `two` the even gap is at least `2`, and it stays so. -/
theorem walk_nontwo : ∀ (w : Word) (p : Parents), 1 ≤ dO p → 0 ≤ dE p → (∃ x ∈ w, x ≠ Digit.two) →
    2 ≤ dE (p.walk w)
  | [], _, _, _, ⟨x, hx, _⟩ => absurd hx (List.not_mem_nil)
  | x :: w, p, h1, h2, hex => by
    rw [Parents.walk_cons]
    cases x with
    | one =>
      have hd : 2 ≤ dE (p.step .one) := by rw [dE_step_one]; omega
      have := walk_inv w (p.step .one) (by rw [dO_step_one]; omega) (by omega)
      omega
    | two =>
      obtain ⟨y, hy, hne⟩ := hex
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd rfl hne
      · have := walk_nontwo w (p.step .two) (by rw [dO_step_two]; omega) (by rw [dE_step_two]; omega)
          ⟨y, hy', hne⟩
        exact this
    | three =>
      have hd : 2 ≤ dE (p.step .three) := by rw [dE_step_three]; omega
      have := walk_inv w (p.step .three) (by rw [dO_step_three]; omega) (by omega)
      omega

/-- The child gap of the frame of a word is `2 δ_o + δ_e` of its parent pair. -/
theorem child_gap_eq (word : Word) :
    (frameAt word).child.den - (frameAt word).child.num = 2 * dO (parentsAt word) + dE (parentsAt word) := by
  simp only [frameAt, ChildFrame.child, dO, dE, Parents.current, Parents.combine]
  ring

theorem root_dO : dO root = 1 := by
  simp only [dO, root]
  norm_num

theorem root_dE : dE root = 0 := by
  simp only [dE, root]
  norm_num

/-- **The child gap of a proper word that is not a two-power is at least `4`.** -/
theorem child_gap_ge_four (word : Word) (hprop : ∃ x ∈ word, x ≠ Digit.three) (hnot : ¬ IsTwoPow word) :
    4 ≤ (frameAt word).child.den - (frameAt word).child.num := by
  have hnt : ∃ x ∈ word, x ≠ Digit.two := by
    by_contra hcon
    apply hnot
    obtain ⟨x0, hx0, -⟩ := hprop
    have hall : ∀ x ∈ word, x = Digit.two := fun x hx => by
      by_contra hne
      exact hcon ⟨x, hx, hne⟩
    refine ⟨word.length - 1, ?_⟩
    rw [Nat.sub_add_cancel (List.length_pos_of_mem hx0)]
    exact List.eq_replicate_iff.mpr ⟨rfl, hall⟩
  have h := walk_inv word root (by rw [root_dO]) (by rw [root_dE])
  have h2 := walk_nontwo word root (by rw [root_dO]) (by rw [root_dE]) hnt
  rw [child_gap_eq]
  unfold parentsAt
  omega

end FLatticePaper.ChildGap
