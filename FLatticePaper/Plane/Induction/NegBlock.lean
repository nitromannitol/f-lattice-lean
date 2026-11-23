import FLatticePaper.Plane.Induction.NoBlackPair
import FLatticePaper.Plane.Induction.Q3White

/-! Task 72 (hNegTie, case (b): the V block for the negative slip `−σ`).

For a rising pair with slip `−σ` (its black translate is `c + (−σ)`), the child kernel `U_c` gives the black pair:
for `ε = +1`, `c − σ = (c + U_q) − U_c`, so the pair is `{c, c + U_q}`; for `ε = −1`, `c − σ = (c − U_q) + U_c`, so the pair is
`{c − U_q, c}`. These are the mirror of `BlockPairAt` (whose base is `c − U_q` for `ε = +1` and `c` for `ε = −1`).
`not_rising_of_blockPairNeg` is the mirror of `not_rising_of_blockPair`: the V-block pair cannot be a black pair. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

namespace ChildFrame

variable (frame : ChildFrame)

/-- The mirror V-block pair for the slip `−σ`: the base is `c` (`ε = +1`) or `c − U_q` (`ε = −1`). -/
def BlockPairNeg (c : Site) : Prop :=
  (frame.eps = 1 ∧ ∃ (v : Site) (k : ℤ), v ∈ frame.freeV ∧
      c = v + (k * (2 * frame.parents.odd.den), k * (2 * frame.parents.odd.num)) ∧
      c ∈ frame.closedPolygon ∧ c + (frame.parents.even.den, frame.parents.even.num) ∈ frame.closedPolygon) ∨
  (frame.eps = -1 ∧ ∃ (v : Site) (k : ℤ), v ∈ frame.freeV ∧
      c - (frame.parents.even.den, frame.parents.even.num) =
        v + (k * (2 * frame.parents.odd.den), k * (2 * frame.parents.odd.num)) ∧
      c - (frame.parents.even.den, frame.parents.even.num) ∈ frame.closedPolygon ∧
      c ∈ frame.closedPolygon)

/-- The black translate under the slip `−σ` (`ε = +1`): `c + (−σ) = (c + U_q) − U_c`. -/
theorem laplacian_negShift_eq_of_eps_one {F : Field} (hP : frame.Packet F) (he : frame.eps = 1) (c : Site) :
    laplacian F (c + -frame.shortShift) = laplacian F (c + (frame.parents.even.den, frame.parents.even.num)) := by
  obtain ⟨hd, hn, -⟩ := frame.linear_facts
  have e : c + -frame.shortShift =
      (c + (frame.parents.even.den, frame.parents.even.num)) - (frame.child.den, frame.child.num) := by
    unfold ChildFrame.shortShift
    rw [he]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg] <;> omega
  rw [e, frame.laplacian_sub_child_kernel hP]

/-- The black translate under the slip `−σ` (`ε = −1`): `c + (−σ) = (c − U_q) + U_c`. -/
theorem laplacian_negShift_eq_of_eps_neg_one {F : Field} (hP : frame.Packet F) (he : frame.eps = -1) (c : Site) :
    laplacian F (c + -frame.shortShift) = laplacian F (c - (frame.parents.even.den, frame.parents.even.num)) := by
  obtain ⟨hd, hn, -⟩ := frame.linear_facts
  have e : c + -frame.shortShift =
      (c - (frame.parents.even.den, frame.parents.even.num)) + (frame.child.den, frame.child.num) := by
    unfold ChildFrame.shortShift
    rw [he]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg] <;> omega
  rw [e, frame.laplacian_add_child_kernel hP]

/-- **The mirror of `not_rising_of_blockPair`.** A V-block pair (for the slip `−σ`) is not a black pair with black
translate `c + (−σ)`. -/
theorem not_rising_of_blockPairNeg {F : Field} (hP : frame.Packet F) {c : Site}
    (hb : laplacian F c = -1) (hbs : laplacian F (c + -frame.shortShift) = -1) (hblk : frame.BlockPairNeg c) :
    False := by
  rcases hblk with ⟨he, v, k, hv, hx, hxE, hxuE⟩ | ⟨he, v, k, hv, hx, hxE, hcE⟩
  · have h1 := frame.laplacian_negShift_eq_of_eps_one hP he c
    have hbu : laplacian F (c + (frame.parents.even.den, frame.parents.even.num)) = -1 := by
      rw [← h1]
      exact hbs
    exact frame.black_centres_contradiction hP hv hx hxE hxuE hb hbu
  · have h1 := frame.laplacian_negShift_eq_of_eps_neg_one hP he c
    have hb' : laplacian F (c - (frame.parents.even.den, frame.parents.even.num)) = -1 := by
      rw [← h1]
      exact hbs
    have hbu : laplacian F (c - (frame.parents.even.den, frame.parents.even.num) +
        (frame.parents.even.den, frame.parents.even.num)) = -1 := by
      rw [sub_add_cancel]
      exact hb
    exact frame.black_centres_contradiction hP hv hx hxE (by rw [sub_add_cancel]; exact hcE) hb' hbu

end ChildFrame

end FLatticePaper.Induction
