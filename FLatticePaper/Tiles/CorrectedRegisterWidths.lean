import FLatticePaper.Tiles.CorrectedRegisterFaces
import FLatticePaper.Tiles.CorrectedMixedDiagram

/-! Uniform endpoint bounds for both diagrams, including arbitrary extensions of their flat sides. -/

namespace FLatticePaper.Tiles.CorrectedRegisterWidths

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open CorrectedRegisterDiagram CorrectedRegisterFaces CorrectedMixedDiagram

/-- The widths needed to replace each of the four unbounded tests by its nine central levels. -/
structure Sizes (r : Register) (s : Shape) : Prop where
  horizontal : 2*r.d+r.n ≤ s.a.1
  vertical : 3*r.d+r.n ≤ s.b.2
  slopeH : |s.a.2| ≤ 2
  slopeV : |s.b.1| ≤ 1
  doubleWidth : |s.a.2|=2 → 2*(2*r.d+r.n) ≤ s.a.1
  extraH : 0 ≤ s.extraA.1
  extraV : 0 ≤ s.extraB.2
  alongH : s.extraA.2=0
  alongV : s.extraB.1=0
  flatH : s.a.2 ≠ 0 → s.extraA.1=0
  flatV : s.b.1 ≠ 0 → s.extraB.2=0

private theorem fixed_bounds (r : Register) (hn : 1 ≤ r.n) (hd : r.n < r.d) (par : Bool) (sec : Fin 3) (i : Fin 4) :
    let z := displacement r (bias par sec i);
    -r.d-r.n ≤ z.1 ∧ z.1 ≤ r.d ∧ -r.d-r.n ≤ z.2 ∧ z.2 ≤ 2*r.d := by
  cases par <;> fin_cases sec <;> fin_cases i <;>
    norm_num [bias,displacement,mulI,Fin.ext_iff] <;> omega

private theorem width_bound (W k ext span pad lo hi : ℤ) (hp : 0 ≤ pad) (hs : pad ≤ span)
    (hw : span ≤ W) (hk : |k| ≤ 2) (h₂ : |k|=2 → 2*span ≤ W)
    (he : k≠0 → ext=0) (hl : -span-pad ≤ lo) (hu : hi ≤ W+ext+span+pad) :
    -4*W ≤ |k| *lo ∧ |k| *hi ≤ 4*W := by
  by_cases z : k=0
  · subst k; simp; omega
  have ex := he z
  have sg := abs_pos.mpr z
  rcases (show |k|=1 ∨ |k|=2 by omega) with h|h
  · rw [h]; omega
  · specialize h₂ h
    rw [h]; omega

/-- Fixed parity biases span at most `2*d+n` horizontally and `3*d+n` vertically.
Only a horizontal face of slope two needs a second width of clearance. -/
theorem fits (r : Register) (s : Shape) (hn : 1 ≤ r.n) (hd : r.n < r.d)
    (h : Sizes r s) (par : Bool) (sec : Fin 3) : Fits (s.probe r par sec) := by
  let q := s.probe r par sec
  have f₀ := fixed_bounds r hn hd par sec 0
  have f₁ := fixed_bounds r hn hd par sec 1
  have f₂ := fixed_bounds r hn hd par sec 2
  have f₃ := fixed_bounds r hn hd par sec 3
  obtain ⟨ax,by',ay,bx,doub,ex,ey,alongH,alongV,flatH,flatV⟩ := h
  have sx := abs_le.mp ay
  have sy := abs_le.mp bx
  have vertical (lo hi : ℤ) (hl : -(3*r.d+r.n)-6 ≤ lo) (hu : hi ≤ s.b.2+s.extraB.2+(3*r.d+r.n)+6) :=
    width_bound s.b.2 s.b.1 s.extraB.2 (3*r.d+r.n) 6 lo hi (by decide) (by omega) by'
      (by omega) (by omega) flatV hl hu
  have horizontal (lo hi : ℤ) (hl : -(2*r.d+r.n)-5 ≤ lo) (hu : hi ≤ s.a.1+s.extraA.1+(2*r.d+r.n)+5) :=
    width_bound s.a.1 s.a.2 s.extraA.1 (2*r.d+r.n) 5 lo hi (by decide) (by omega) ax ay doub flatH hl hu
  dsimp only at f₀ f₁ f₂ f₃
  constructor
  · change (q 3).w ≤ (q 2).w+8
    norm_num [q,Shape.probe]; omega
  · change (q 1).w ≤ (q 0).w+8
    norm_num [q,Shape.probe]; omega
  · intro i; fin_cases i <;> norm_num [Shape.probe] <;> omega
  · have four {P : Fin 4 → Prop} (a : P 0) (b : P 1) (c : P 2) (d : P 3) : ∀ i, P i := by
      intro i; fin_cases i <;> assumption
    apply four
    · apply horizontal <;> norm_num [low,high,Shape.probe] <;> omega
    · apply horizontal <;> norm_num [low,high,Shape.probe] <;> omega
    · apply vertical <;> norm_num [low,high,Shape.probe] <;> omega
    · apply vertical <;> norm_num [low,high,Shape.probe] <;> omega

/-- Both the mixed period and its complement exceed the width of the fixed horizontal biases. -/
theorem register_widths {r : Register} {one : Bool} {sec : Fin 3} (h : Regular r one sec) :
    2*r.d+r.n ≤ r.T ∧ 2*r.d+r.n ≤ r.M-r.T := by
  have a := h.oddSize
  have b := h.evenSize
  have c := h.num
  have d := h.den
  cases one <;> simp only [Bool.false_eq_true,if_false,if_true] at a b <;> omega

end FLatticePaper.Tiles.CorrectedRegisterWidths
