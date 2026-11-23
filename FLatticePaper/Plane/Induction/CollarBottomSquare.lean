import FLatticePaper.Plane.Induction.CollarBottomCases
import FLatticePaper.Plane.Induction.CollarGlue
import FLatticePaper.Plane.Induction.Binary
import FLatticePaper.Plane.Induction.CollarBottomBand
import FLatticePaper.Plane.Induction.CollarUpper

/-! Task 72 (hcollar, band (a), the bottom class): the four corners of the bottom collar square are strict.

For a bottom centre `c` (a strict centre with a free H witness `v`, `|v − c|∞ ≤ 1`, `c ≠ (1,1)`), the centre band of the
direct cores holds, and the four corners `(c1 − 1, c2)`, `(c1, c2)`, `(c1 − 1, c2 + 1)`, `(c1, c2 + 1)` of
`squareCorners (c1 − 1) c2` are strict, using `T > 3 (d + n)`. -/

namespace FLatticePaper.CollarBottomSquare

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.CollarBottomCases
  FLatticePaper.CollarGlue FLatticePaper.AndOrRank FLatticePaper.CollarBottomBand FLatticePaper.CollarUpper

/-- `T > 3 (d + n)` for a child pair with `1 ≤ n` and `n + 2 ≤ d`. -/
theorem T_gt (n d : ℤ) (hn : 0 < n) (hnd : n + 2 ≤ d) :
    3 * (d + n) < d ^ 2 + 2 * d * n - n ^ 2 := by
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - n - 2 by omega) (show (0 : ℤ) ≤ d + n by omega),
    mul_nonneg (show (0 : ℤ) ≤ d by omega) (show (0 : ℤ) ≤ n - 1 by omega)]

/-- The corners of the bottom square `squareCorners (c.1 − 1) c.2`. -/
theorem mem_bottom_square (c : Site) (x y : ℤ) :
    (x, y) ∈ squareCorners (c.1 - 1) c.2 ↔
      (x = c.1 - 1 ∧ y = c.2) ∨ (x = c.1 ∧ y = c.2) ∨ (x = c.1 - 1 ∧ y = c.2 + 1) ∨
        (x = c.1 ∧ y = c.2 + 1) := by
  simp [squareCorners, Prod.ext_iff]

/-- The four corners of an even centre with the even band. -/
theorem corners_of_even (n d a b : ℤ) (hn : 0 < n) (hnd : n + 2 ≤ d) (hcE : (a + b) % 2 = 0)
    (B1 : 2 * (d + n) - 2 < (d + n) * a + (d - n) * b)
    (B2 : (d + n) * a + (d - n) * b ≤ d ^ 2 + 2 * d * n - n ^ 2 - 2 * d + 2 * n + 1)
    (B3 : 2 - (d + n) ≤ n * a - d * b) (B4 : n * a - d * b ≤ 0) :
    StrictInterior n d (a - 1, b) ∧ StrictInterior n d (a, b) ∧
      StrictInterior n d (a - 1, b + 1) ∧ StrictInterior n d (a, b + 1) := by
  have hT := T_gt n d hn hnd
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [strict_odd_iff n d (a - 1, b) (by unfold EvenSite; dsimp only; omega)]
    dsimp only
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [strict_even_iff n d (a, b) (by unfold EvenSite; dsimp only; omega)]
    dsimp only
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [strict_even_iff n d (a - 1, b + 1) (by unfold EvenSite; dsimp only; omega)]
    dsimp only
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [strict_odd_iff n d (a, b + 1) (by unfold EvenSite; dsimp only; omega)]
    dsimp only
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The four corners of an odd centre with the odd band. -/
theorem corners_of_odd (n d a b : ℤ) (hn : 0 < n) (hnd : n + 2 ≤ d) (hcO : (a + b) % 2 = 1)
    (B1 : d + n + 2 * n < (d + n) * a + (d - n) * b)
    (B2 : (d + n) * a + (d - n) * b ≤ d ^ 2 + 2 * d * n - n ^ 2 - d + n - 1)
    (B3 : -d ≤ n * a - d * b) (B4 : n * a - d * b ≤ n - 2) :
    StrictInterior n d (a - 1, b) ∧ StrictInterior n d (a, b) ∧
      StrictInterior n d (a - 1, b + 1) ∧ StrictInterior n d (a, b + 1) := by
  have hT := T_gt n d hn hnd
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [strict_even_iff n d (a - 1, b) (by unfold EvenSite; dsimp only; omega)]
    dsimp only
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [strict_odd_iff n d (a, b) (by unfold EvenSite; dsimp only; omega)]
    dsimp only
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [strict_odd_iff n d (a - 1, b + 1) (by unfold EvenSite; dsimp only; omega)]
    dsimp only
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [strict_even_iff n d (a, b + 1) (by unfold EvenSite; dsimp only; omega)]
    dsimp only
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The even H points have `t ≥ 2`. -/
theorem even_t_lower (frame : ChildFrame) {v : Site} (hv : EvenSite v)
    (hsp : frame.hSpectrum (frame.tGrade v)) : 2 ≤ frame.child.num * v.1 - frame.child.den * v.2 := by
  obtain ⟨hn, hd⟩ := frame.child_odd
  have hp := t_parity frame.child.num frame.child.den v.1 v.2 hn hd
  unfold ChildFrame.hSpectrum ChildFrame.tGrade at hsp
  unfold EvenSite at hv
  generalize frame.child.num * v.1 - frame.child.den * v.2 = τ at *
  rcases hsp with ⟨h1, h2, -⟩ | ⟨h1, -, -⟩
  · exact h2
  · omega

/-- The odd H points have `t ≥ n`. -/
theorem odd_t_range (frame : ChildFrame) {v : Site} (hv : ¬ EvenSite v)
    (hsp : frame.hSpectrum (frame.tGrade v)) : frame.child.num ≤ frame.child.num * v.1 - frame.child.den * v.2 := by
  obtain ⟨hn, hd⟩ := frame.child_odd
  have hp := t_parity frame.child.num frame.child.den v.1 v.2 hn hd
  unfold ChildFrame.hSpectrum ChildFrame.tGrade at hsp
  unfold EvenSite at hv
  generalize frame.child.num * v.1 - frame.child.den * v.2 = τ at *
  rcases hsp with ⟨h1, -, -⟩ | ⟨-, h2, -⟩
  · omega
  · exact h2

/-- The centre band of an even strict centre with a free H witness within one pixel (not the black corner). -/
theorem band_even_of_witness (frame : ChildFrame) {c : Site}
    (hcS : StrictInterior frame.child.num frame.child.den c) (hcE : EvenSite c) (hne : c ≠ (1, 1))
    {v : Site} (hvA : |v.1 - c.1| ≤ 1) (hvB : |v.2 - c.2| ≤ 1) (hv : v ∈ frame.freeH) :
    2 * (frame.child.den + frame.child.num) - 2 <
        (frame.child.den + frame.child.num) * c.1 + (frame.child.den - frame.child.num) * c.2 ∧
      (frame.child.den + frame.child.num) * c.1 + (frame.child.den - frame.child.num) * c.2 ≤
        frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 -
          2 * frame.child.den + 2 * frame.child.num + 1 ∧
      2 - (frame.child.den + frame.child.num) ≤ frame.child.num * c.1 - frame.child.den * c.2 ∧
      frame.child.num * c.1 - frame.child.den * c.2 ≤ 0 := by
  obtain ⟨hn0, hnd1, hd2, -, -⟩ := frame.child_facts
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  obtain ⟨-, hcu, hcs1, hcs2⟩ := (strict_even_iff _ _ c hcE).mp hcS
  have hcE' : (c.1 + c.2) % 2 = 0 := hcE
  have ha : -1 ≤ c.1 - v.1 ∧ c.1 - v.1 ≤ 1 := by
    obtain ⟨h1, h2⟩ := abs_le.mp hvA
    exact ⟨by omega, by omega⟩
  have hb : -1 ≤ c.2 - v.2 ∧ c.2 - v.2 ≤ 1 := by
    obtain ⟨h1, h2⟩ := abs_le.mp hvB
    exact ⟨by omega, by omega⟩
  have hne' : ¬ (c.1 = 1 ∧ c.2 = 1) := fun h => hne (Prod.ext h.1 h.2)
  obtain ⟨hE, -, hsp⟩ := hv
  have hsv : frame.sGrade v =
      (frame.child.den + frame.child.num) * v.1 + (frame.child.den - frame.child.num) * v.2 := rfl
  by_cases hvE : EvenSite v
  · obtain ⟨l, hvl, hl1, -, hvs⟩ := even_H_bounds frame hvE hE hsp
    obtain ⟨hk1, hk2⟩ := even_H_k_bounds frame hvE hE hsp
    have hpl := even_t_lower frame hvE hsp
    rw [hsv] at hvs
    have hl1' : l = 1 → v.1 = 2 ∧ v.2 = 0 := by
      intro hl
      have h2 := even_H_l1 frame hvE hsp (by omega)
      exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
    have hk2' : v.1 + v.2 = frame.child.den + frame.child.num - 2 →
        v.1 = frame.child.den - 1 ∧ v.2 = frame.child.num - 1 := fun h =>
      ⟨congrArg Prod.fst (hk2 h), congrArg Prod.snd (hk2 h)⟩
    exact even_direct_arith frame.child.num frame.child.den
      (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2)
      v.1 v.2 l c.1 c.2 hn0 hnd hnodd hdodd rfl hcE' hcu hcs2 hvE hpl hvl hl1 hvs hk1 hk2' hl1' ha hb hne'
  · have hvO : (v.1 + v.2) % 2 = 1 := by
      unfold EvenSite at hvE
      omega
    obtain ⟨hk1, hk2⟩ := odd_H_k_bounds frame hvE hE hsp
    have hvt := odd_t_range frame hvE hsp
    have hvc : (v.1 = 1 ∧ v.2 = 0) ∨
        3 * (frame.child.den + frame.child.num) ≤
          (frame.child.den + frame.child.num) * v.1 + (frame.child.den - frame.child.num) * v.2 := by
      rcases odd_H_bounds frame hvE hE hsp with h | h
      · exact Or.inl ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      · exact Or.inr h
    have hk2' : v.1 + v.2 = frame.child.den + frame.child.num - 1 →
        v.1 = frame.child.den ∧ v.2 = frame.child.num - 1 := fun h =>
      ⟨congrArg Prod.fst (hk2 h), congrArg Prod.snd (hk2 h)⟩
    exact even_direct_odd_arith frame.child.num frame.child.den
      (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2)
      v.1 v.2 c.1 c.2 hn0 hnd hnodd hdodd rfl hcE' hcs1 hcu hcs2 hne' hvO hvt hk1 hk2' hvc ha hb

/-- The centre band of an odd strict centre with a free H witness within one pixel. -/
theorem band_odd_of_witness (frame : ChildFrame) {c : Site}
    (hcS : StrictInterior frame.child.num frame.child.den c) (hcO : ¬ EvenSite c)
    {v : Site} (hvA : |v.1 - c.1| ≤ 1) (hvB : |v.2 - c.2| ≤ 1) (hv : v ∈ frame.freeH) :
    frame.child.den + frame.child.num + 2 * frame.child.num <
        (frame.child.den + frame.child.num) * c.1 + (frame.child.den - frame.child.num) * c.2 ∧
      (frame.child.den + frame.child.num) * c.1 + (frame.child.den - frame.child.num) * c.2 ≤
        frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 -
          frame.child.den + frame.child.num - 1 ∧
      -frame.child.den ≤ frame.child.num * c.1 - frame.child.den * c.2 ∧
      frame.child.num * c.1 - frame.child.den * c.2 ≤ frame.child.num - 2 := by
  obtain ⟨hn0, hnd1, hd2, -, -⟩ := frame.child_facts
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  obtain ⟨hcl, hcu, hcs1, hcs2⟩ := (strict_odd_iff _ _ c hcO).mp hcS
  have hcO' : (c.1 + c.2) % 2 = 1 := by
    unfold EvenSite at hcO
    omega
  have ha : -1 ≤ c.1 - v.1 ∧ c.1 - v.1 ≤ 1 := by
    obtain ⟨h1, h2⟩ := abs_le.mp hvA
    exact ⟨by omega, by omega⟩
  have hb : -1 ≤ c.2 - v.2 ∧ c.2 - v.2 ≤ 1 := by
    obtain ⟨h1, h2⟩ := abs_le.mp hvB
    exact ⟨by omega, by omega⟩
  obtain ⟨hE, -, hsp⟩ := hv
  have hsv : frame.sGrade v =
      (frame.child.den + frame.child.num) * v.1 + (frame.child.den - frame.child.num) * v.2 := rfl
  by_cases hvE : EvenSite v
  · obtain ⟨l, hvl, hl1, -, hvs⟩ := even_H_bounds frame hvE hE hsp
    obtain ⟨hk1, hk2⟩ := even_H_k_bounds frame hvE hE hsp
    have hpl := even_t_lower frame hvE hsp
    rw [hsv] at hvs
    have hl1' : l = 1 → v.1 = 2 ∧ v.2 = 0 := by
      intro hl
      have h2 := even_H_l1 frame hvE hsp (by omega)
      exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
    exact odd_direct_even_arith frame.child.num frame.child.den
      (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2)
      v.1 v.2 l c.1 c.2 hn0 hnd hnodd hdodd rfl hcO' hcl hcu hcs1 (by linarith) hvE hpl hvl hl1 hvs hk1 hl1' ha hb
  · have hvO : (v.1 + v.2) % 2 = 1 := by
      unfold EvenSite at hvE
      omega
    obtain ⟨hk1, hk2⟩ := odd_H_k_bounds frame hvE hE hsp
    have hvt := odd_t_range frame hvE hsp
    have hvc : (v.1 = 1 ∧ v.2 = 0) ∨ (v.1 = 3 ∧ v.2 = 0) ∨
        3 * (frame.child.den + frame.child.num) <
          (frame.child.den + frame.child.num) * v.1 + (frame.child.den - frame.child.num) * v.2 := by
      rcases odd_H_cases frame hvE hE hsp with h | h | h
      · exact Or.inl ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      · exact Or.inr (Or.inl ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩)
      · exact Or.inr (Or.inr h)
    have hk2' : v.1 + v.2 = frame.child.den + frame.child.num - 1 →
        v.1 = frame.child.den ∧ v.2 = frame.child.num - 1 := fun h =>
      ⟨congrArg Prod.fst (hk2 h), congrArg Prod.snd (hk2 h)⟩
    exact odd_direct_odd_arith frame.child.num frame.child.den
      (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2)
      v.1 v.2 c.1 c.2 hn0 hnd hnodd hdodd rfl hcO' hcu hcs1 (by linarith) hvO hvt hk1 hk2' hvc ha hb

/-- **The bottom class.** A strict bottom centre `c ≠ (1, 1)` has its whole collar square `squareCorners (c.1 − 1) c.2`
strict. -/
theorem bottom_square_strict (frame : ChildFrame) {c : Site}
    (hcS : StrictInterior frame.child.num frame.child.den c) (hne : c ≠ (1, 1)) (hB : BottomArc frame c) :
    ∀ c' ∈ squareCorners (c.1 - 1) c.2, StrictInterior frame.child.num frame.child.den c' := by
  obtain ⟨v, hvA, hvB, hv⟩ := hB
  obtain ⟨hn0, hnd1, hd2, -, -⟩ := frame.child_facts
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  intro c' hc'
  obtain ⟨x, y⟩ := c'
  by_cases hcE : EvenSite c
  · obtain ⟨B1, B2, B3, B4⟩ := band_even_of_witness frame hcS hcE hne hvA hvB hv
    obtain ⟨C1, C2, C3, C4⟩ :=
      corners_of_even frame.child.num frame.child.den c.1 c.2 hn0 hnd hcE B1 B2 B3 B4
    rcases (mem_bottom_square c x y).mp hc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact C1
    · exact C2
    · exact C3
    · exact C4
  · have hcO' : (c.1 + c.2) % 2 = 1 := by
      unfold EvenSite at hcE
      omega
    obtain ⟨B1, B2, B3, B4⟩ := band_odd_of_witness frame hcS hcE hvA hvB hv
    obtain ⟨C1, C2, C3, C4⟩ :=
      corners_of_odd frame.child.num frame.child.den c.1 c.2 hn0 hnd hcO' B1 B2 B3 B4
    rcases (mem_bottom_square c x y).mp hc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact C1
    · exact C2
    · exact C3
    · exact C4

end FLatticePaper.CollarBottomSquare
