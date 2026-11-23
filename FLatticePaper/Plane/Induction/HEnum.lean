import FLatticePaper.Plane.Induction.FreeTraceBox
import FLatticePaper.Plane.Induction.Binary

/-! # One free H point per abscissa (task 118, step (3))

`ChildFrame.freeH` is the bottom boundary of `closedPolygon` with `hSpectrum (tGrade z)`. Its abscissas lie in `[1, d]`
(`FreeTraceBox.freeH_box`). Here:

* `abscissa_core` (integers): two H spectrum values `t₁ = n x − d y₁`, `t₂ = n x − d y₂` at the same abscissa satisfy
  `d (y₂ − y₁) = t₁ − t₂`; with `d` odd, the spectrum bounds force `y₁ = y₂`. No polygon and no floor law is needed.
* `freeH_abscissa_unique`: at most one free H point on each abscissa.
* `freeH_cover`: given existence on each abscissa, the free H trace is `{H j : j < d}` with `H j` the free point of abscissa `j + 1`.
* `residue_spectrum`, `freeH_exists`: existence. The H spectrum meets every residue class mod `d` (the representative in the window
  `[n, n + d − 1]`, moved down by `d` when it is odd and above `d`); for `t` in the spectrum with `n x − t = d y`, the closed polygon
  bounds of `(x, y)` follow from `d·s = T x − (d − n) t`, and `(x, y − 1)` is outside by its `t`-grade `t + d`.
* `freeH_enumeration`: the unconditional enumeration of the free H trace.

-/

namespace FLatticePaper.Induction

/-- **The integer core.** With `d` odd and `0 < n < d`, two H spectrum values at the same abscissa force the ordinate difference to
vanish: `d·m = t₁ − t₂` with `t` in `[2, d+n−2]` even or in `[n, d]` odd. -/
theorem abscissa_core (n d m t₁ t₂ : ℤ) (hn : 0 < n) (hnd : n < d) (hd : d % 2 = 1) (hm : d * m = t₁ - t₂)
    (hs₁ : (t₁ % 2 = 0 ∧ 2 ≤ t₁ ∧ t₁ ≤ d + n - 2) ∨ (t₁ % 2 = 1 ∧ n ≤ t₁ ∧ t₁ ≤ d))
    (hs₂ : (t₂ % 2 = 0 ∧ 2 ≤ t₂ ∧ t₂ ≤ d + n - 2) ∨ (t₂ % 2 = 1 ∧ n ≤ t₂ ∧ t₂ ≤ d)) :
    m = 0 := by
  have hdpos : 0 < d := by omega
  -- uniform bounds: every spectrum value lies in [1, d + n − 1]
  have hu₁ : 1 ≤ t₁ ∧ t₁ ≤ d + n - 1 := by
    rcases hs₁ with ⟨-, a, b⟩ | ⟨-, a, b⟩ <;> constructor <;> omega
  have hu₂ : 1 ≤ t₂ ∧ t₂ ≤ d + n - 1 := by
    rcases hs₂ with ⟨-, a, b⟩ | ⟨-, a, b⟩ <;> constructor <;> omega
  by_contra hne
  rcases (show m % 2 = 0 ∨ m % 2 = 1 by omega) with hme | hmo
  · -- m even and nonzero: |m| ≥ 2, so |d m| ≥ 2d, but |t₁ − t₂| ≤ d + n − 2 < 2d
    rcases (show 2 ≤ m ∨ m ≤ -2 by omega) with h | h
    · have hdm : 2 * d ≤ d * m := by nlinarith
      linarith [hu₁.1, hu₁.2, hu₂.1, hu₂.2]
    · have hdm : d * m ≤ -(2 * d) := by nlinarith
      linarith [hu₁.1, hu₁.2, hu₂.1, hu₂.2]
  · -- m odd: t₁ − t₂ = d m is odd, so the two spectra are of opposite parity (mixed), and |t₁ − t₂| ≤ d − 2 < d ≤ |d m|
    have hodd : (t₁ - t₂) % 2 = 1 := by
      rw [← hm, Int.mul_emod, hd, hmo]
      norm_num
    rcases (show 1 ≤ m ∨ m ≤ -1 by omega) with h | h
    · have hdm : d ≤ d * m := by nlinarith
      rcases hs₁ with ⟨e₁, a₁, b₁⟩ | ⟨o₁, a₁, b₁⟩ <;> rcases hs₂ with ⟨e₂, a₂, b₂⟩ | ⟨o₂, a₂, b₂⟩ <;>
        omega
    · have hdm : d * m ≤ -d := by nlinarith
      rcases hs₁ with ⟨e₁, a₁, b₁⟩ | ⟨o₁, a₁, b₁⟩ <;> rcases hs₂ with ⟨e₂, a₂, b₂⟩ | ⟨o₂, a₂, b₂⟩ <;>
        omega

/-- **At most one free H point per abscissa.** -/
theorem freeH_abscissa_unique (frame : ChildFrame) {x y₁ y₂ : ℤ}
    (h₁ : (x, y₁) ∈ frame.freeH) (h₂ : (x, y₂) ∈ frame.freeH) : y₁ = y₂ := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  obtain ⟨-, hdodd⟩ := frame.child_odd
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at h₁ h₂
  have hs₁ := h₁.2.2
  have hs₂ := h₂.2.2
  simp only [ChildFrame.hSpectrum, ChildFrame.tGrade] at hs₁ hs₂
  have hm : frame.child.den * (y₂ - y₁) =
      (frame.child.num * x - frame.child.den * y₁) - (frame.child.num * x - frame.child.den * y₂) := by
    ring
  have h0 := abscissa_core frame.child.num frame.child.den (y₂ - y₁) _ _ hn0 hnd hdodd hm hs₁ hs₂
  omega

/-- **The enumeration of the free H trace.** If each abscissa `1 ≤ x ≤ d` carries a free H point (`hex`, the existence part,
numerically checked on the valid child frames), there is `H : ℕ → Site` with `H j` the free point of abscissa `j + 1`, and every free
H point is some `H j` with `j < d`. -/
theorem freeH_cover (frame : ChildFrame)
    (hex : ∀ x : ℤ, 1 ≤ x → x ≤ frame.child.den → ∃ y : ℤ, (x, y) ∈ frame.freeH) :
    ∃ H : ℕ → Site, (∀ j : ℕ, (j : ℤ) < frame.child.den → H j ∈ frame.freeH ∧ (H j).1 = (j : ℤ) + 1) ∧
      ∀ z ∈ frame.freeH, ∃ j : ℕ, (j : ℤ) < frame.child.den ∧ z = H j := by
  have key : ∀ j : ℕ, ∃ p : Site, ((j : ℤ) < frame.child.den → p ∈ frame.freeH ∧ p.1 = (j : ℤ) + 1) := by
    intro j
    by_cases hj : (j : ℤ) < frame.child.den
    · obtain ⟨y, hy⟩ := hex ((j : ℤ) + 1) (by omega) (by omega)
      exact ⟨((j : ℤ) + 1, y), fun _ => ⟨hy, rfl⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hj⟩
  choose H hH using key
  refine ⟨H, fun j hj => hH j hj, ?_⟩
  intro z hz
  obtain ⟨x, y⟩ := z
  obtain ⟨hx1, hxd, -, -⟩ := FLatticePaper.Induction.FreeTraceBox.freeH_box frame hz
  have hx1' : 1 ≤ x := hx1
  have hxd' : x ≤ frame.child.den := hxd
  have hxa : (0 : ℤ) ≤ x - 1 := by omega
  have hjx : (((x - 1).toNat : ℕ) : ℤ) = x - 1 := Int.toNat_of_nonneg hxa
  obtain ⟨hmem, hfst⟩ := hH (x - 1).toNat (by omega)
  have hfst' : (H (x - 1).toNat).1 = x := by omega
  have hyb : (x, (H (x - 1).toNat).2) ∈ frame.freeH := by
    have e : (x, (H (x - 1).toNat).2) = H (x - 1).toNat := Prod.ext hfst'.symm rfl
    rw [e]
    exact hmem
  have hy : y = (H (x - 1).toNat).2 := freeH_abscissa_unique frame hz hyb
  exact ⟨(x - 1).toNat, by omega, Prod.ext hfst'.symm hy⟩

/-- **Residues of the H spectrum.** For odd `n < d` with `d` odd, every integer `r` is congruent mod `d` to a spectrum value:
there are `t` in the H spectrum and `k` with `r − t = d k`. -/
theorem residue_spectrum (n d r : ℤ) (hn : 0 < n) (hnd : n < d) (hdo : d % 2 = 1) (hno : n % 2 = 1) :
    ∃ t k : ℤ, r - t = d * k ∧
      ((t % 2 = 0 ∧ 2 ≤ t ∧ t ≤ d + n - 2) ∨ (t % 2 = 1 ∧ n ≤ t ∧ t ≤ d)) := by
  have hd0 : 0 < d := by omega
  obtain ⟨t0, k0, hdiv, hlo, hhi⟩ : ∃ t0 k0 : ℤ, r - t0 = d * k0 ∧ n ≤ t0 ∧ t0 ≤ n + d - 1 := by
    refine ⟨n + (r - n) % d, (r - n) / d, ?_, ?_, ?_⟩
    · have h := Int.emod_def (r - n) d
      linarith
    · have h := Int.emod_nonneg (r - n) hd0.ne'
      linarith
    · have h : (r - n) % d < d := Int.emod_lt_of_pos (r - n) hd0
      have h' : (r - n) % d + 1 ≤ d := Int.lt_iff_add_one_le.mp h
      linarith
  rcases Int.emod_two_eq_zero_or_one t0 with he | ho
  · exact ⟨t0, k0, hdiv, Or.inl ⟨he, by omega, by omega⟩⟩
  · by_cases hd' : t0 ≤ d
    · exact ⟨t0, k0, hdiv, Or.inr ⟨ho, hlo, hd'⟩⟩
    · refine ⟨t0 - d, k0 + 1, ?_, Or.inl ⟨by omega, by omega, by omega⟩⟩
      rw [mul_add, mul_one]
      linarith

/-- **Existence on each abscissa.** For `1 ≤ x ≤ d` the free H trace has a point on the abscissa `x`. -/
theorem freeH_exists (frame : ChildFrame) {x : ℤ} (hx1 : 1 ≤ x) (hxd : x ≤ frame.child.den) :
    ∃ y : ℤ, (x, y) ∈ frame.freeH := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  obtain ⟨hno, hdo⟩ := frame.child_odd
  obtain ⟨t, k, hdiv, hs⟩ :=
    residue_spectrum frame.child.num frame.child.den (frame.child.num * x) hn0 hnd hdo hno
  have htk : t = frame.child.num * x - frame.child.den * k := by linarith
  have htg : frame.tGrade (x, k) = t := by
    unfold ChildFrame.tGrade
    simp only
    rw [htk]
  have htgpar : t % 2 = (x + k) % 2 := by
    have h := FLatticePaper.Induction.tGrade_parity frame (x, k)
    rw [htg] at h
    exact h
  -- d · s = T x − (d − n) t, with s = sGrade (x, k)
  have hs_id : frame.child.den * frame.sGrade (x, k) =
      frame.child.periodDenominator * x - (frame.child.den - frame.child.num) * t := by
    unfold ChildFrame.sGrade
    simp only
    rw [hT, htk]
    ring
  have hTpos : 0 < frame.child.periodDenominator := by
    rw [hT]
    nlinarith [mul_pos hn0 (show (0 : ℤ) < frame.child.den by omega)]
  have hd0 : 0 < frame.child.den := by omega
  have hdn : 0 < frame.child.den - frame.child.num := by omega
  -- the s-bounds of the even branch
  have sE : 2 ≤ t → t ≤ frame.child.den + frame.child.num - 2 →
      0 ≤ frame.sGrade (x, k) ∧ frame.sGrade (x, k) ≤ frame.child.periodDenominator + 2 * frame.child.num := by
    intro ta tb
    constructor
    · by_contra hc
      have h1 : frame.sGrade (x, k) ≤ -1 := by omega
      have h2 := mul_le_mul_of_nonneg_left h1 hd0.le
      have h3 : frame.child.periodDenominator * 1 ≤ frame.child.periodDenominator * x :=
        mul_le_mul_of_nonneg_left hx1 hTpos.le
      have h4 : (frame.child.den - frame.child.num) * t ≤
          (frame.child.den - frame.child.num) * (frame.child.den + frame.child.num - 2) :=
        mul_le_mul_of_nonneg_left tb hdn.le
      have h5 : 0 ≤ frame.child.num * (frame.child.den - 1) := mul_nonneg hn0.le (by omega)
      nlinarith
    · by_contra hc
      have h1 : frame.child.periodDenominator + 2 * frame.child.num + 1 ≤ frame.sGrade (x, k) := by omega
      have h2 := mul_le_mul_of_nonneg_left h1 hd0.le
      have h3 : frame.child.periodDenominator * x ≤ frame.child.periodDenominator * frame.child.den :=
        mul_le_mul_of_nonneg_left hxd hTpos.le
      have h4 : 0 ≤ (frame.child.den - frame.child.num) * t := mul_nonneg hdn.le (by omega)
      have h5 : 0 ≤ frame.child.den * frame.child.num := mul_nonneg hd0.le hn0.le
      nlinarith
  -- the s-bounds of the odd branch
  have sO : frame.child.num ≤ t → t ≤ frame.child.den →
      2 - frame.child.den + frame.child.num ≤ frame.sGrade (x, k) ∧
        frame.sGrade (x, k) ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2 := by
    intro tn td
    constructor
    · by_contra hc
      have h1 : frame.sGrade (x, k) ≤ 1 - frame.child.den + frame.child.num := by omega
      have h2 := mul_le_mul_of_nonneg_left h1 hd0.le
      have h3 : frame.child.periodDenominator * 1 ≤ frame.child.periodDenominator * x :=
        mul_le_mul_of_nonneg_left hx1 hTpos.le
      have h4 : (frame.child.den - frame.child.num) * t ≤ (frame.child.den - frame.child.num) * frame.child.den :=
        mul_le_mul_of_nonneg_left td hdn.le
      have h6 : frame.child.num * frame.child.num ≤ (frame.child.den - 2) * (frame.child.den - 2) :=
        mul_le_mul (by omega) (by omega) (by omega) (by omega)
      have h7 : frame.child.den * 1 ≤ frame.child.den * frame.child.num :=
        mul_le_mul_of_nonneg_left (by omega) hd0.le
      nlinarith
    · by_contra hc
      have h1 : frame.child.periodDenominator + frame.child.den + frame.child.num - 1 ≤ frame.sGrade (x, k) := by omega
      have h2 := mul_le_mul_of_nonneg_left h1 hd0.le
      have h3 : frame.child.periodDenominator * x ≤ frame.child.periodDenominator * frame.child.den :=
        mul_le_mul_of_nonneg_left hxd hTpos.le
      have h4 : 0 ≤ (frame.child.den - frame.child.num) * t := mul_nonneg hdn.le (by omega)
      have h5 : frame.child.den ≤ frame.child.den * frame.child.den :=
        le_mul_of_one_le_right hd0.le (by omega)
      have h6 : 0 ≤ frame.child.den * frame.child.num := mul_nonneg hd0.le hn0.le
      nlinarith
  -- the point (x, k) lies in the closed polygon
  have hcp : (x, k) ∈ frame.closedPolygon := by
    rw [FLatticePaper.Induction.mem_closedPolygon_iff]
    rcases hs with ⟨te, ta, tb⟩ | ⟨tod, tc, td⟩
    · have hev : EvenSite (x, k) := by
        show (x + k) % 2 = 0
        omega
      rw [if_pos hev, htg]
      obtain ⟨s1, s2⟩ := sE ta tb
      exact ⟨by omega, by omega, s1, s2⟩
    · have hod : ¬ EvenSite (x, k) := by
        show ¬ (x + k) % 2 = 0
        omega
      rw [if_neg hod, htg]
      obtain ⟨s1, s2⟩ := sO tc td
      exact ⟨by omega, td, s1, s2⟩
  -- the point below, (x, k − 1), is outside the closed polygon: its t-grade is t + d
  have hbd : (x, k - 1) ∉ frame.closedPolygon := by
    intro hmem
    rw [FLatticePaper.Induction.mem_closedPolygon_iff] at hmem
    have htg2 : frame.tGrade (x, k - 1) = t + frame.child.den := by
      unfold ChildFrame.tGrade
      simp only
      rw [htk]
      ring
    have hp2 := FLatticePaper.Induction.tGrade_parity frame (x, k - 1)
    rw [htg2] at hp2
    by_cases hev2 : EvenSite (x, k - 1)
    · rw [if_pos hev2, htg2] at hmem
      have hev2' : (x + (k - 1)) % 2 = 0 := hev2
      rcases hs with ⟨te, ta, tb⟩ | ⟨tod, tc, td⟩
      · omega
      · omega
    · rw [if_neg hev2, htg2] at hmem
      have hev2' : ¬ (x + (k - 1)) % 2 = 0 := hev2
      rcases hs with ⟨te, ta, tb⟩ | ⟨tod, tc, td⟩
      · omega
      · omega
  exact ⟨k, ⟨hcp, hbd, by rw [htg]; unfold ChildFrame.hSpectrum; exact hs⟩⟩

/-- **The free H trace, unconditionally.** For the child frame, the free H points are exactly `H j`, `j < d`, with `H j` on the
abscissa `j + 1` (uniqueness and existence on every abscissa). -/
theorem freeH_enumeration (frame : ChildFrame) :
    ∃ H : ℕ → Site, (∀ j : ℕ, (j : ℤ) < frame.child.den → H j ∈ frame.freeH ∧ (H j).1 = (j : ℤ) + 1) ∧
      ∀ z ∈ frame.freeH, ∃ j : ℕ, (j : ℤ) < frame.child.den ∧ z = H j :=
  freeH_cover frame (fun _x h1 h2 => freeH_exists frame h1 h2)

end FLatticePaper.Induction
