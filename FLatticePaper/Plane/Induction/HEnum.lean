import FLatticePaper.Plane.Induction.FreeTraceBox
import FLatticePaper.Plane.Induction.Binary

/-! # One free H point per abscissa (task 118, step (3))

`ChildFrame.freeH` is the bottom boundary of `closedPolygon` with `hSpectrum (tGrade z)`. Its abscissas lie in `[1, d]`
(`FreeTraceBox.freeH_box`). Here:

* `abscissa_core` (integers): two H spectrum values `t₁ = n x − d y₁`, `t₂ = n x − d y₂` at the same abscissa satisfy
  `d (y₂ − y₁) = t₁ − t₂`; with `d` odd, the spectrum bounds force `y₁ = y₂`. No polygon and no floor law is needed.
* `freeH_abscissa_unique`: at most one free H point on each abscissa.
* `freeH_cover`: given existence on each abscissa (named as `hex`, numerically checked on 74 valid child frames), the free H
  trace is `{H j : j < d}` with `H j` the free point of abscissa `j + 1`.

The existence `hex` is NOT proved here (it needs the bottom-boundary analysis of the column). -/

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

end FLatticePaper.Induction
