import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import FLatticePaper.Graph

/-! The maximum principle on the incoming graph of the plane (global_recurrence.tex, the periodic harmonic difference).

A real function `E` with `E(in₋ x) + E(in₊ x) = 2 E x` (harmonic) and invariant under `N·ℤ²` is constant. The incoming
neighbours of a site are its two horizontal (even site) or vertical (odd site) neighbours, so they have the other parity,
and a maximizer forces both of them to be maximizers. Diagonal steps therefore keep the maximizers, and they reach every
site of the parity class of a maximizer. -/

namespace FLatticePaper.HarmonicConstant

theorem incomingNeg_even {x : Site} (h : EvenSite x) : incomingNeg x = (x.1 - 1, x.2) := by
  unfold incomingNeg; rw [if_pos h]

theorem incomingPos_even {x : Site} (h : EvenSite x) : incomingPos x = (x.1 + 1, x.2) := by
  unfold incomingPos; rw [if_pos h]

theorem incomingNeg_odd {x : Site} (h : ¬ EvenSite x) : incomingNeg x = (x.1, x.2 - 1) := by
  unfold incomingNeg; rw [if_neg h]

theorem incomingPos_odd {x : Site} (h : ¬ EvenSite x) : incomingPos x = (x.1, x.2 + 1) := by
  unfold incomingPos; rw [if_neg h]

/-- The incoming neighbours of a site have the other parity. -/
theorem incomingPos_parity (x : Site) :
    ((incomingPos x).1 + (incomingPos x).2) % 2 ≠ (x.1 + x.2) % 2 := by
  by_cases h : EvenSite x
  · rw [incomingPos_even h]
    unfold EvenSite at h
    dsimp only
    omega
  · rw [incomingPos_odd h]
    unfold EvenSite at h
    dsimp only
    omega

/-- Closure of the maximizers under the two incoming neighbours. -/
theorem closed_step {E : Site → ℝ} {M : ℝ} (hharm : ∀ x, E (incomingNeg x) + E (incomingPos x) = 2 * E x)
    (hle : ∀ x, E x ≤ M) {x : Site} (hx : E x = M) :
    E (incomingNeg x) = M ∧ E (incomingPos x) = M := by
  have h1 := hle (incomingNeg x)
  have h2 := hle (incomingPos x)
  have h3 := hharm x
  constructor <;> linarith

/-- The four diagonal neighbours of a maximizer are maximizers. -/
theorem diag_four {E : Site → ℝ} {M : ℝ} (hharm : ∀ x, E (incomingNeg x) + E (incomingPos x) = 2 * E x)
    (hle : ∀ x, E x ≤ M) {x : Site} (hx : E x = M) :
    E (x.1 + 1, x.2 + 1) = M ∧ E (x.1 + 1, x.2 - 1) = M ∧ E (x.1 - 1, x.2 + 1) = M ∧
      E (x.1 - 1, x.2 - 1) = M := by
  by_cases h : EvenSite x
  · obtain ⟨hn, hp⟩ := closed_step hharm hle hx
    rw [incomingNeg_even h] at hn
    rw [incomingPos_even h] at hp
    have hpo : ¬ EvenSite (x.1 + 1, x.2) := by
      unfold EvenSite at h ⊢; dsimp only; omega
    have hno : ¬ EvenSite (x.1 - 1, x.2) := by
      unfold EvenSite at h ⊢; dsimp only; omega
    obtain ⟨p1, p2⟩ := closed_step hharm hle hp
    obtain ⟨q1, q2⟩ := closed_step hharm hle hn
    rw [incomingNeg_odd hpo] at p1
    rw [incomingPos_odd hpo] at p2
    rw [incomingNeg_odd hno] at q1
    rw [incomingPos_odd hno] at q2
    exact ⟨p2, p1, q2, q1⟩
  · obtain ⟨hn, hp⟩ := closed_step hharm hle hx
    rw [incomingNeg_odd h] at hn
    rw [incomingPos_odd h] at hp
    have hne : EvenSite (x.1, x.2 - 1) := by
      unfold EvenSite at h ⊢; dsimp only; omega
    have hpe : EvenSite (x.1, x.2 + 1) := by
      unfold EvenSite at h ⊢; dsimp only; omega
    obtain ⟨a1, a2⟩ := closed_step hharm hle hn
    obtain ⟨b1, b2⟩ := closed_step hharm hle hp
    rw [incomingNeg_even hne] at a1
    rw [incomingPos_even hne] at a2
    rw [incomingNeg_even hpe] at b1
    rw [incomingPos_even hpe] at b2
    exact ⟨b2, a2, b1, a1⟩

/-- Maximizers are closed under the diagonal translations `(±1, ±1)`, hence under `(u, u)`. -/
theorem diagonal_up {E : Site → ℝ} {M : ℝ} (hharm : ∀ x, E (incomingNeg x) + E (incomingPos x) = 2 * E x)
    (hle : ∀ x, E x ≤ M) {y : Site} (hy : E y = M) : ∀ u : ℤ, E (y.1 + u, y.2 + u) = M := by
  intro u
  induction u using Int.induction_on with
  | zero => simpa using hy
  | succ n ih =>
    have h := (diag_four hharm hle ih).1
    have e : (y.1 + (n + 1), y.2 + (n + 1)) = ((y.1 + n) + 1, (y.2 + n) + 1) := Prod.ext (by ring) (by ring)
    rw [e]
    exact h
  | pred n ih =>
    have h := (diag_four hharm hle ih).2.2.2
    have e : (y.1 + (-n - 1), y.2 + (-n - 1)) = ((y.1 + -n) - 1, (y.2 + -n) - 1) := Prod.ext (by ring) (by ring)
    rw [e]
    exact h

/-- Maximizers are closed under the anti-diagonal translations `(v, -v)`. -/
theorem diagonal_down {E : Site → ℝ} {M : ℝ} (hharm : ∀ x, E (incomingNeg x) + E (incomingPos x) = 2 * E x)
    (hle : ∀ x, E x ≤ M) {y : Site} (hy : E y = M) : ∀ v : ℤ, E (y.1 + v, y.2 - v) = M := by
  intro v
  induction v using Int.induction_on with
  | zero => simpa using hy
  | succ n ih =>
    have h := (diag_four hharm hle ih).2.1
    have e : (y.1 + (n + 1), y.2 - (n + 1)) = ((y.1 + n) + 1, (y.2 - n) - 1) := Prod.ext (by ring) (by ring)
    rw [e]
    exact h
  | pred n ih =>
    have h := (diag_four hharm hle ih).2.2.1
    have e : (y.1 + (-n - 1), y.2 - (-n - 1)) = ((y.1 + -n) - 1, (y.2 - -n) + 1) := Prod.ext (by ring) (by ring)
    rw [e]
    exact h

/-- Every site of the parity class of a maximizer is a maximizer. -/
theorem diagonal_const {E : Site → ℝ} {M : ℝ} (hharm : ∀ x, E (incomingNeg x) + E (incomingPos x) = 2 * E x)
    (hle : ∀ x, E x ≤ M) {y : Site} (hy : E y = M) (z : Site)
    (hz : (z.1 + z.2) % 2 = (y.1 + y.2) % 2) : E z = M := by
  obtain ⟨u, hu⟩ : ∃ u : ℤ, (z.1 - y.1) + (z.2 - y.2) = 2 * u := ⟨((z.1 - y.1) + (z.2 - y.2)) / 2, by omega⟩
  have hz' : z = ((y.1 + u) + (z.1 - y.1 - u), (y.2 + u) - (z.1 - y.1 - u)) :=
    Prod.ext (by ring) (by omega)
  rw [hz']
  exact diagonal_down hharm hle (diagonal_up hharm hle hy u) (z.1 - y.1 - u)

/-- A real function that is harmonic and invariant under `N·ℤ²` is constant. -/
theorem harmonic_periodic_constant (E : Site → ℝ) (N : ℤ) (hN : 0 < N)
    (hper : ∀ x : Site, ∀ k l : ℤ, E (x.1 + k * N, x.2 + l * N) = E x)
    (hharm : ∀ x : Site, E (incomingNeg x) + E (incomingPos x) = 2 * E x) :
    ∀ x : Site, E x = E 0 := by
  obtain ⟨x0, hx0B, hmax⟩ := Finset.exists_max_image
    ((Finset.Ico (0 : ℤ) N) ×ˢ (Finset.Ico (0 : ℤ) N)) E
    ⟨(0, 0), Finset.mem_product.2 ⟨Finset.mem_Ico.2 ⟨le_refl _, hN⟩, Finset.mem_Ico.2 ⟨le_refl _, hN⟩⟩⟩
  have hle : ∀ x : Site, E x ≤ E x0 := by
    intro x
    have hr : (x.1 % N, x.2 % N) ∈ (Finset.Ico (0 : ℤ) N) ×ˢ (Finset.Ico (0 : ℤ) N) :=
      Finset.mem_product.2 ⟨Finset.mem_Ico.2 ⟨Int.emod_nonneg _ hN.ne', Int.emod_lt_of_pos _ hN⟩,
        Finset.mem_Ico.2 ⟨Int.emod_nonneg _ hN.ne', Int.emod_lt_of_pos _ hN⟩⟩
    have h : E (x.1 % N + x.1 / N * N, x.2 % N + x.2 / N * N) = E (x.1 % N, x.2 % N) :=
      hper (x.1 % N, x.2 % N) (x.1 / N) (x.2 / N)
    have e1 : x.1 % N + x.1 / N * N = x.1 := by
      rw [Int.emod_def]
      ring
    have e2 : x.2 % N + x.2 / N * N = x.2 := by
      rw [Int.emod_def]
      ring
    rw [e1, e2] at h
    rw [show (x.1, x.2) = x from rfl] at h
    rw [h]
    exact hmax _ hr
  have hx0 : E x0 = E x0 := rfl
  have hall : ∀ z : Site, E z = E x0 := by
    intro z
    by_cases hz : (z.1 + z.2) % 2 = (x0.1 + x0.2) % 2
    · exact diagonal_const hharm hle hx0 z hz
    · have hpos : E (incomingPos x0) = E x0 := (closed_step hharm hle hx0).2
      have hpar := incomingPos_parity x0
      apply diagonal_const hharm hle hpos z
      omega
  intro x
  rw [hall x, hall 0]

end FLatticePaper.HarmonicConstant
