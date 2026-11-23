import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.S3FreeBoundary
import FLatticePaper.Plane.Induction.ShortPassages
import FLatticePaper.Plane.Induction.FreeEnum

/-! # The rows of the closed polygon and the free V cut (task 118, step (a))

Along a row `y = r`, `t(x, r) = n x − d r` grows by `n` and `s(x, r) = L x + (d − n) r` grows by `L = d + n` per step.

* `cp_row_contig`: if `(x₁, r)` and `(x₂, r)` lie in the closed polygon, so does every `(x, r)` with `x₁ < x < x₂`.
  Reason: a polygon point has `t ≥ 2 − T` and `s ≥ 2 − d + n`, and `t ≤ L − 2`, `s ≤ T + L − 2`; the step bounds then put
  `t` and `s` of `(x, r)` strictly inside both parity windows, so the parity of `(x, r)` does not matter.
* `freeV_row_unique`: a row contains at most one free V point (from contiguity).

The existence of a free V point on each row `0 ≤ r < L`, and that the leftmost polygon point of a row satisfies `s ≤ L − 2`,
are NOT proved here (checked numerically on 2724 rows of the 74 frames). They are the remaining part of `CutOnePerOrdinate`. -/

namespace FLatticePaper.CutRows

open Farey FLatticePaper FLatticePaper.Induction

/-- Lower bounds of a polygon point of a row: `t ≥ 2 − T` and `s ≥ 2 − d + n`. -/
theorem cp_lower (frame : ChildFrame) (hn2 : 2 ≤ frame.child.num) (hnd : frame.child.num + 2 ≤ frame.child.den)
    {p : Site} (hp : p ∈ frame.closedPolygon) :
    2 - frame.child.periodDenominator ≤ frame.tGrade p ∧ 2 - frame.child.den + frame.child.num ≤ frame.sGrade p := by
  rw [FLatticePaper.Induction.mem_closedPolygon_iff] at hp
  split_ifs at hp with he
  · obtain ⟨h1, -, h3, -⟩ := hp
    constructor <;> omega
  · obtain ⟨h1, -, h3, -⟩ := hp
    constructor <;> omega

/-- Upper bounds of a polygon point of a row: `t ≤ L − 2` and `s ≤ T + L − 2`. -/
theorem cp_upper (frame : ChildFrame) (hn2 : 2 ≤ frame.child.num) (hnd : frame.child.num + 2 ≤ frame.child.den)
    {p : Site} (hp : p ∈ frame.closedPolygon) :
    frame.tGrade p ≤ frame.child.den + frame.child.num - 2 ∧
      frame.sGrade p ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2 := by
  rw [FLatticePaper.Induction.mem_closedPolygon_iff] at hp
  split_ifs at hp with he
  · obtain ⟨-, h2, -, h4⟩ := hp
    constructor <;> omega
  · obtain ⟨-, h2, -, h4⟩ := hp
    constructor <;> omega

/-- **Contiguity of a row.** Two polygon points of the row `r` force every point between them into the polygon. -/
theorem cp_row_contig (frame : ChildFrame) (hn2 : 2 ≤ frame.child.num) (hnd : frame.child.num + 2 ≤ frame.child.den)
    (r x₁ x x₂ : ℤ) (h₁ : (x₁, r) ∈ frame.closedPolygon) (h₂ : (x₂, r) ∈ frame.closedPolygon)
    (hx₁ : x₁ < x) (hx₂ : x < x₂) : (x, r) ∈ frame.closedPolygon := by
  obtain ⟨hn0, hnd', hdn, hd3, hT⟩ := frame.child_facts
  obtain ⟨l1, l2⟩ := cp_lower frame hn2 hnd h₁
  obtain ⟨u1, u2⟩ := cp_upper frame hn2 hnd h₂
  have ht1 : frame.tGrade (x, r) = frame.tGrade (x₁, r) + frame.child.num * (x - x₁) := by
    unfold ChildFrame.tGrade
    ring
  have ht2 : frame.tGrade (x₂, r) = frame.tGrade (x, r) + frame.child.num * (x₂ - x) := by
    unfold ChildFrame.tGrade
    ring
  have hs1 : frame.sGrade (x, r) = frame.sGrade (x₁, r) + (frame.child.den + frame.child.num) * (x - x₁) := by
    unfold ChildFrame.sGrade
    ring
  have hs2 : frame.sGrade (x₂, r) = frame.sGrade (x, r) + (frame.child.den + frame.child.num) * (x₂ - x) := by
    unfold ChildFrame.sGrade
    ring
  have hk : frame.child.num ≤ frame.child.num * (x - x₁) := by nlinarith
  have hm : frame.child.num ≤ frame.child.num * (x₂ - x) := by nlinarith
  have hLk : frame.child.den + frame.child.num ≤ (frame.child.den + frame.child.num) * (x - x₁) := by nlinarith
  have hLm : frame.child.den + frame.child.num ≤ (frame.child.den + frame.child.num) * (x₂ - x) := by nlinarith
  -- the bounds of (x, r): t ∈ [2 − T + n, L − 2 − n] and s ∈ [2 − d + n + L, T − 2]
  have hta : 2 - frame.child.periodDenominator + frame.child.num ≤ frame.tGrade (x, r) := by omega
  have htb : frame.tGrade (x, r) ≤ frame.child.den + frame.child.num - 2 - frame.child.num := by omega
  have hsa : 2 - frame.child.den + frame.child.num + (frame.child.den + frame.child.num) ≤ frame.sGrade (x, r) := by
    omega
  have hsb : frame.sGrade (x, r) ≤ frame.child.periodDenominator - 2 := by omega
  rw [FLatticePaper.Induction.mem_closedPolygon_iff]
  split_ifs with he
  · exact ⟨by omega, by omega, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega, by omega⟩

/-- **A row has at most one free V point.** -/
theorem freeV_row_unique (frame : ChildFrame) (hn2 : 2 ≤ frame.child.num) (hnd : frame.child.num + 2 ≤ frame.child.den)
    (r x₁ x₂ : ℤ) (h₁ : (x₁, r) ∈ frame.freeV) (h₂ : (x₂, r) ∈ frame.freeV) : x₁ = x₂ := by
  simp only [ChildFrame.freeV, Set.mem_setOf_eq] at h₁ h₂
  have hu : ∀ a b : ℤ, a < b → (a, r) ∈ frame.closedPolygon → (b, r) ∈ frame.closedPolygon →
      (b - 1, r) ∉ frame.closedPolygon → False := by
    intro a b hab ha hb hbm
    rcases (show a = b - 1 ∨ a < b - 1 by omega) with h | h
    · subst h
      exact hbm ha
    · exact hbm (cp_row_contig frame hn2 hnd r a (b - 1) b ha hb (by omega) (by omega))
  rcases lt_trichotomy x₁ x₂ with h | h | h
  · exact (hu x₁ x₂ h h₁.1 h₂.1 h₂.2.1).elim
  · exact h
  · exact (hu x₂ x₁ h h₂.1 h₁.1 h₁.2.1).elim

/-- **A row point.** For `0 ≤ r < L`, some `x₀` puts `(x₀, r)` in the closed polygon with `s(x₀, r) ∈ [0, L)`. -/
theorem exists_row_point (frame : ChildFrame) (hn2 : 2 ≤ frame.child.num)
    (hnd : frame.child.num + 2 ≤ frame.child.den) (r : ℤ) (hr0 : 0 ≤ r)
    (hrL : r < frame.child.den + frame.child.num) :
    ∃ x₀ : ℤ, (x₀, r) ∈ frame.closedPolygon ∧ 0 ≤ frame.sGrade (x₀, r) ∧
      frame.sGrade (x₀, r) < frame.child.den + frame.child.num := by
  obtain ⟨hn0, hnd', hdn, hd3, hT⟩ := frame.child_facts
  obtain ⟨q, hq⟩ : ∃ q : ℤ, q = ((frame.child.den - frame.child.num) * r) / (frame.child.den + frame.child.num) :=
    ⟨_, rfl⟩
  have hLpos : 0 < frame.child.den + frame.child.num := by omega
  have hsm : frame.sGrade (-q, r) = ((frame.child.den - frame.child.num) * r) % (frame.child.den + frame.child.num) := by
    rw [Int.emod_def, ← hq]
    unfold ChildFrame.sGrade
    ring
  have hs0 : 0 ≤ frame.sGrade (-q, r) := by
    rw [hsm]
    exact Int.emod_nonneg _ hLpos.ne'
  have hsL : frame.sGrade (-q, r) < frame.child.den + frame.child.num := by
    rw [hsm]
    exact Int.emod_lt_of_pos _ hLpos
  have key : (frame.child.den + frame.child.num) * frame.tGrade (-q, r) =
      frame.child.num * frame.sGrade (-q, r) -
        (frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num - frame.child.num * frame.child.num) * r := by
    unfold ChildFrame.tGrade ChildFrame.sGrade
    ring
  have hTL : frame.child.num * (frame.child.den + frame.child.num) ≤
      frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num - frame.child.num * frame.child.num := by
    nlinarith
  have hTpos : 0 < frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num - frame.child.num * frame.child.num := by
    nlinarith
  have hrL' : r ≤ frame.child.den + frame.child.num - 1 := by omega
  have hLT : frame.child.den + frame.child.num ≤
      frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num - frame.child.num * frame.child.num := by
    nlinarith
  have hCr : (frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num - frame.child.num * frame.child.num) * r ≤
      (frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num - frame.child.num * frame.child.num) *
        (frame.child.den + frame.child.num - 1) :=
    mul_le_mul_of_nonneg_left hrL' hTpos.le
  have hr_nn : 0 ≤ (frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num - frame.child.num * frame.child.num) * r :=
    mul_nonneg hTpos.le hr0
  have hsn : 0 ≤ frame.child.num * frame.sGrade (-q, r) := mul_nonneg (by omega) hs0
  -- lower bound: t₀ ≥ n − T
  have hlow : frame.child.num - (frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num -
      frame.child.num * frame.child.num) ≤ frame.tGrade (-q, r) := by
    by_contra hc
    have h1 : frame.tGrade (-q, r) ≤ frame.child.num - (frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num -
        frame.child.num * frame.child.num) - 1 := by omega
    have h2 := mul_le_mul_of_nonneg_left h1 hLpos.le
    nlinarith
  -- upper bound: t₀ ≤ n − 1
  have hup : frame.tGrade (-q, r) ≤ frame.child.num - 1 := by
    by_contra hc
    have h1 : frame.child.num ≤ frame.tGrade (-q, r) := by omega
    have h2 := mul_le_mul_of_nonneg_left h1 hLpos.le
    have h3 := mul_lt_mul_of_pos_left hsL (show (0:ℤ) < frame.child.num by omega)
    nlinarith
  refine ⟨-q, ?_, hs0, hsL⟩
  rw [FLatticePaper.Induction.mem_closedPolygon_iff]
  have hTeq := hT
  rw [hTeq]
  split_ifs with he
  · exact ⟨by linarith, by omega, hs0, by linarith⟩
  · exact ⟨by linarith, by omega, by omega, by linarith⟩

/-- The lower bound of the polygon points of a row: `x ≥ −(d − n)` when `r ≤ L − 1`. -/
theorem row_lower (frame : ChildFrame) (hn2 : 2 ≤ frame.child.num)
    (hnd : frame.child.num + 2 ≤ frame.child.den) (r : ℤ) (hrL : r ≤ frame.child.den + frame.child.num - 1)
    (x : ℤ) (hx : (x, r) ∈ frame.closedPolygon) : -(frame.child.den - frame.child.num) ≤ x := by
  have hc := (cp_lower frame hn2 hnd hx).2
  unfold ChildFrame.sGrade at hc
  by_contra hcon
  have h1 : x ≤ -(frame.child.den - frame.child.num) - 1 := by omega
  have h2 := mul_le_mul_of_nonneg_left h1 (show (0:ℤ) ≤ frame.child.den + frame.child.num by omega)
  have h3 := mul_le_mul_of_nonneg_left hrL (show (0:ℤ) ≤ frame.child.den - frame.child.num by omega)
  nlinarith

/-- **The cut has one point per ordinate.** For `0 ≤ r < L`, the row `r` has exactly one free V point. -/
theorem cut_one_per_ordinate (frame : ChildFrame) (hn2 : 2 ≤ frame.child.num)
    (hnd : frame.child.num + 2 ≤ frame.child.den) (hev : (frame.child.num + frame.child.den) % 2 = 0) :
    FLatticePaper.FreeEnum.CutOnePerOrdinate frame := by
  classical
  intro r hr0 hrL
  unfold FLatticePaper.FreeEnum.period at hrL
  obtain ⟨x₀, hx₀, -, hsL⟩ := exists_row_point frame hn2 hnd r hr0 hrL
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, (z, r) ∈ frame.closedPolygon → b ≤ z :=
    ⟨-(frame.child.den - frame.child.num), fun z hz => row_lower frame hn2 hnd r (by omega) z hz⟩
  obtain ⟨a, ha, hmin⟩ := Int.exists_least_of_bdd hbdd ⟨x₀, hx₀⟩
  have hax : a ≤ x₀ := hmin x₀ hx₀
  have hlow := (cp_lower frame hn2 hnd ha).2
  obtain ⟨k, hk⟩ : ∃ k : ℤ, frame.child.den + frame.child.num = 2 * k :=
    ⟨(frame.child.den + frame.child.num) / 2, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, frame.child.den - frame.child.num = 2 * j :=
    ⟨(frame.child.den - frame.child.num) / 2, by omega⟩
  have hsev : frame.sGrade (a, r) = 2 * (k * a + j * r) := by
    unfold ChildFrame.sGrade
    rw [hk, hj]
    ring
  have hpar : frame.sGrade (a, r) % 2 = 0 := by
    rw [hsev]
    omega
  have hsle : frame.sGrade (a, r) ≤ frame.sGrade (x₀, r) := by
    unfold ChildFrame.sGrade
    nlinarith
  have hfree : (a, r) ∈ frame.freeV := by
    show (a, r) ∈ frame.closedPolygon ∧ (a - 1, r) ∉ frame.closedPolygon ∧ frame.vSpectrum (frame.sGrade (a, r))
    refine ⟨ha, ?_, ?_⟩
    · intro h
      have := hmin (a - 1) h
      omega
    · unfold ChildFrame.vSpectrum
      exact ⟨hpar, Or.inr ⟨hlow, by omega⟩⟩
  exact ⟨a, hfree, fun y hy => freeV_row_unique frame hn2 hnd r y a hy hfree⟩

end FLatticePaper.CutRows
