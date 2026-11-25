import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.S3FreeBoundary
import FLatticePaper.Plane.Induction.FreeEnum
import FLatticePaper.Plane.Induction.Binary
import FLatticePaper.Plane.Induction.PolygonGeometry

/-! Task w3, hcutC: the free V cut has one point per ordinate for EVERY child frame (no proper-word hypothesis).

`CutRows` assumed `2 ≤ n`, which the odd parity of `n` allows only from `n ≥ 3`; the frames with `n = 1` (the conjugates of pure
words) need the same argument with the universal polygon bounds `1 − T ≤ t ≤ L − 1` and `2 − c ≤ s ≤ T + L − 2`, which hold for
every child frame (`child_facts`), and the parity `t ≡ x + y (mod 2)` (`child_odd`) for the even lower end. -/

namespace FLatticePaper.CutRowsAll

open Farey FLatticePaper FLatticePaper.Induction

/-- Universal bounds of a polygon point: `1 − T ≤ t ≤ L − 1` and `2 − c ≤ s ≤ T + L − 2`. -/
theorem cp_univ (frame : ChildFrame) {p : Site} (hp : p ∈ frame.closedPolygon) :
    1 - frame.child.periodDenominator ≤ frame.tGrade p ∧ frame.tGrade p ≤ frame.child.den + frame.child.num - 1 ∧
      2 - frame.child.den + frame.child.num ≤ frame.sGrade p ∧
      frame.sGrade p ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2 := by
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := frame.child_facts
  rw [FLatticePaper.Induction.mem_closedPolygon_iff] at hp
  split_ifs at hp with he
  · obtain ⟨h1, h2, h3, h4⟩ := hp
    exact ⟨by omega, by omega, by omega, by omega⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hp
    exact ⟨by omega, by omega, by omega, by omega⟩

/-- The parity of `t` is the parity of `x + y` (since `n`, `d` are odd). -/
theorem tGrade_par (frame : ChildFrame) (z : Site) : frame.tGrade z % 2 = (z.1 + z.2) % 2 := by
  obtain ⟨hn, hd⟩ := frame.child_odd
  unfold ChildFrame.tGrade
  have h1 : (frame.child.num * z.1) % 2 = z.1 % 2 := by
    rw [Int.mul_emod, hn]
    simp
  have h2 : (frame.child.den * z.2) % 2 = z.2 % 2 := by
    rw [Int.mul_emod, hd]
    simp
  rw [Int.sub_emod, h1, h2]
  omega

/-- `T = d² + 2dn − n²` is even when `n`, `d` are odd. -/
theorem T_even (frame : ChildFrame) : frame.child.periodDenominator % 2 = 0 := by
  obtain ⟨hn, hd⟩ := frame.child_odd
  have hT : frame.child.periodDenominator = (frame.child.den - frame.child.num) * (frame.child.den + frame.child.num) +
      2 * frame.child.den * frame.child.num := by
    unfold Fraction.periodDenominator
    ring
  have h1 : (frame.child.den - frame.child.num) % 2 = 0 := by omega
  have h2 : (frame.child.den + frame.child.num) % 2 = 0 := by omega
  rw [hT]
  have h3 : ((frame.child.den - frame.child.num) * (frame.child.den + frame.child.num)) % 2 = 0 := by
    rw [Int.mul_emod, h1]
    simp
  rw [Int.add_emod, h3]
  simp [Int.mul_emod]

/-- **Contiguity of a row, for every child frame.** -/
theorem cp_row_contig (frame : ChildFrame) (r x₁ x x₂ : ℤ) (h₁ : (x₁, r) ∈ frame.closedPolygon)
    (h₂ : (x₂, r) ∈ frame.closedPolygon) (hx₁ : x₁ < x) (hx₂ : x < x₂) : (x, r) ∈ frame.closedPolygon := by
  obtain ⟨hn0, hnd', hdn, hd3, -⟩ := frame.child_facts
  obtain ⟨l1, -, s1, -⟩ := cp_univ frame h₁
  obtain ⟨-, u2, -, su2⟩ := cp_univ frame h₂
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
  have hta : 1 - frame.child.periodDenominator + frame.child.num ≤ frame.tGrade (x, r) := by linarith
  have htb : frame.tGrade (x, r) ≤ frame.child.den + frame.child.num - 1 - frame.child.num := by linarith
  have hsa : 2 - frame.child.den + frame.child.num + (frame.child.den + frame.child.num) ≤ frame.sGrade (x, r) := by
    linarith
  have hsb : frame.sGrade (x, r) ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2 -
      (frame.child.den + frame.child.num) := by
    linarith
  rw [FLatticePaper.Induction.mem_closedPolygon_iff]
  split_ifs with he
  · exact ⟨by omega, by omega, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega, by omega⟩

/-- A row has at most one free V point. -/
theorem freeV_row_unique (frame : ChildFrame) (r x₁ x₂ : ℤ) (h₁ : (x₁, r) ∈ frame.freeV) (h₂ : (x₂, r) ∈ frame.freeV) :
    x₁ = x₂ := by
  simp only [ChildFrame.freeV, Set.mem_setOf_eq] at h₁ h₂
  have hu : ∀ a b : ℤ, a < b → (a, r) ∈ frame.closedPolygon → (b, r) ∈ frame.closedPolygon →
      (b - 1, r) ∉ frame.closedPolygon → False := by
    intro a b hab ha hb hbm
    rcases (show a = b - 1 ∨ a < b - 1 by omega) with h | h
    · subst h
      exact hbm ha
    · exact hbm (cp_row_contig frame r a (b - 1) b ha hb (by omega) (by omega))
  rcases lt_trichotomy x₁ x₂ with h | h | h
  · exact (hu x₁ x₂ h h₁.1 h₂.1 h₂.2.1).elim
  · exact h
  · exact (hu x₂ x₁ h h₂.1 h₁.1 h₁.2.1).elim

theorem exists_row_point (frame : ChildFrame) (r : ℤ) (hr0 : 0 ≤ r)
    (hrL : r < frame.child.den + frame.child.num) :
    ∃ x₀ : ℤ, (x₀, r) ∈ frame.closedPolygon ∧ 0 ≤ frame.sGrade (x₀, r) ∧
      frame.sGrade (x₀, r) < frame.child.den + frame.child.num := by
  obtain ⟨hn0, hnd', hdn, hd3, hT⟩ := frame.child_facts
  have hTe := T_even frame
  have hnodd := frame.child_odd.1
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
  have hlow0 : frame.child.num - (frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num -
      frame.child.num * frame.child.num) ≤ frame.tGrade (-q, r) := by
    by_contra hc
    have h1 : frame.tGrade (-q, r) ≤ frame.child.num - (frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num -
        frame.child.num * frame.child.num) - 1 := by omega
    have h2 := mul_le_mul_of_nonneg_left h1 hLpos.le
    nlinarith
  have hlow : frame.child.num - frame.child.periodDenominator ≤ frame.tGrade (-q, r) := by
    linarith [hlow0, hT]
  -- upper bound: t₀ ≤ n − 1
  have hup : frame.tGrade (-q, r) ≤ frame.child.num - 1 := by
    by_contra hc
    have h1 : frame.child.num ≤ frame.tGrade (-q, r) := by omega
    have h2 := mul_le_mul_of_nonneg_left h1 hLpos.le
    have h3 := mul_lt_mul_of_pos_left hsL (show (0:ℤ) < frame.child.num by omega)
    nlinarith
  refine ⟨-q, ?_, hs0, hsL⟩
  rw [FLatticePaper.Induction.mem_closedPolygon_iff]
  split_ifs with he
  · have hpt : frame.tGrade (-q, r) % 2 = 0 := by
      rw [tGrade_par]
      exact he
    exact ⟨by omega, by omega, hs0, by linarith⟩
  · exact ⟨by linarith, by omega, by omega, by linarith⟩

/-- The lower bound of the polygon points of a row: `x ≥ −(d − n)` when `r ≤ L − 1`. -/
theorem row_lower (frame : ChildFrame) (r : ℤ) (hrL : r ≤ frame.child.den + frame.child.num - 1)
    (x : ℤ) (hx : (x, r) ∈ frame.closedPolygon) : -(frame.child.den - frame.child.num) ≤ x := by
  have hc := (cp_univ frame hx).2.2.1
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := frame.child_facts
  unfold ChildFrame.sGrade at hc
  by_contra hcon
  have h1 : x ≤ -(frame.child.den - frame.child.num) - 1 := by omega
  have h2 := mul_le_mul_of_nonneg_left h1 (show (0:ℤ) ≤ frame.child.den + frame.child.num by omega)
  have h3 := mul_le_mul_of_nonneg_left hrL (show (0:ℤ) ≤ frame.child.den - frame.child.num by omega)
  nlinarith

/-- **The cut has one point per ordinate, for every child frame.** -/
theorem cut_one_per_ordinate_all (frame : ChildFrame) : FLatticePaper.FreeEnum.CutOnePerOrdinate frame := by
  classical
  intro r hr0 hrL
  unfold FLatticePaper.FreeEnum.period at hrL
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  obtain ⟨x₀, hx₀, -, hsL⟩ := exists_row_point frame r hr0 hrL
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, (z, r) ∈ frame.closedPolygon → b ≤ z :=
    ⟨-(frame.child.den - frame.child.num), fun z hz => row_lower frame r (by omega) z hz⟩
  obtain ⟨a, ha, hmin⟩ := Int.exists_least_of_bdd hbdd ⟨x₀, hx₀⟩
  have hax : a ≤ x₀ := hmin x₀ hx₀
  have hlow := (cp_univ frame ha).2.2.1
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  have hev := frame.child_even
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
  exact ⟨a, hfree, fun y hy => freeV_row_unique frame r y a hy hfree⟩

end FLatticePaper.CutRowsAll
