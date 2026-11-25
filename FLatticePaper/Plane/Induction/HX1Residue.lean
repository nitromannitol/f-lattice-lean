import FLatticePaper.Plane.Induction.LowerBandCore
import FLatticePaper.Plane.Induction.LowerBand
import FLatticePaper.Plane.Induction.ShortPassages

/-! # The neighbours hX1 of an even free V root are nonfree (residue avoidance)

For an even free V root `z` (not the origin; not `vLast` for the west neighbour) the east neighbour `(z.1 + 1, z.2)` and the west
neighbour `(z.1 - 1, z.2)` are nonfree: `ShortPassages.nonfree_of_avoid` applies, since no translate of the neighbour has its
`t`-grade in the H spectrum or its `s`-grade in the V spectrum. Together with the binary field this is the `hX1` dichotomy. -/

namespace FLatticePaper.Induction

open LowerBandCore

/-- `P` exceeds `2(d+n) - 2` for a child `n/d` with `d - n ≥ 2`, `n > 0`. -/
theorem P_gt_L (n d P : ℤ) (hn0 : 0 < n) (hdn : 2 ≤ d - n) (hP : P = d ^ 2 + 2 * d * n - n ^ 2) :
    2 * (d + n) - 2 < P := by
  subst hP
  nlinarith

/-- The origin is the only even free V root with `t = 0`. -/
theorem core_t0 {n d P a b s : ℤ} (hn0 : 0 < n) (hnd : n < d) (hdn : 2 ≤ d - n)
    (hP : P = d ^ 2 + 2 * d * n - n ^ 2)
    (hA : P * a = (d - n) * 0 + d * s) (hB : P * b = n * s - (d + n) * 0)
    (hs1 : 0 ≤ s) (hs2 : s ≤ 2 * n) : a = 0 ∧ b = 0 := by
  have hPpos : 0 < P := by rw [hP]; nlinarith
  have hds : d * s ≤ 2 * n * d := by nlinarith
  have hlt : d * s < P := by rw [hP]; nlinarith
  have ha : a = 0 := by
    by_contra h
    rcases lt_or_gt_of_ne h with h' | h'
    · nlinarith [mul_le_mul_of_nonneg_left (show a ≤ -1 by omega) hPpos.le]
    · nlinarith [mul_le_mul_of_nonneg_left (show 1 ≤ a by omega) hPpos.le]
  subst ha
  have hds0 : d * s = 0 := by linear_combination -hA
  have hs0 : s = 0 := by
    rcases mul_eq_zero.mp hds0 with h | h
    · omega
    · exact h
  subst hs0
  have hPb : P * b = 0 := by linear_combination hB
  exact ⟨rfl, (mul_eq_zero.mp hPb).resolve_left hPpos.ne'⟩

/-- Integer form of `IsCoprime d P` from `u n + v d = 1` and `P = d² + 2dn - n²`. -/
theorem coprime_d_P {n d P u v : ℤ} (hP : P = d ^ 2 + 2 * d * n - n ^ 2) (huv : u * n + v * d = 1) :
    IsCoprime d P :=
  ⟨u ^ 2 * (d + 2 * n) + 2 * v - v ^ 2 * d, -u ^ 2, by
    subst hP
    linear_combination (u * n - v * d + 1) * huv⟩

/-- On `t = L - P` with `0 ≤ s ≤ 2n`, the even point is `vLast`. -/
theorem core_vlast {n d P a b s : ℤ} (hn0 : 0 < n) (hnd : n < d) (hdn : 2 ≤ d - n)
    (hP : P = d ^ 2 + 2 * d * n - n ^ 2) (hcop : IsCoprime d P)
    (hA : P * a = (d - n) * (n + d - P) + d * s) (hB : P * b = n * s - (d + n) * (n + d - P))
    (hs1 : 0 ≤ s) (hs2 : s ≤ 2 * n) : a = n - d + 1 ∧ b = n + d - 1 := by
  have hPpos : 0 < P := by rw [hP]; nlinarith
  have hα : P * (a - (n - d + 1)) = d * (s - 2 * n) := by
    linear_combination hA - hP
  obtain ⟨m, hm⟩ := hcop.dvd_of_dvd_mul_left ⟨s - 2 * n, hα⟩
  have hPm : P * m = s - 2 * n := by
    have hd0 : d ≠ 0 := by omega
    apply mul_left_cancel₀ hd0
    rw [hm] at hα
    linear_combination hα
  have hm0 : m = 0 := by
    by_contra h
    rcases lt_or_gt_of_ne h with h' | h'
    · nlinarith [mul_le_mul_of_nonneg_left (show m ≤ -1 by omega) hPpos.le]
    · nlinarith [mul_le_mul_of_nonneg_left (show 1 ≤ m by omega) hPpos.le]
  subst hm0
  have hα0 : a - (n - d + 1) = 0 := by rw [hm]; ring
  have hs : s = 2 * n := by
    have : P * 0 = s - 2 * n := hPm
    linarith
  subst hs
  have hPb : P * (b - (n + d - 1)) = 0 := by
    linear_combination hB + hP
  have hb : b - (n + d - 1) = 0 := (mul_eq_zero.mp hPb).resolve_left hPpos.ne'
  constructor <;> omega

namespace ChildFrame
variable (frame : ChildFrame)

/-- The bounds of an even free V root in the grades: `0 ≤ s ≤ 2n`, `L - P ≤ t ≤ 0`. -/
theorem root_bounds {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z) :
    0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ 2 * frame.child.num ∧
      frame.child.den + frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z ∧
      frame.tGrade z ≤ 0 := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hodd := frame.child_num_odd
  have hcoprime : ∃ u v : ℤ, u * frame.child.num + v * frame.child.den = 1 := frame.child_reduced
  obtain ⟨u, v, huv⟩ := hcoprime
  have hcop : IsCoprime frame.child.den (frame.child.den - frame.child.num) :=
    ⟨u + v, -u, by linear_combination huv⟩
  have hA := frame.ident_a z
  obtain ⟨hzcp, hzn, hzspec⟩ := hz
  have hpz : 2 - frame.child.periodDenominator ≤ frame.tGrade z ∧
      frame.tGrade z ≤ frame.child.den + frame.child.num - 2 ∧ 0 ≤ frame.sGrade z ∧
      frame.sGrade z ≤ frame.child.periodDenominator + 2 * frame.child.num := by
    rcases (frame.mem_closedPolygon_iff z).mp hzcp with h | h
    · exact h.2
    · exact absurd hev h.1
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hpz
  have hsv : frame.sGrade z % 2 = 0 ∧
      ((0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ 2 * frame.child.num) ∨
        (2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
          frame.sGrade z ≤ frame.child.den + frame.child.num - 2)) := hzspec
  obtain ⟨hsE, hspec⟩ := hsv
  have hnot : frame.tGrade z < 2 * frame.child.num - frame.child.periodDenominator ∨
      frame.sGrade z < 2 * frame.child.num + 2 := by
    by_contra hc
    push Not at hc
    apply hzn
    rw [frame.mem_closedPolygon_iff]
    have hodd' : ¬ EvenSite (z.1 - 1, z.2) := by
      show ¬ ((z.1 - 1 + z.2) % 2 = 0)
      have hev' : (z.1 + z.2) % 2 = 0 := hev
      omega
    right
    refine ⟨hodd', ?_, ?_, ?_, ?_⟩
    · rw [frame.tGrade_sub_x]; omega
    · rw [frame.tGrade_sub_x]; omega
    · rw [frame.sGrade_sub_x]; omega
    · rw [frame.sGrade_sub_x]; omega
  have hev' : (z.1 + z.2) % 2 = 0 := hev
  have hs2n : frame.sGrade z ≤ 2 * frame.child.num :=
    core_s_le hn0 hnd hdn hd3 hP hcop hA hp1 hp3 hsE hspec hnot
  have hTb := core_t_bounds hn0 hnd hdn hd3 hP hA hp1 hp2 hp3 hs2n
  exact ⟨hp3, hs2n, hTb.1, hTb.2⟩

/-- The grade `t` of an even point is even (the child `n/d` has both entries odd). -/
theorem tGrade_even {z : Site} (hev : EvenSite z) : frame.tGrade z % 2 = 0 := by
  have hn := frame.child_num_odd
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hd : frame.child.den % 2 = 1 := by omega
  obtain ⟨k, hk⟩ : ∃ k, frame.child.num = 2 * k + 1 := ⟨frame.child.num / 2, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, frame.child.den = 2 * m + 1 := ⟨frame.child.den / 2, by omega⟩
  have hev' : (z.1 + z.2) % 2 = 0 := hev
  unfold ChildFrame.tGrade
  rw [hk, hm]
  have key : (2 * k + 1) * z.1 - (2 * m + 1) * z.2 = 2 * (k * z.1 - m * z.2) + (z.1 - z.2) := by ring
  rw [key]
  omega

/-- The east neighbour of an even free V root (not the origin) is nonfree. -/
theorem nonfree_east {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z)
    (hzF : z ≠ FLatticePaper.Induction.vFirst) : Nonfree frame (z.1 + 1, z.2) := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hodd := frame.child_num_odd
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * frame.child.num + v * frame.child.den = 1 := frame.child_reduced
  obtain ⟨hs1, hs2, ht1, ht2⟩ := frame.root_bounds hz hev
  have hpar := frame.tGrade_even hev
  have hPpar := frame.T_even
  have hA := frame.ident_a z
  have hB := frame.ident_b z
  have ht0 : frame.tGrade z ≠ 0 := by
    intro h0
    rw [h0] at hA hB
    obtain ⟨ha, hb⟩ := core_t0 hn0 hnd hdn hP hA hB hs1 hs2
    exact hzF (Prod.ext ha hb)
  have hPgt := P_gt_L _ _ _ hn0 hdn hP
  apply FLatticePaper.Induction.ShortPassages.nonfree_of_avoid
  · intro j hj
    rw [frame.tGrade_add_x] at hj
    unfold ChildFrame.hSpectrum at hj
    rcases hj with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have hjP : (j * frame.child.periodDenominator) % 2 = 0 := by
        rw [Int.mul_emod, hPpar]; simp
      omega
    · rcases lt_trichotomy j 0 with hj0 | hj0 | hj0
      · nlinarith [mul_le_mul_of_nonneg_left (show (1:ℤ) ≤ -j by omega) (show (0:ℤ) ≤ frame.child.periodDenominator by omega)]
      · subst hj0
        have : frame.tGrade z = 0 := by omega
        exact ht0 this
      · nlinarith [mul_le_mul_of_nonneg_left (show (1:ℤ) ≤ j by omega) (show (0:ℤ) ≤ frame.child.periodDenominator by omega)]
  · intro i hi
    rw [frame.sGrade_add_x] at hi
    unfold ChildFrame.vSpectrum at hi
    obtain ⟨hpar', hb⟩ := hi
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases lt_trichotomy i 0 with hi0 | hi0 | hi0
    · nlinarith [mul_le_mul_of_nonneg_left (show i ≤ -1 by omega) (show (0:ℤ) ≤ frame.child.periodDenominator by omega)]
    · subst hi0; omega
    · nlinarith [mul_le_mul_of_nonneg_left (show (1:ℤ) ≤ i by omega) (show (0:ℤ) ≤ frame.child.periodDenominator by omega)]
    · nlinarith [mul_le_mul_of_nonneg_left (show i ≤ -1 by omega) (show (0:ℤ) ≤ frame.child.periodDenominator by omega)]
    · subst hi0; omega
    · nlinarith [mul_le_mul_of_nonneg_left (show (1:ℤ) ≤ i by omega) (show (0:ℤ) ≤ frame.child.periodDenominator by omega)]

/-- The west neighbour of an even free V root (not the origin, not `vLast`) is nonfree. -/
theorem nonfree_west {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z)
    (hzF : z ≠ FLatticePaper.Induction.vFirst) (hzL : z ≠ frame.vLast) :
    Nonfree frame (z.1 - 1, z.2) := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hodd := frame.child_num_odd
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hPpar := frame.T_even
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * frame.child.num + v * frame.child.den = 1 := frame.child_reduced
  obtain ⟨hs1, hs2, ht1, ht2⟩ := frame.root_bounds hz hev
  have hpar_t := frame.tGrade_even hev
  have hA := frame.ident_a z
  have hB := frame.ident_b z
  have ht0 : frame.tGrade z ≠ 0 := by
    intro h0
    rw [h0] at hA hB
    obtain ⟨ha, hb⟩ := core_t0 hn0 hnd hdn hP hA hB hs1 hs2
    exact hzF (Prod.ext ha hb)
  have htL : frame.tGrade z ≠ frame.child.den + frame.child.num - frame.child.periodDenominator := by
    intro hL
    rw [hL] at hA hB
    have hA' : frame.child.periodDenominator * z.1 = (frame.child.den - frame.child.num) * (frame.child.num + frame.child.den - frame.child.periodDenominator) + frame.child.den * frame.sGrade z := by
      linear_combination hA
    have hB' : frame.child.periodDenominator * z.2 = frame.child.num * frame.sGrade z - (frame.child.den + frame.child.num) * (frame.child.num + frame.child.den - frame.child.periodDenominator) := by
      linear_combination hB
    obtain ⟨ha, hb⟩ := core_vlast hn0 hnd hdn hP (coprime_d_P hP huv) hA' hB' hs1 hs2
    exact hzL (by unfold ChildFrame.vLast; exact Prod.ext ha hb)
  have ht2' : frame.child.den + frame.child.num - frame.child.periodDenominator + 2 ≤ frame.tGrade z := by
    omega
  have hPgt := P_gt_L _ _ _ hn0 hdn hP
  apply FLatticePaper.Induction.ShortPassages.nonfree_of_avoid
  · intro j hj
    rw [frame.tGrade_sub_x] at hj
    unfold ChildFrame.hSpectrum at hj
    rcases hj with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have hjP : (j * frame.child.periodDenominator) % 2 = 0 := by
        rw [Int.mul_emod, hPpar]; simp
      omega
    · rcases lt_trichotomy j 0 with hj0 | hj0 | hj0
      · nlinarith [mul_le_mul_of_nonneg_left (show (1:ℤ) ≤ -j by omega) (show (0:ℤ) ≤ frame.child.periodDenominator by omega)]
      · subst hj0
        omega
      · nlinarith [mul_le_mul_of_nonneg_left (show (1:ℤ) ≤ j by omega) (show (0:ℤ) ≤ frame.child.periodDenominator by omega)]
  · intro i hi
    rw [frame.sGrade_sub_x] at hi
    unfold ChildFrame.vSpectrum at hi
    obtain ⟨hpar', hb⟩ := hi
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases lt_trichotomy i 0 with hi0 | hi0 | hi0
    · nlinarith [mul_le_mul_of_nonneg_left (show i ≤ -1 by omega) (show (0:ℤ) ≤ frame.child.periodDenominator by omega)]
    · subst hi0; omega
    · nlinarith [mul_le_mul_of_nonneg_left (show (1:ℤ) ≤ i by omega) (show (0:ℤ) ≤ frame.child.periodDenominator by omega)]
    · nlinarith [mul_le_mul_of_nonneg_left (show i ≤ -1 by omega) (show (0:ℤ) ≤ frame.child.periodDenominator by omega)]
    · subst hi0; omega
    · nlinarith [mul_le_mul_of_nonneg_left (show (1:ℤ) ≤ i by omega) (show (0:ℤ) ≤ frame.child.periodDenominator by omega)]

/-- The `hX1` dichotomy at the east and west neighbours, from the binary field. -/
theorem hX1_dichotomy {G : Field} (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z) (hzF : z ≠ FLatticePaper.Induction.vFirst)
    {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) (hδz : δ = 1 ∨ z ≠ frame.vLast) :
    laplacian G (z.1 + δ, z.2) = -1 ∨
      (laplacian G (z.1 + δ, z.2) = 0 ∧ Nonfree frame (z.1 + δ, z.2)) := by
  rcases hδ with rfl | rfl
  · have hnf := frame.nonfree_east hz hev hzF
    exact (hbin _).imp id (fun h => ⟨h, hnf⟩)
  · have hzL : z ≠ frame.vLast := hδz.resolve_left (by norm_num)
    have hnf := frame.nonfree_west hz hev hzF hzL
    have e : z.1 + -1 = z.1 - 1 := by ring
    rw [e]
    exact (hbin _).imp id (fun h => ⟨h, hnf⟩)

end ChildFrame

end FLatticePaper.Induction
