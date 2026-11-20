import FLatticePaper.GeneralK.Columns
import Mathlib.Data.Int.Init

namespace FLatticePaper.GeneralK

private theorem sub_le_mul_of_step_le (height : ℤ → ℤ) {a b slope : ℤ} (hab : a ≤ b)
    (hstep : ∀ i, a ≤ i → i < b → height (i + 1) - height i ≤ slope) :
    height b - height a ≤ (b - a) * slope := by
  revert hstep
  induction b, hab using Int.leInduction with
  | base => simp
  | succ j hj ih =>
    intro hstep
    have hprev := ih (fun i hi hij => hstep i hi (by omega))
    have hlast := hstep j hj (by omega)
    rw [show (j + 1 - a) * slope = (j - a) * slope + slope by ring]
    omega

private theorem step_antitone (height : ℤ → ℤ) {k i j : ℤ}
    (hconcave : ∀ n, 0 < n → n < k → height (n - 1) + height (n + 1) ≤ 2 * height n)
    (hi : 0 ≤ i) (hij : i ≤ j) (hj : j < k) :
    height (j + 1) - height j ≤ height (i + 1) - height i := by
  revert hj
  induction j, hij using Int.leInduction with
  | base => intro _; exact le_rfl
  | succ j hj ih =>
    intro hjk
    have h := hconcave (j + 1) (by omega) hjk
    rw [add_sub_cancel_right] at h
    have hprev := ih (by omega)
    omega

/-- Every integer chain that is concave at its interior sites lies above the
literal interpolation between its endpoints. -/
theorem interpolate_le_of_concave {k : ℤ} (hk : 2 ≤ k) (height : ℤ → ℤ)
    (hconcave : ∀ n, 0 < n → n < k → height (n - 1) + height (n + 1) ≤ 2 * height n)
    {offset : ℤ} (hlo : 0 ≤ offset) (hhi : offset ≤ k) :
    interpolate k (height 0) (height k) offset ≤ height offset := by
  by_cases htop : offset = k
  · subst offset
    rw [interpolate_top (by omega : 0 < k)]
  have hinside : offset < k := lt_of_le_of_ne hhi htop
  let quotient := (height k - height 0) / k
  let remainder := (height k - height 0) % k
  have hdiv : remainder + k * quotient = height k - height 0 := Int.emod_add_mul_ediv _ _
  change height 0 + offset * quotient + min offset remainder ≤ height offset
  by_cases hnext : height (offset + 1) - height offset ≤ quotient
  · have hsuffix := sub_le_mul_of_step_le height hhi (slope := quotient) fun i hi hik =>
      (step_antitone height hconcave hlo hi hik).trans hnext
    rw [sub_mul] at hsuffix
    omega
  · have hprefix := sub_le_mul_of_step_le (fun i => -height i) hlo (slope := -(quotient + 1))
      (fun i hi hio => by
        have hslope := step_antitone height hconcave hi (by omega : i ≤ offset) hinside
        omega)
    rw [sub_zero, mul_neg, mul_add, mul_one] at hprefix
    omega

theorem interpolate_succ_last_bounds {k : ℤ} (hk : 2 ≤ k) (first last : ℤ)
    {offset : ℤ} (hlo : 0 ≤ offset) (hhi : offset ≤ k) :
    interpolate k first last offset ≤ interpolate k first (last + 1) offset ∧
      interpolate k first (last + 1) offset ≤ interpolate k first last offset + 1 := by
  have hkPos : 0 < k := by omega
  let n := last - first
  have hn : last + 1 - first = n + 1 := by dsimp only [n]; omega
  have hr₀ := Int.emod_nonneg n (ne_of_gt hkPos)
  have hrk := Int.emod_lt_of_pos n hkPos
  simp only [interpolate, hn]
  change first + offset * (n / k) + min offset (n % k) ≤
      first + offset * ((n + 1) / k) + min offset ((n + 1) % k) ∧
    first + offset * ((n + 1) / k) + min offset ((n + 1) % k) ≤
      first + offset * (n / k) + min offset (n % k) + 1
  rw [Int.add_ediv_of_pos hkPos, Int.ediv_eq_zero_of_lt (by decide : (0 : ℤ) ≤ 1) (by omega : 1 < k),
    Int.emod_eq_of_lt (by decide : (0 : ℤ) ≤ 1) (by omega : 1 < k), add_zero,
    ← Int.emod_add_emod n k 1]
  by_cases h : n % k + 1 < k
  · rw [if_neg (not_le_of_gt h), add_zero, Int.emod_eq_of_lt (by omega) h]
    omega
  · have hcarry : n % k + 1 = k := by omega
    rw [hcarry, if_pos le_rfl, Int.emod_self, min_eq_right hlo, add_zero, mul_add, mul_one]
    omega

/-- Raising the top endpoint never lowers the least interpolation. -/
theorem interpolate_monotone_last {k : ℤ} (hk : 2 ≤ k) (first : ℤ)
    {offset : ℤ} (hlo : 0 ≤ offset) (hhi : offset ≤ k) :
    Monotone (fun last => interpolate k first last offset) := by
  apply monotone_int_of_le_succ
  intro last
  exact (interpolate_succ_last_bounds hk first last hlo hhi).1

/-- Raising the bottom endpoint never lowers the least interpolation. -/
theorem interpolate_monotone_first {k : ℤ} (hk : 2 ≤ k) (last : ℤ)
    {offset : ℤ} (hlo : 0 ≤ offset) (hhi : offset ≤ k) :
    Monotone (fun first => interpolate k first last offset) := by
  apply monotone_int_of_le_succ
  intro first
  have h := (interpolate_succ_last_bounds hk first (last - 1) hlo hhi).2
  rw [sub_add_cancel] at h
  have hshift : interpolate k (first + 1) last offset = interpolate k first (last - 1) offset + 1 := by
    simp only [interpolate, show last - (first + 1) = last - 1 - first by omega]
    omega
  rwa [hshift]

/-- Physical superharmonicity on each open chain forces the pointwise
minimum given by lifting the field's own retained values. -/
theorem liftColumns_restriction_le {k : ℤ} (hk : 2 ≤ k) {field : Field}
    (hconcave : ∀ site, ¬ Retained k site → laplacian k field site ≤ 0) :
    liftColumns k (fun ij => field (columnSite k ij.1 ij.2 0)) ≤ field := by
  intro site
  let row := (site.1 + site.2) / k
  let offset := (site.1 + site.2) % k
  have hkPos : 0 < k := by omega
  have hlo : 0 ≤ offset := Int.emod_nonneg _ (ne_of_gt hkPos)
  have hhi : offset < k := Int.emod_lt_of_pos _ hkPos
  let height := fun j => field (columnSite k site.1 row j)
  have hchain (j : ℤ) (hj₀ : 0 < j) (hjk : j < k) :
      height (j - 1) + height (j + 1) ≤ 2 * height j := by
    let center := columnSite k site.1 row j
    have hphase : ¬ Retained k center := by
      change ¬ Retained k (columnSite k site.1 row j)
      rw [Retained, columnSite_phase, Int.emod_eq_of_lt hj₀.le hjk]
      omega
    have h := hconcave center hphase
    have hneg : incomingNeg k center = columnSite k site.1 row (j - 1) := by
      rw [incomingNeg, if_neg hphase]
      exact Prod.ext rfl (by simp only [center, columnSite]; ring)
    have hpos : incomingPos k center = columnSite k site.1 row (j + 1) := by
      rw [incomingPos, if_neg hphase]
      exact Prod.ext rfl (by simp only [center, columnSite]; ring)
    unfold laplacian at h
    rw [hneg, hpos] at h
    change height (j - 1) - height j + (height (j + 1) - height j) ≤ 0 at h
    omega
  have htop : columnSite k site.1 row k = columnSite k site.1 (row + 1) 0 :=
    Prod.ext rfl (by simp only [columnSite]; ring)
  have hcoord : columnSite k site.1 row offset = site := columnSite_coordinates k site
  have h := interpolate_le_of_concave hk height hchain hlo hhi.le
  change interpolate k (field (columnSite k site.1 row 0)) (field (columnSite k site.1 row k)) offset ≤
    field (columnSite k site.1 row offset) at h
  rw [htop, hcoord] at h
  change interpolate k (field (columnSite k site.1 row 0)) (field (columnSite k site.1 (row + 1) 0)) offset ≤
    field site
  exact h

/-- Taking the least extension can only decrease the two incoming heights
at a retained center. -/
theorem columnRow_restriction_nonpos {k : ℤ} (hk : 2 ≤ k) {field : Field}
    (hfield : Superharmonic k field) (column row : ℤ) :
    columnRow k (fun ij => field (columnSite k ij.1 ij.2 0)) column row ≤ 0 := by
  let columns : Field := fun ij => field (columnSite k ij.1 ij.2 0)
  let center := columnSite k column row 0
  have hkPos : 0 < k := by omega
  have hle : liftColumns k columns ≤ field :=
    liftColumns_restriction_le hk (fun site _ => hfield site)
  have hcenter : liftColumns k columns center = field center := by
    rw [liftColumns_columnSite hkPos columns column row 0 le_rfl hkPos, interpolate_zero hkPos]
  have hneg : liftColumns k columns (incomingNeg k center) ≤ field (incomingNeg k center) :=
    hle (incomingNeg k center)
  have hpos : liftColumns k columns (incomingPos k center) ≤ field (incomingPos k center) :=
    hle (incomingPos k center)
  have h := hfield center
  change columnRow k columns column row ≤ 0
  rw [← laplacian_liftColumns_columnSite hk columns column row]
  change laplacian k (liftColumns k columns) center ≤ 0
  simp only [laplacian, hcenter] at h ⊢
  omega

end FLatticePaper.GeneralK
