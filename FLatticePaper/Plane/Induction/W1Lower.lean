import FLatticePaper.Plane.Induction.W1Strips
import FLatticePaper.Plane.Induction.W1Pick

/-! Task 48, step 1: the lower odd h0 interval, from the price chain.

For the odd parent `N/D` of the child, the parent shift `v = ε(N − D, N + D)` moves `s` by `2`, and the price
`P(z) = F z − F(z − v) − ε(N z₁ − D z₂)` satisfies `h(z) − h(z − v) = P(z) − cutPrice` for `h = F − harmonicGrid`
(`harmonicGrid_shift_price`, the identity proved here). With the price range on the closed polygon and the price drift under the
kernel, `0 ≤ h(z) − h(z − v) ≤ 1` on the odd sites with `s ∈ [2 − 3d + n, 2 − 2d]`. -/

namespace FLatticePaper.W1Lower

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Strips FLatticePaper.W1 FLatticePaper.W1Pick

/-- The integer identity behind the price: the harmonic grid moves by `ε(N x − D y) + c` under the parent shift, with `2c` the
numerator `D² + 2DN − N² − ε(D + N)` of the cut price. -/
theorem harmonicGrid_shift_int (x y N D ε c : ℤ) (hε2 : ε * ε = 1)
    (hc2 : 2 * c = D ^ 2 + 2 * D * N - N ^ 2 - ε * (D + N)) :
    harmonicGrid (x, y) - harmonicGrid (x - ε * (N - D), y - ε * (N + D)) = ε * (N * x - D * y) + c := by
  have hsum : x - ε * (N - D) + (y - ε * (N + D)) = (x + y) - 2 * (ε * N) := by ring
  have hpar : (x - ε * (N - D) + (y - ε * (N + D))) % 2 = (x + y) % 2 := by
    rw [hsum]
    generalize ε * N = k
    omega
  have key : (x ^ 2 + 2 * x * y - y ^ 2 - 2 * y - (x + y) % 2) =
      ((x - ε * (N - D)) ^ 2 + 2 * (x - ε * (N - D)) * (y - ε * (N + D)) - (y - ε * (N + D)) ^ 2 -
        2 * (y - ε * (N + D)) - (x - ε * (N - D) + (y - ε * (N + D))) % 2) + 4 * (ε * (N * x - D * y) + c) := by
    rw [hpar]
    linear_combination (2 * (D ^ 2 + 2 * D * N - N ^ 2)) * hε2 - 2 * hc2
  unfold harmonicGrid
  simp only
  rw [key, Int.add_mul_ediv_left _ _ (by norm_num)]
  ring

/-- The cut price is exact: `2 · cutPrice = D² + 2DN − N² − ε(D + N)` for the odd parent. -/
theorem two_cutPrice (frame : ChildFrame) :
    2 * frame.cutPrice = frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num -
      frame.parents.odd.num ^ 2 - frame.eps * (frame.parents.odd.den + frame.parents.odd.num) := by
  have hodd : (frame.parents.odd.num + frame.parents.odd.den) % 2 = 1 := frame.valid.odd_parity
  have hεodd : frame.eps % 2 = 1 := by
    rcases frame.eps_unit with h | h <;> rw [h] <;> norm_num
  have hTp : (frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num -
      frame.parents.odd.num ^ 2 - frame.eps * (frame.parents.odd.den + frame.parents.odd.num)) % 2 = 0 := by
    have hfac : frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num -
        frame.parents.odd.num ^ 2 - frame.eps * (frame.parents.odd.den + frame.parents.odd.num) =
        (frame.parents.odd.den + frame.parents.odd.num) *
          (frame.parents.odd.den - frame.parents.odd.num - frame.eps) +
          2 * (frame.parents.odd.den * frame.parents.odd.num) := by ring
    rw [hfac, Int.add_mul_emod_self_left]
    have hpar2 : (frame.parents.odd.den - frame.parents.odd.num - frame.eps) % 2 = 0 := by omega
    rw [Int.mul_emod, show (frame.parents.odd.den + frame.parents.odd.num) % 2 = 1 by omega, hpar2]
    norm_num
  unfold ChildFrame.cutPrice Fraction.periodDenominator
  exact Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hTp)

/-- **The price identity.** For every site, `h0(z) − h0(z − v) = ε(N z₁ − D z₂) + cutPrice` with `v` the parent shift. -/
theorem harmonicGrid_shift_price (frame : ChildFrame) (z : Site) :
    harmonicGrid z - harmonicGrid (z - frame.parentShift) =
      frame.eps * (frame.parents.odd.num * z.1 - frame.parents.odd.den * z.2) + frame.cutPrice := by
  have hε2 := shortShift_eps_sq frame
  have hc2 := two_cutPrice frame
  obtain ⟨x, y⟩ := z
  have hv : (x, y) - frame.parentShift = (x - frame.eps * (frame.parents.odd.num - frame.parents.odd.den),
      y - frame.eps * (frame.parents.odd.num + frame.parents.odd.den)) := rfl
  rw [hv]
  exact harmonicGrid_shift_int x y frame.parents.odd.num frame.parents.odd.den frame.eps frame.cutPrice hε2
    (by linarith [hc2])

/-- **The price on the lower odd range.** For an odd site with `s ∈ [2 − 3d + n, 2 − 2d]`, the price lies in `[cutPrice, cutPrice + 1]`:
a `U`-shift and a `V`-shift bring the site into the closed polygon, where the price lies in `[cutPrice − 1, cutPrice]`, and the price
drops by one under the kernel period `U` and is unchanged under `V`. -/
theorem price_odd_range (frame : ChildFrame) {F : Field}
    (hPR : ∀ z ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price F z ∧ frame.price F z ≤ frame.cutPrice)
    (hPU : ∀ z, frame.price F (z + frame.child.modifiedDeck.kernel) = frame.price F z - 1)
    (hPV : ∀ z, frame.price F (z + frame.child.modifiedDeck.transverse) = frame.price F z)
    (z : Site) (hz : ¬ EvenSite z) (hlo : 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z)
    (hhi : frame.sGrade z ≤ 2 - 2 * frame.child.den) :
    frame.cutPrice ≤ frame.price F z ∧ frame.price F z ≤ frame.cutPrice + 1 := by
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  have hLev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hT : 0 < w1T frame.child.num frame.child.den := by
    show 0 < frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2
    nlinarith
  have hT2 : 2 * frame.child.den ≤ w1T frame.child.num frame.child.den := by
    show 2 * frame.child.den ≤ frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2
    nlinarith
  have hK := frame.child_modifiedDeck_kernel
  have hVd := frame.child_modifiedDeck_transverse
  have hPVper : Function.Periodic (frame.price F) frame.child.modifiedDeck.transverse := fun w => hPV w
  set m : ℤ := (w1t frame.child.num frame.child.den z - (frame.child.num - w1T frame.child.num frame.child.den)) /
    w1T frame.child.num frame.child.den with hm
  have hzeq : z + lat frame.child.num frame.child.den 1 m =
      (z + frame.child.modifiedDeck.kernel) + m • frame.child.modifiedDeck.transverse := by
    rw [hK, hVd]
    ext <;> simp [lat] <;> ring
  have hPz' : frame.price F (z + lat frame.child.num frame.child.den 1 m) = frame.price F z - 1 := by
    rw [hzeq, hPVper.zsmul m (z + frame.child.modifiedDeck.kernel), hPU z]
  have hEz' : ¬ EvenSite (z + lat frame.child.num frame.child.den 1 m) := fun h =>
    hz ((evenSite_lat frame.child.num frame.child.den (by omega) z 1 m).1 h)
  have hmem : z + lat frame.child.num frame.child.den 1 m ∈ frame.closedPolygon := by
    rw [closedPolygon_eq_closedRect]
    show closedRect frame.child.num frame.child.den (z + lat frame.child.num frame.child.den 1 m)
    unfold closedRect
    rw [if_neg hEz', w1t_lat, w1s_lat]
    have hlo' : 2 - 3 * frame.child.den + frame.child.num ≤ w1s frame.child.num frame.child.den z := hlo
    have hhi' : w1s frame.child.num frame.child.den z ≤ 2 - 2 * frame.child.den := hhi
    have h1 := Int.emod_def (w1t frame.child.num frame.child.den z - (frame.child.num - w1T frame.child.num frame.child.den))
      (w1T frame.child.num frame.child.den)
    have h2 := Int.emod_nonneg (w1t frame.child.num frame.child.den z - (frame.child.num - w1T frame.child.num frame.child.den))
      hT.ne'
    have h3 := Int.emod_lt_of_pos (w1t frame.child.num frame.child.den z - (frame.child.num - w1T frame.child.num frame.child.den)) hT
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  obtain ⟨h1, h2⟩ := hPR _ hmem
  constructor <;> linarith

theorem sGrade_sub_pt (frame : ChildFrame) (x y : Site) :
    frame.sGrade (x - y) = frame.sGrade x - frame.sGrade y := by
  unfold ChildFrame.sGrade
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

theorem sGrade_parentShift (frame : ChildFrame) : frame.sGrade frame.parentShift = 2 := by
  have he : frame.eps = frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num :=
    frame.eps_eq
  have hε2 := shortShift_eps_sq frame
  unfold ChildFrame.sGrade ChildFrame.parentShift
  simp only
  linear_combination 2 * hε2 - 2 * frame.eps * he

theorem evenSite_parentShift (frame : ChildFrame) : EvenSite frame.parentShift := by
  unfold EvenSite ChildFrame.parentShift
  simp only
  rw [show frame.eps * (frame.parents.odd.num - frame.parents.odd.den) +
      frame.eps * (frame.parents.odd.num + frame.parents.odd.den) =
      2 * (frame.eps * frame.parents.odd.num) by ring]
  exact Int.mul_emod_right _ _

/-- The identity of the chain: `(F z − F(z − v)) − (h0 z − h0(z − v)) = P z − cutPrice`. -/
theorem delta_eq_price (frame : ChildFrame) (F : Field) (z : Site) :
    (F z - harmonicGrid z) - (F (z - frame.parentShift) - harmonicGrid (z - frame.parentShift)) =
      frame.price F z - frame.cutPrice := by
  have h := harmonicGrid_shift_price frame z
  unfold ChildFrame.price ChildFrame.parentSlope
  linarith

/-- **The lower odd h0 interval.** For an odd site with `s ∈ [2 − 3d + n, 1 − 2d]`, `F = h0`, given the named seed on the bottom
line `s = 2 − 3d + n` (`hseed`), the price range and drift, and the ordinary h0 strip. -/
theorem lower_odd_h0 (frame : ChildFrame) {F : Field}
    (hstrips : frame.HasStrips F)
    (hPR : ∀ z ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price F z ∧ frame.price F z ≤ frame.cutPrice)
    (hPU : ∀ z, frame.price F (z + frame.child.modifiedDeck.kernel) = frame.price F z - 1)
    (hPV : ∀ z, frame.price F (z + frame.child.modifiedDeck.transverse) = frame.price F z)
    (hseed : ∀ w : Site, ¬ EvenSite w → frame.sGrade w = 2 - 3 * frame.child.den + frame.child.num →
      F w = harmonicGrid w)
    (z : Site) (hz : ¬ EvenSite z) (hlo : 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z)
    (hhi : frame.sGrade z ≤ 1 - 2 * frame.child.den) : F z = harmonicGrid z := by
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  -- the increment of `h = F − h0` along the parent shift lies in `[0, 1]` on the range
  have hδ : ∀ w : Site, ¬ EvenSite w → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade w →
      frame.sGrade w ≤ 2 - 2 * frame.child.den →
      0 ≤ (F w - harmonicGrid w) - (F (w - frame.parentShift) - harmonicGrid (w - frame.parentShift)) ∧
        (F w - harmonicGrid w) - (F (w - frame.parentShift) - harmonicGrid (w - frame.parentShift)) ≤ 1 := by
    intro w hw h1 h2
    rw [delta_eq_price frame F w]
    have := price_odd_range frame hPR hPU hPV w hw h1 h2
    constructor <;> linarith [this.1, this.2]
  have hsv := sGrade_parentShift frame
  have hev := evenSite_parentShift frame
  -- the lower bound from the seed, upward along the chain
  have hlow : ∀ j : ℕ, ∀ w : Site, ¬ EvenSite w → frame.sGrade w = 2 - 3 * frame.child.den + frame.child.num + 2 * (j : ℤ) →
      frame.sGrade w ≤ 2 - 2 * frame.child.den → 0 ≤ F w - harmonicGrid w := by
    intro j
    induction j with
    | zero =>
      intro w hw hs _
      have h0 : F w = harmonicGrid w := hseed w hw (by simpa using hs)
      rw [h0]
      simp
    | succ j ih =>
      intro w hw hs hle
      push_cast at hs
      have hm0 : (0 : ℤ) ≤ (j : ℤ) := by positivity
      have hu : ¬ EvenSite (w - frame.parentShift) := by
        intro h
        apply hw
        have := evenSite_add_pt h hev
        have e : w - frame.parentShift + frame.parentShift = w := by
          ext <;> simp
        rw [e] at this
        exact this
      have hsu : frame.sGrade (w - frame.parentShift) = 2 - 3 * frame.child.den + frame.child.num + 2 * (j : ℤ) := by
        rw [sGrade_sub_pt, hsv]
        omega
      have hI := ih (w - frame.parentShift) hu hsu (by omega)
      have hd := hδ w hw (by omega) hle
      linarith [hd.1]
  -- the upper bound from the ordinary strip, downward along the chain
  have hup : ∀ j : ℕ, ∀ w : Site, ¬ EvenSite w → frame.sGrade w = 2 - 2 * frame.child.den - 2 * (j : ℤ) →
      2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade w → F w - harmonicGrid w ≤ 0 := by
    intro j
    induction j with
    | zero =>
      intro w hw hs _
      have h0 : F w = harmonicGrid w := hstrips.2 w (by simp at hs; omega) (by omega)
      rw [h0]
      simp
    | succ j ih =>
      intro w hw hs hge
      push_cast at hs
      have hm0 : (0 : ℤ) ≤ (j : ℤ) := by positivity
      have hu : ¬ EvenSite (w + frame.parentShift) := by
        intro h
        apply hw
        have := evenSite_add_pt h (evenSite_neg_pt hev)
        have e : w + frame.parentShift + -frame.parentShift = w := by
          ext <;> simp
        rw [← e]
        exact this
      have hsu : frame.sGrade (w + frame.parentShift) = 2 - 2 * frame.child.den - 2 * (j : ℤ) := by
        rw [show frame.sGrade (w + frame.parentShift) = frame.sGrade w + frame.sGrade frame.parentShift from
          by unfold ChildFrame.sGrade ChildFrame.parentShift; simp only [Prod.fst_add, Prod.snd_add]; ring]
        rw [hsv]
        omega
      have hI := ih (w + frame.parentShift) hu hsu (by omega)
      have hd := hδ (w + frame.parentShift) hu (by omega) (by omega)
      have hcancel : w + frame.parentShift - frame.parentShift = w := by
        ext <;> simp
      rw [hcancel] at hd
      linarith [hd.1]
  -- the grade `s` is always even for the child (`L` and `d − n` are even)
  have hLev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hpar : ∀ w : Site, frame.sGrade w % 2 = 0 := by
    intro w
    have hdn : (frame.child.den - frame.child.num) % 2 = 0 := by omega
    unfold ChildFrame.sGrade
    exact FLatticePaper.W1Exit.parity_s frame.child.den frame.child.num w.1 w.2 (by omega) hdn
  obtain ⟨j, hj⟩ : ∃ j : ℕ, frame.sGrade z = 2 - 3 * frame.child.den + frame.child.num + 2 * (j : ℤ) := by
    have hnn : 0 ≤ (frame.sGrade z - (2 - 3 * frame.child.den + frame.child.num)) / 2 := by
      have := hpar z
      omega
    exact ⟨((frame.sGrade z - (2 - 3 * frame.child.den + frame.child.num)) / 2).toNat, by
      rw [Int.toNat_of_nonneg hnn]
      have := hpar z
      omega⟩
  obtain ⟨j', hj'⟩ : ∃ j' : ℕ, frame.sGrade z = 2 - 2 * frame.child.den - 2 * (j' : ℤ) := by
    have hnn : 0 ≤ (2 - 2 * frame.child.den - frame.sGrade z) / 2 := by
      have := hpar z
      omega
    exact ⟨((2 - 2 * frame.child.den - frame.sGrade z) / 2).toNat, by
      rw [Int.toNat_of_nonneg hnn]
      have := hpar z
      omega⟩
  have hA := hlow j z hz hj (by omega)
  have hB := hup j' z hz hj' (by omega)
  have hdiff : F z - harmonicGrid z = 0 := le_antisymm hB hA
  linarith

end FLatticePaper.W1Lower
