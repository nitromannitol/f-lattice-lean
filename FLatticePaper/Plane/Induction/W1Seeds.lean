import FLatticePaper.Plane.Induction.W1Top
import FLatticePaper.Plane.Induction.Q3Paragraph8
import FLatticePaper.Construction.NominalAgreement

/-! Task 50: the two zero seeds of the paired induction as inherited data (archive `.work/fields/escape/newzeros/`).

`SeedFields u` (a proper word `u`) collects the two inherited zero seeds:
* `even_zero`: `G(2 − L) = 0` on the even sites of the line `t = 2 − L` (PAIR_INDUCTION, even role; BASE_TWO_PIXEL_ZEROS §1, §3);
* `odd_zero`: the odd conjugate's zero on the even sites of the line `t_p = 1 − d`, `t_p = n_p x − d_p y` with
  `(d_p, n_p) = (parentD u, parentN u)` (NO_ODD_SLIP_AUDIT §2, §4; PAIR_INDUCTION, odd role).
The odd bottom `h0` seed `F = h0` on `s = 2 − 3d + n` is DERIVED from `odd_zero` (`odd_bottom_of_odd_zero`, by the quarter-turn).
`even_zero_of_parent` derives `even_zero` of a word from its parent's `odd_zero`, the sheet minimum on `E` and the sign of the
second branch (`C(z0) ≥ 0`, named: PAIR_INDUCTION, even child branches, `fC = 1`, exception `0`). -/

namespace FLatticePaper.W1Seeds

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.W1Strips FLatticePaper.W1Top
open FLatticePaper.Construction

/-- The numerator of `h0` is divisible by four (as the private `numer_dvd` of `ChildFrame`). -/
private theorem numer_dvd_seed (p q : ℤ) :
    ∃ k : ℤ, p ^ 2 + 2 * p * q - q ^ 2 - 2 * q - (p + q) % 2 = 4 * k := by
  obtain ⟨a, i, hi, hp⟩ : ∃ a i : ℤ, (i = 0 ∨ i = 1) ∧ p = 2 * a + i :=
    ⟨p / 2, p % 2, by omega, by omega⟩
  obtain ⟨b, j, hj, hq⟩ : ∃ b j : ℤ, (j = 0 ∨ j = 1) ∧ q = 2 * b + j :=
    ⟨q / 2, q % 2, by omega, by omega⟩
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · refine ⟨a ^ 2 + 2 * a * b - b ^ 2 - b, ?_⟩
    have hm : (p + q) % 2 = 0 := by omega
    rw [hm, hp, hq]; ring
  · refine ⟨a ^ 2 + 2 * a * b + a - b ^ 2 - 2 * b - 1, ?_⟩
    have hm : (p + q) % 2 = 1 := by omega
    rw [hm, hp, hq]; ring
  · refine ⟨a ^ 2 + a + 2 * a * b - b ^ 2, ?_⟩
    have hm : (p + q) % 2 = 1 := by omega
    rw [hm, hp, hq]; ring
  · refine ⟨a ^ 2 + 2 * a + 2 * a * b - b ^ 2 - b, ?_⟩
    have hm : (p + q) % 2 = 0 := by omega
    rw [hm, hp, hq]; ring

/-- The inverse quarter-turn of `h0`: `h0(z₂ + 1, −z₁) = −h0(z)`. -/
theorem harmonicGrid_quarter_inv (z : Site) : harmonicGrid (z.2 + 1, -z.1) = -harmonicGrid z := by
  obtain ⟨k, hk⟩ := numer_dvd_seed z.1 z.2
  have hp : ((z.2 + 1) + -z.1) % 2 = 1 - (z.1 + z.2) % 2 := by omega
  have hnum : (z.2 + 1) ^ 2 + 2 * (z.2 + 1) * -z.1 - (-z.1) ^ 2 - 2 * -z.1 - ((z.2 + 1) + -z.1) % 2 = -(4 * k) := by
    rw [hp]; linear_combination (-1 : ℤ) * hk
  unfold harmonicGrid
  dsimp only
  rw [hnum, hk]
  omega

/-- **The odd bottom seed from the odd zero.** If the odd conjugate vanishes on its line `t_p = 1 − d` (even sites), then
`F = h0` on the odd sites of the bottom line `s = 2 − 3d + n`: the point `z` goes to `x = (z₂ + 1, −z₁)`, which is even with
`t_p(x) = s(z)/2 + n_p = 1 − d`, and `quarterTurnField F x = F z + h0(x) = 0`. -/
theorem odd_bottom_of_odd_zero {u : Word}
    (hO : ∀ x : Site, EvenSite x → parentN u * x.1 - parentD u * x.2 = 1 - (parentD u + parentN u) →
      quarterTurnField (standardField u) x = 0)
    (z : Site) (hz : ¬ EvenSite z)
    (hs : (frameAt u).sGrade z = 2 - 3 * (frameAt u).child.den + (frameAt u).child.num) :
    standardField u z = harmonicGrid z := by
  have hev : ((frameAt u).child.num + (frameAt u).child.den) % 2 = 0 := (frameAt u).child_even
  have hN2 : 2 * parentN u = (frameAt u).child.den - (frameAt u).child.num := by
    unfold parentN; omega
  have hD2 : 2 * parentD u = (frameAt u).child.den + (frameAt u).child.num := by
    unfold parentD; omega
  unfold ChildFrame.sGrade at hs
  have hpar : EvenSite (z.2 + 1, -z.1) := by
    unfold EvenSite at hz ⊢
    show ((z.2 + 1) + -z.1) % 2 = 0
    omega
  have hlev : parentN u * (z.2 + 1) - parentD u * (-z.1) = 1 - (parentD u + parentN u) := by
    have key : 2 * (parentN u * (z.2 + 1) - parentD u * (-z.1)) = 2 * (1 - (parentD u + parentN u)) := by
      linear_combination (z.2 + 2) * hN2 + (z.1 + 1) * hD2 + hs
    linarith
  have h := hO _ hpar hlev
  have hZ : QuarterTurn.counterclockwise.mapSite (0, -1) (z.2 + 1, -z.1) = z := by
    rw [quarterTurn_site]
    ext <;> simp
  unfold quarterTurnField at h
  rw [hZ, harmonicGrid_quarter_inv] at h
  linarith

/-- The two inherited zero seeds of a proper word `u` (task 50). -/
structure SeedFields (u : Word) : Prop where
  /-- `G(2 − L) = 0` on the even sites of the line `t = 2 − L` (the even seed). -/
  even_zero : ∀ z : Site, EvenSite z →
    (frameAt u).tGrade z = 2 - ((frameAt u).child.den + (frameAt u).child.num) → standardField u z = 0
  /-- The odd conjugate's zero on the even sites of its line `t_p = 1 − d` (the odd seed). -/
  odd_zero : ∀ x : Site, EvenSite x →
    parentN u * x.1 - parentD u * x.2 = 1 - (parentD u + parentN u) → quarterTurnField (standardField u) x = 0

/-- The odd bottom seed of the structure, derived from `odd_zero`. -/
theorem SeedFields.odd_bottom {u : Word} (h : SeedFields u) (z : Site) (hz : ¬ EvenSite z)
    (hs : (frameAt u).sGrade z = 2 - 3 * (frameAt u).child.den + (frameAt u).child.num) :
    standardField u z = harmonicGrid z :=
  odd_bottom_of_odd_zero h.odd_zero z hz hs

/-! The even seed point of the child: the unique site with `t = 2 − L` and `t_p(z − lv) = 1 − (D+N)`. -/

/-- `K = 1 − (D + N) + (1 − W) ε`, so that `t_p(z) = K` at the seed point. -/
def seedK (frame : ChildFrame) : ℤ :=
  1 - (frame.parents.odd.den + frame.parents.odd.num) + (1 - frame.phaseW) * frame.eps

/-- The seed point `z0 = ε (d K − D (2 − L), n K − N (2 − L))`. -/
def seedPoint (frame : ChildFrame) : Site :=
  (frame.eps * (frame.child.den * seedK frame - frame.parents.odd.den * (2 - (frame.child.den + frame.child.num))),
    frame.eps * (frame.child.num * seedK frame - frame.parents.odd.num * (2 - (frame.child.den + frame.child.num))))

theorem eps_sq (frame : ChildFrame) : frame.eps * frame.eps = 1 := by
  rcases frame.eps_unit with h | h <;> rw [h] <;> norm_num

theorem seed_t (frame : ChildFrame) :
    frame.tGrade (seedPoint frame) = 2 - (frame.child.den + frame.child.num) := by
  have h1 := frame.eps_eq
  have h2 := eps_sq frame
  unfold ChildFrame.tGrade seedPoint
  dsimp only
  linear_combination (-(2 - (frame.child.den + frame.child.num)) * frame.eps) * h1 +
    (2 - (frame.child.den + frame.child.num)) * h2

theorem seed_tp (frame : ChildFrame) :
    frame.parents.odd.num * (seedPoint frame).1 - frame.parents.odd.den * (seedPoint frame).2 = seedK frame := by
  have h1 := frame.eps_eq
  have h2 := eps_sq frame
  unfold seedPoint
  dsimp only
  linear_combination (-(frame.eps * seedK frame)) * h1 + seedK frame * h2

/-- The coordinate sum of the seed point is even (the child's `L` is even). -/
theorem seed_sum (frame : ChildFrame) :
    ∃ Y : ℤ, (seedPoint frame).1 + (seedPoint frame).2 = 2 * Y := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, frame.child.den + frame.child.num = 2 * m :=
    ⟨(frame.child.den + frame.child.num) / 2, by
      have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
      omega⟩
  refine ⟨frame.eps * (m * seedK frame - (frame.parents.odd.den + frame.parents.odd.num) * (1 - m)), ?_⟩
  unfold seedPoint
  dsimp only
  linear_combination (frame.eps * seedK frame + frame.eps * (frame.parents.odd.den + frame.parents.odd.num)) * hm

theorem seed_even (frame : ChildFrame) : EvenSite (seedPoint frame) := by
  obtain ⟨Y, hY⟩ := seed_sum frame
  unfold EvenSite
  rw [hY]
  omega

theorem phaseW_pos (frame : ChildFrame) (h : frame.eps = 1) : frame.phaseW = 1 := by
  unfold ChildFrame.phaseW; rw [h]; norm_num

theorem phaseW_neg (frame : ChildFrame) (h : frame.eps = -1) : frame.phaseW = 0 := by
  unfold ChildFrame.phaseW; rw [h]; norm_num

/-- The sine-type grade of the seed point: `s(z0) = ε (K T − (2 − L) C)`, with `T` the period denominator and `C` the parent constant. -/
theorem seed_s (frame : ChildFrame) :
    frame.sGrade (seedPoint frame) = frame.eps * (seedK frame * frame.child.periodDenominator -
      (2 - (frame.child.den + frame.child.num)) * frame.parentC) := by
  unfold ChildFrame.sGrade seedPoint ChildFrame.parentC Fraction.periodDenominator
  dsimp only
  ring

/-- **The seed point lies in the closed polygon** (`E`). The `t`-range is `t = 2 − L`; the `s`-range reduces to
`2C + 2n ≤ T` (`ε = 1`) and `n ≤ C`, `2C ≤ T` (`ε = −1`), from `C d = D T + ε(d − n)` and `D ≤ (d − 1)/2`. -/
theorem seed_mem (frame : ChildFrame) : seedPoint frame ∈ frame.closedPolygon := by
  have hev : EvenSite (seedPoint frame) := seed_even frame
  obtain ⟨hpos, hnlt, hdn, hd3, hTeq⟩ := frame.child_facts
  have hTL : frame.child.den + frame.child.num ≤ frame.child.periodDenominator := child_T_ge_L frame
  have hden : frame.child.den = 2 * frame.parents.odd.den + frame.parents.even.den := ZoneI1.child_den_eq frame
  have hevq : 0 < frame.parents.even.den := by have := frame.valid.even_bounds.1; omega
  have hD : 1 ≤ frame.parents.odd.den := by have := frame.valid.odd_bounds.1; omega
  have hT : 0 < frame.child.periodDenominator := by omega
  have hd_pos : 0 < frame.child.den := by omega
  have hLC := frame.parentC_mul_L
  have hdC := frame.parentC_mul_den
  unfold ChildFrame.closedPolygon
  simp only [Set.mem_setOf_eq, if_pos hev]
  rw [seed_t, seed_s]
  refine ⟨by omega, by omega, ?_⟩
  rcases frame.eps_unit with h | h
  · have hW := phaseW_pos frame h
    have hK : seedK frame = 1 - (frame.parents.odd.den + frame.parents.odd.num) := by
      unfold seedK; rw [hW, h]; ring
    rw [h, hK]
    rw [h] at hLC hdC
    have hC0 : 0 ≤ frame.parentC := by
      nlinarith [mul_nonneg (show (0:ℤ) ≤ frame.parents.odd.den - 1 by omega) hT.le]
    have key1' : frame.child.den * (2 * frame.parentC + 2 * frame.child.num) ≤
        frame.child.den * frame.child.periodDenominator := by
      nlinarith [mul_nonneg (show (0:ℤ) ≤ frame.child.den - 2 * frame.parents.odd.den - 1 by omega) hT.le,
        mul_nonneg (show (0:ℤ) ≤ frame.child.den - frame.child.num by omega)
          (show (0:ℤ) ≤ frame.child.den + frame.child.num - 2 by omega)]
    have key1 := le_of_mul_le_mul_left key1' hd_pos
    constructor <;> nlinarith
  · have hW := phaseW_neg frame h
    have hK : seedK frame = -(frame.parents.odd.den + frame.parents.odd.num) := by
      unfold seedK; rw [hW, h]; ring
    rw [h, hK]
    rw [h] at hLC hdC
    have hn_le : frame.child.num * frame.child.den ≤ frame.child.den * frame.parentC := by
      nlinarith [mul_nonneg (show (0:ℤ) ≤ frame.parents.odd.den - 1 by omega) hT.le,
        mul_nonneg (show (0:ℤ) ≤ frame.child.den - frame.child.num by omega)
          (show (0:ℤ) ≤ frame.child.den + frame.child.num - 1 by omega),
        mul_nonneg hd_pos.le (show (0:ℤ) ≤ frame.child.num by omega)]
    have hn := le_of_mul_le_mul_left (by linarith [hn_le] : frame.child.den * frame.child.num ≤
      frame.child.den * frame.parentC) hd_pos
    have key2' : frame.child.den * (2 * frame.parentC) ≤ frame.child.den * frame.child.periodDenominator := by
      nlinarith [mul_nonneg (show (0:ℤ) ≤ frame.child.den - 2 * frame.parents.odd.den - 1 by omega) hT.le,
        mul_nonneg (show (0:ℤ) ≤ frame.child.den - frame.child.num by omega) hT.le]
    have key2 := le_of_mul_le_mul_left key2' hd_pos
    constructor <;> nlinarith

/-- The even parent's determinant: `N d_q − D n_q = ε`. -/
theorem even_det (frame : ChildFrame) :
    frame.parents.odd.num * frame.parents.even.den - frame.parents.odd.den * frame.parents.even.num = frame.eps := by
  have h1 := frame.eps_eq
  have h2 : frame.child.den = 2 * frame.parents.odd.den + frame.parents.even.den := ZoneI1.child_den_eq frame
  have h3 : frame.child.num = 2 * frame.parents.odd.num + frame.parents.even.num := ZoneI1.child_num_eq frame
  linear_combination (-1 : ℤ) * h1 + (-frame.parents.odd.num) * h2 + frame.parents.odd.den * h3

theorem sheetShift_eq (frame : ChildFrame) :
    frame.sheetShift = ((1 - frame.phaseW) * frame.parents.even.den, (1 - frame.phaseW) * frame.parents.even.num) :=
  rfl

/-- The parent shift `lv = (1 − W)(d_q, n_q)` keeps the parity (`d_q + n_q` is even). -/
theorem shift_even_site (frame : ChildFrame) (z : Site) (hz : EvenSite z) :
    EvenSite (z - frame.sheetShift) := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, frame.parents.even.den + frame.parents.even.num = 2 * m := by
    have h2 : frame.child.den = 2 * frame.parents.odd.den + frame.parents.even.den := ZoneI1.child_den_eq frame
    have h3 : frame.child.num = 2 * frame.parents.odd.num + frame.parents.even.num := ZoneI1.child_num_eq frame
    have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
    exact ⟨(frame.parents.even.den + frame.parents.even.num) / 2, by omega⟩
  obtain ⟨X, hX⟩ : ∃ X : ℤ, frame.sheetShift.1 + frame.sheetShift.2 = 2 * X :=
    ⟨(1 - frame.phaseW) * m, by
      rw [sheetShift_eq frame]
      dsimp only
      linear_combination (1 - frame.phaseW) * hm⟩
  unfold EvenSite at hz ⊢
  simp only [Prod.fst_sub, Prod.snd_sub]
  omega

/-- The odd parent's value at the shifted seed point: `N x₁ − D x₂ = 1 − (D + N)` for `x = z0 − lv`. -/
theorem shifted_level (frame : ChildFrame) :
    frame.parents.odd.num * (seedPoint frame - frame.sheetShift).1 -
      frame.parents.odd.den * (seedPoint frame - frame.sheetShift).2 =
      1 - (frame.parents.odd.den + frame.parents.odd.num) := by
  have hT := seed_tp frame
  have hD := even_det frame
  have hK : seedK frame = 1 - (frame.parents.odd.den + frame.parents.odd.num) +
      (1 - frame.phaseW) * frame.eps := rfl
  rw [hK] at hT
  rw [sheetShift_eq frame]
  simp only [Prod.fst_sub, Prod.snd_sub]
  linear_combination hT - (1 - frame.phaseW) * hD

/-- **The level is one orbit of the zero-character period.** Every even site with `t = t(z0)` is `z0 + k U`, `U = (d, n)`
(`gcd(n, d) = 1`). -/
theorem level_shift (frame : ChildFrame) (z : Site)
    (hz : frame.tGrade z = frame.tGrade (seedPoint frame)) :
    ∃ k : ℤ, z = seedPoint frame + k • frame.child.modifiedDeck.kernel := by
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  have hc : IsCoprime frame.child.num frame.child.den := frame.child_reduced
  have hker : frame.child.modifiedDeck.kernel = (frame.child.den, frame.child.num) :=
    frame.child_modifiedDeck_kernel
  have hz' : frame.child.num * z.1 - frame.child.den * z.2 =
      frame.child.num * (seedPoint frame).1 - frame.child.den * (seedPoint frame).2 := hz
  have hEq : frame.child.num * (z.1 - (seedPoint frame).1) =
      frame.child.den * (z.2 - (seedPoint frame).2) := by
    linear_combination hz'
  have hdvd : frame.child.den ∣ frame.child.num * (z.1 - (seedPoint frame).1) :=
    ⟨z.2 - (seedPoint frame).2, hEq⟩
  have hk1 : frame.child.den ∣ (z.1 - (seedPoint frame).1) :=
    (IsCoprime.symm hc).dvd_of_dvd_mul_left hdvd
  obtain ⟨k, hk⟩ := hk1
  have hd0 : frame.child.den ≠ 0 := by omega
  have hk2 : frame.child.den * (z.2 - (seedPoint frame).2 - frame.child.num * k) = 0 := by
    linear_combination (-1 : ℤ) * hEq + frame.child.num * hk
  have hk3 : z.2 - (seedPoint frame).2 = frame.child.num * k := by
    rcases mul_eq_zero.1 hk2 with h | h
    · exact absurd h hd0
    · linarith
  refine ⟨k, ?_⟩
  rw [hker]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_mk, smul_eq_mul]
    linarith
  · simp only [Prod.snd_add, Prod.smul_mk, smul_eq_mul]
    linarith

/-- **The even seed of a word from its parent's odd seed (PAIR_INDUCTION, even child).** Inputs: the inherited seeds of the
conjugate word (`hpar`, the odd parent's zero, the parent's `t_p = 1 − (D+N)` line), the child's period `U` with zero
character (`hG`), the sheet minimum on `E` (`hM`, `standardField_eq_sheetMin`) and the sign of the second branch
at the seed point (`hC`, PAIR_INDUCTION `fC = 1`, exception `0`). The seed point is in `E` (`seed_mem`), so
`F(z0) = min(A(z0), C(z0)) = min(0, C(z0)) = 0`, and the level is one `U`-orbit. -/
theorem even_zero_of_parent {w : Word} (hproper : ∃ x ∈ w, x ≠ Digit.three)
    (hpar : SeedFields (conjWord w))
    (hG : HasGeneratorPeriods (frameAt w).child (standardField w) 0 (frameAt w).coherentConstantV)
    (hM : RespectsPeriodsOn (frameAt w).child (frameAt w).coherentConstantU (frameAt w).coherentConstantV
      (frameAt w).closedPolygon ((frameAt w).sheetMin (quarterTurnField (standardField (conjWord w)))))
    (hC : 0 ≤ (frameAt w).sheetC (quarterTurnField (standardField (conjWord w))) (seedPoint (frameAt w))) :
    ∀ z : Site, EvenSite z →
      (frameAt w).tGrade z = 2 - ((frameAt w).child.den + (frameAt w).child.num) → standardField w z = 0 := by
  have hEq := standardField_eq_sheetMin hproper (seed_mem (frameAt w)) hM
  have hA : (frameAt w).sheetA (quarterTurnField (standardField (conjWord w))) (seedPoint (frameAt w)) = 0 := by
    unfold ChildFrame.sheetA
    apply hpar.odd_zero
    · exact shift_even_site (frameAt w) _ (seed_even (frameAt w))
    · rw [parentN_conjWord hproper, parentD_conjWord hproper]
      exact shifted_level (frameAt w)
  have hF0 : standardField w (seedPoint (frameAt w)) = 0 := by
    rw [hEq]
    unfold ChildFrame.sheetMin
    rw [hA]
    exact min_eq_left hC
  intro z _ hz
  have hlev : (frameAt w).tGrade z = (frameAt w).tGrade (seedPoint (frameAt w)) := by
    rw [hz, seed_t]
  obtain ⟨k, hk⟩ := level_shift (frameAt w) z hlev
  have hper : Function.Periodic (standardField w) (frameAt w).child.modifiedDeck.kernel :=
    fun site => by simpa using hG.1 site
  rw [hk, (hper.zsmul k) (seedPoint (frameAt w)), hF0]

end FLatticePaper.W1Seeds
