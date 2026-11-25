import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.Sheets
import FLatticePaper.Plane.Induction.Q3Field
import FLatticePaper.Plane.Induction.W1Strips
import FLatticePaper.Plane.Induction.PriceDeck
import Mathlib.RingTheory.Coprime.Basic

/-! # The sheet monotonicities of the cap, from the signed comparison (ALL_SLOPE_STEP; Q26)

The single named input is the signed comparison on the closed polygon with `σ = shortShift` (`t(σ) = −2`):
`F w − F (w − σ) ≤ 0` for `w ∈ closedPolygon` (Q26 (1), `D_−`). Everything else is proved here:

* `−T < t` on the closed polygon (`tGrade_gt_of_mem`), from its explicit inequalities (Q26 (2), first bound);
* the generator periods: `F (x + U) = F x` (the constant `c_U` vanishes), `F (x + V) = F x + t x + c_V`;
* the coverage `z = y + iU + jV` with `y ∈ E` (`closedPolygon_covers`) gives `D_− z ≤ 0` for all `z` with `t z ≤ 0`
  (Q26 (3), step two: `D_−` is fixed by `U`, drops by `2` under `V`, and `j ≥ 0` when `t z ≤ 0`);
* the chain `F u ≤ F (u − σ)` along a parity class gives the monotonicity on each sheet (Q26, `SheetMono`, `SheetMonoOdd`). -/

namespace FLatticePaper.SheetMonoChild

open Farey FLatticePaper FLatticePaper.Induction

/-- The kernel displacement `i·(D, N)`. -/
def kPt (frame : ChildFrame) (i : ℤ) : Site := (i * frame.child.den, i * frame.child.num)

/-- The transverse displacement `j·V`, `V = (N−D, N+D)`. -/
def vPt (frame : ChildFrame) (j : ℤ) : Site :=
  (j * (frame.child.num - frame.child.den), j * (frame.child.num + frame.child.den))

theorem periodMult_one (frame : ChildFrame) : frame.child.periodMultiplicity = 1 := by
  unfold Fraction.periodMultiplicity
  exact if_pos frame.child_even

theorem kernel_eq (frame : ChildFrame) :
    frame.child.modifiedDeck.kernel = (frame.child.den, frame.child.num) := by
  unfold Fraction.modifiedDeck
  simp only [periodMult_one frame, one_mul]

theorem transverse_eq (frame : ChildFrame) :
    frame.child.modifiedDeck.transverse
      = (frame.child.num - frame.child.den, frame.child.num + frame.child.den) := by
  unfold Fraction.modifiedDeck Fraction.unmodifiedDeck
  simp only

theorem kernel_eq_kPt (frame : ChildFrame) : frame.child.modifiedDeck.kernel = kPt frame 1 := by
  rw [kernel_eq frame]
  ext <;> simp [kPt]

theorem transverse_eq_vPt (frame : ChildFrame) : frame.child.modifiedDeck.transverse = vPt frame 1 := by
  rw [transverse_eq frame]
  ext <;> simp [vPt]

theorem combine_eq (frame : ChildFrame) (i j : ℤ) :
    frame.child.modifiedDeck.combine i j = kPt frame i + vPt frame j := by
  unfold PeriodDeck.combine
  rw [kernel_eq_kPt frame, transverse_eq_vPt frame]
  ext <;> simp [kPt, vPt]

theorem sm_tG_sub (frame : ChildFrame) (a b : Site) :
    frame.tGrade (a - b) = frame.tGrade a - frame.tGrade b := by
  unfold ChildFrame.tGrade
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

theorem sm_tG_add (frame : ChildFrame) (a b : Site) :
    frame.tGrade (a + b) = frame.tGrade a + frame.tGrade b := by
  unfold ChildFrame.tGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem sm_tG_smul (frame : ChildFrame) (n : ℤ) (a : Site) :
    frame.tGrade (n * a.1, n * a.2) = n * frame.tGrade a := by
  unfold ChildFrame.tGrade
  ring

/-- The strict lower bound `−T < t` on the closed polygon (Q26 (2), first bound). -/
theorem tGrade_gt_of_mem (frame : ChildFrame) {y : Site} (hy : y ∈ frame.closedPolygon) :
    -frame.child.periodDenominator < frame.tGrade y := by
  obtain ⟨h1, -, -⟩ := frame.child_facts
  unfold ChildFrame.closedPolygon at hy
  simp only [Set.mem_setOf_eq] at hy
  split_ifs at hy with he
  · omega
  · omega

/-- The sites of a parity class differ by an even `t`-amount. -/
theorem tGrade_diff_even (frame : ChildFrame) (u v : Site)
    (hpar : (u.1 + u.2) % 2 = (v.1 + v.2) % 2) :
    ∃ m : ℤ, frame.tGrade v - frame.tGrade u = 2 * m := by
  obtain ⟨α, β, hα, hβ⟩ := FLatticePaper.PriceDeck.child_odd_witness frame
  obtain ⟨r, hr⟩ : ∃ r : ℤ, (v.1 + v.2) - (u.1 + u.2) = 2 * r :=
    ⟨((v.1 + v.2) - (u.1 + u.2)) / 2, by omega⟩
  refine ⟨α * (v.1 - u.1) - β * (v.2 - u.2) - (v.2 - u.2) + r, ?_⟩
  unfold ChildFrame.tGrade
  rw [hα, hβ]
  linear_combination hr

/-- `F (x + U) = F x`: the kernel period has constant zero. -/
theorem F_U {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (x : Site) :
    F (x + kPt frame 1) = F x := by
  have h := hP.periods.1 x
  rw [kernel_eq_kPt frame, FLatticePaper.Induction.coherentConstantU_eq_zero frame] at h
  simpa using h

/-- `F (x + V) = F x + t x + c_V`: the transverse period. -/
theorem F_V {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (x : Site) :
    F (x + vPt frame 1) = F x + frame.tGrade x + frame.coherentConstantV := by
  have h := hP.periods.2 x
  rw [transverse_eq_vPt frame] at h
  rw [h]
  simp only [Fraction.transverseGrade, ChildFrame.tGrade]
  ring

/-- Integer multiples of `U` are periods of `F`. -/
theorem F_Kpt {F : Field} (frame : ChildFrame) (hP : frame.Packet F) :
    ∀ (i : ℤ) (y : Site), F (y + kPt frame i) = F y := by
  intro i
  refine Int.induction_on i ?_ ?_ ?_
  · intro y
    have e : kPt frame 0 = 0 := by ext <;> simp [kPt]
    rw [e, add_zero]
  · intro k ih y
    have e : kPt frame ((k : ℤ) + 1) = kPt frame k + kPt frame 1 := by
      ext <;> simp [kPt] <;> ring
    rw [e, ← add_assoc, F_U frame hP, ih y]
  · intro k ih y
    have e : y + kPt frame (-(k : ℤ) - 1) + kPt frame 1 = y + kPt frame (-(k : ℤ)) := by
      ext <;> simp [kPt] <;> ring
    have h := F_U frame hP (y + kPt frame (-(k : ℤ) - 1))
    rw [e, ih y] at h
    exact h.symm

/-- The vertical step of `D_− = F z − F (z − σ)`: it drops by `2` under `V` (`t σ = −2`). -/
theorem D_shift_V {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (x : Site) :
    F (x + vPt frame 1) - F (x + vPt frame 1 - frame.shortShift)
      = (F x - F (x - frame.shortShift)) - 2 := by
  have e : x + vPt frame 1 - frame.shortShift = (x - frame.shortShift) + vPt frame 1 := by abel
  rw [e, F_V frame hP x, F_V frame hP (x - frame.shortShift)]
  have h1 := sm_tG_sub frame x frame.shortShift
  have h2 := FLatticePaper.W1Strips.tGrade_shortShift frame
  linarith

/-- `D_−` after `j ≥ 0` vertical steps. -/
theorem D_shift_nat {F : Field} (frame : ChildFrame) (hP : frame.Packet F) :
    ∀ (n : ℕ) (y : Site),
      F (y + vPt frame (n : ℤ)) - F (y + vPt frame (n : ℤ) - frame.shortShift)
        = (F y - F (y - frame.shortShift)) - 2 * (n : ℤ) := by
  intro n
  induction n with
  | zero =>
    intro y
    have e : vPt frame ((0 : ℕ) : ℤ) = 0 := by ext <;> simp [vPt]
    rw [e]
    simp
  | succ k ih =>
    intro y
    have e : vPt frame ((k + 1 : ℕ) : ℤ) = vPt frame (k : ℤ) + vPt frame 1 := by
      ext <;> simp [vPt] <;> ring
    have e2 : y + vPt frame ((k + 1 : ℕ) : ℤ) = (y + vPt frame (k : ℤ)) + vPt frame 1 := by
      rw [e]; abel
    rw [e2, D_shift_V frame hP (y + vPt frame (k : ℤ)), ih y]
    push_cast
    ring

/-- **Step two** (Q26 (3)): `D_− z ≤ 0` for every `z` with `t z ≤ 0`, from the signed comparison on the polygon. -/
theorem D_nonpos_of_tGrade_le {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    (z : Site) (hz : frame.tGrade z ≤ 0) :
    F z - F (z - frame.shortShift) ≤ 0 := by
  obtain ⟨y, hy, i, j, hzeq⟩ := frame.closedPolygon_covers z
  obtain ⟨-, -, -, -, hT⟩ := frame.child_facts
  obtain ⟨h1, h2, -⟩ := frame.child_facts
  have hTpos : 0 < frame.child.periodDenominator := by
    rw [hT]
    nlinarith
  have ht : frame.tGrade (kPt frame i + vPt frame j) = -(j * frame.child.periodDenominator) := by
    simp only [ChildFrame.tGrade, Prod.fst_add, Prod.snd_add, kPt, vPt]
    rw [hT]
    ring
  have htz : frame.tGrade z = frame.tGrade y - j * frame.child.periodDenominator := by
    rw [hzeq, combine_eq frame, sm_tG_add, ht]
    ring
  have hy' := tGrade_gt_of_mem frame hy
  have hj : 0 ≤ j := by
    by_contra hneg
    have hneg' : j < 0 := not_le.mp hneg
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ -1 - j by omega) hTpos.le]
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = (n : ℤ) := ⟨j.toNat, (Int.toNat_of_nonneg hj).symm⟩
  have hz2 : z = (y + vPt frame (n : ℤ)) + kPt frame i := by
    rw [hzeq, combine_eq frame]
    abel
  rw [hz2]
  have e2 : (y + vPt frame (n : ℤ)) + kPt frame i - frame.shortShift
      = (y + vPt frame (n : ℤ) - frame.shortShift) + kPt frame i := by abel
  rw [e2, F_Kpt frame hP i, F_Kpt frame hP i, D_shift_nat frame hP n y]
  have hw := hsig y hy
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := Nat.cast_nonneg n
  linarith

/-- The kernel of `t` on the lattice is `kPt`: `t Δ = 0` forces `Δ = kPt k` (the child is reduced). -/
theorem kernel_of_tGrade_zero (frame : ChildFrame) (Δ : Site) (h : frame.tGrade Δ = 0) :
    ∃ k : ℤ, Δ = kPt frame k := by
  obtain ⟨-, hn2, -⟩ := frame.child_facts
  obtain ⟨h1, -, -⟩ := frame.child_facts
  have hcop : IsCoprime frame.child.den frame.child.num := IsCoprime.symm frame.child_reduced
  have hd : frame.child.den ≠ 0 := by omega
  have hdvd : frame.child.den ∣ Δ.1 := by
    have h' : frame.child.den ∣ Δ.1 * frame.child.num := by
      refine ⟨Δ.2, ?_⟩
      unfold ChildFrame.tGrade at h
      linear_combination h
    exact hcop.dvd_of_dvd_mul_right h'
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨k, ?_⟩
  unfold ChildFrame.tGrade at h
  apply Prod.ext
  · simp only [kPt]
    rw [hk]
    ring
  · simp only [kPt]
    apply mul_left_cancel₀ hd
    linear_combination (-1 : ℤ) * h + frame.child.num * hk

/-- The chain: `F u ≤ F (u − n σ)` while the `t`-grades stay `≤ 0` before the last step. -/
theorem chain_step {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0) :
    ∀ (n : ℕ) (u : Site), frame.tGrade u + 2 * (n : ℤ) ≤ 2 →
      F u ≤ F (u - ((n : ℤ) * frame.shortShift.1, (n : ℤ) * frame.shortShift.2)) := by
  intro n
  induction n with
  | zero =>
    intro u _
    simp only [Nat.cast_zero, zero_mul, Prod.mk_zero_zero, sub_zero, le_refl]
  | succ k ih =>
    intro u hu
    push_cast at hu
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := Nat.cast_nonneg k
    have hD := D_nonpos_of_tGrade_le frame hP hsig u (by linarith)
    have hstep : F u ≤ F (u - frame.shortShift) := by linarith
    have hσ := FLatticePaper.W1Strips.tGrade_shortShift frame
    have hu' : frame.tGrade (u - frame.shortShift) + 2 * (k : ℤ) ≤ 2 := by
      rw [sm_tG_sub frame, hσ]
      linarith
    have h2 := ih (u - frame.shortShift) hu'
    have e : u - frame.shortShift - ((k : ℤ) * frame.shortShift.1, (k : ℤ) * frame.shortShift.2)
        = u - (((k + 1 : ℕ) : ℤ) * frame.shortShift.1, ((k + 1 : ℕ) : ℤ) * frame.shortShift.2) := by
      ext <;> simp <;> ring
    rw [e] at h2
    exact hstep.trans h2

/-- **The monotonicity on one parity class** (Q26): `t u ≤ t v ≤ 0` and `u, v` of the same parity give `F u ≤ F v`. -/
theorem sheet_mono_signed {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    (u v : Site) (hpar : (u.1 + u.2) % 2 = (v.1 + v.2) % 2)
    (hu : frame.tGrade u ≤ frame.tGrade v) (hv : frame.tGrade v ≤ 0) :
    F u ≤ F v := by
  obtain ⟨m, hm⟩ := tGrade_diff_even frame u v hpar
  have hm0 : 0 ≤ m := by linarith
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = (n : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg hm0).symm⟩
  have hσ := FLatticePaper.W1Strips.tGrade_shortShift frame
  set w : Site := u - ((n : ℤ) * frame.shortShift.1, (n : ℤ) * frame.shortShift.2) with hw
  have htw : frame.tGrade w = frame.tGrade v := by
    rw [hw, sm_tG_sub frame, sm_tG_smul frame, hσ]
    linarith
  have h1 : F u ≤ F w := chain_step frame hP hsig n u (by linarith)
  have hΔ : frame.tGrade (v - w) = 0 := by
    rw [sm_tG_sub frame, htw, sub_self]
  obtain ⟨k, hk⟩ := kernel_of_tGrade_zero frame (v - w) hΔ
  have hv' : v = w + kPt frame k := by
    rw [add_comm]
    exact sub_eq_iff_eq_add.mp hk
  have hFv : F v = F w := by
    rw [hv']
    exact F_Kpt frame hP k w
  exact h1.trans (le_of_eq hFv.symm)

/-- **`SheetMono`, the even sheet** (Q26): derived from the signed comparison. -/
theorem sheetMono_even_of_signed {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0) :
    ∀ u v : Site, EvenSite u → EvenSite v → frame.tGrade u ≤ frame.tGrade v →
      frame.tGrade v ≤ 0 → F u ≤ F v := by
  intro u v hu hv h1 h2
  exact sheet_mono_signed frame hP hsig u v (by unfold EvenSite at hu hv; omega) h1 h2

/-- **`SheetMonoOdd`, the odd sheet** (Q26): derived from the signed comparison. -/
theorem sheetMono_odd_of_signed {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0) :
    ∀ u v : Site, ¬ EvenSite u → ¬ EvenSite v → frame.tGrade u ≤ frame.tGrade v →
      frame.tGrade v ≤ 0 → F u ≤ F v := by
  intro u v hu hv h1 h2
  exact sheet_mono_signed frame hP hsig u v (by unfold EvenSite at hu hv; omega) h1 h2

/-- The slip difference `F x − F (x + σ)` rises by `2` under one `V` (`t σ = −2`). -/
theorem slip1_V {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (x : Site) :
    F (x + vPt frame 1) - F (x + vPt frame 1 + frame.shortShift)
      = (F x - F (x + frame.shortShift)) + 2 := by
  have e : x + vPt frame 1 + frame.shortShift = (x + frame.shortShift) + vPt frame 1 := by abel
  rw [e, F_V frame hP x, F_V frame hP (x + frame.shortShift)]
  have h1 := sm_tG_add frame x frame.shortShift
  have h2 := FLatticePaper.W1Strips.tGrade_shortShift frame
  linarith

/-- The slip difference after `n ≥ 0` vertical steps. -/
theorem slip1_nat {F : Field} (frame : ChildFrame) (hP : frame.Packet F) :
    ∀ (n : ℕ) (y : Site),
      F (y + vPt frame (n : ℤ)) - F (y + vPt frame (n : ℤ) + frame.shortShift)
        = (F y - F (y + frame.shortShift)) + 2 * (n : ℤ) := by
  intro n
  induction n with
  | zero =>
    intro y
    have e : vPt frame ((0 : ℕ) : ℤ) = 0 := by ext <;> simp [vPt]
    rw [e]
    simp
  | succ k ih =>
    intro y
    have e : vPt frame ((k + 1 : ℕ) : ℤ) = vPt frame (k : ℤ) + vPt frame 1 := by
      ext <;> simp [vPt] <;> ring
    have e2 : y + vPt frame ((k + 1 : ℕ) : ℤ) = (y + vPt frame (k : ℤ)) + vPt frame 1 := by
      rw [e]; abel
    rw [e2, slip1_V frame hP (y + vPt frame (k : ℤ)), ih y]
    push_cast
    ring

/-- **Step two for the slip** (Q26 (3), the other sign): `F z − F (z + σ) ≥ 0` for every `z` with `t z ≤ 0`, from the slip range on
the closed polygon. The slip range is `StrongEstimates.slipRange` of the word (`slipRange_of_strong`). -/
theorem slip1_nonneg_of_tGrade_le {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hslip : ∀ w ∈ frame.closedPolygon, 0 ≤ F w - F (w + frame.shortShift) ∧ F w - F (w + frame.shortShift) ≤ 2)
    (z : Site) (hz : frame.tGrade z ≤ 0) :
    0 ≤ F z - F (z + frame.shortShift) := by
  obtain ⟨y, hy, i, j, hzeq⟩ := frame.closedPolygon_covers z
  obtain ⟨-, -, -, -, hT⟩ := frame.child_facts
  obtain ⟨h1, h2, -⟩ := frame.child_facts
  have hTpos : 0 < frame.child.periodDenominator := by
    rw [hT]
    nlinarith
  have ht : frame.tGrade (kPt frame i + vPt frame j) = -(j * frame.child.periodDenominator) := by
    simp only [ChildFrame.tGrade, Prod.fst_add, Prod.snd_add, kPt, vPt]
    rw [hT]
    ring
  have htz : frame.tGrade z = frame.tGrade y - j * frame.child.periodDenominator := by
    rw [hzeq, combine_eq frame, sm_tG_add, ht]
    ring
  have hy' := tGrade_gt_of_mem frame hy
  have hj : 0 ≤ j := by
    by_contra hneg
    have hneg' : j < 0 := not_le.mp hneg
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ -1 - j by omega) hTpos.le]
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = (n : ℤ) := ⟨j.toNat, (Int.toNat_of_nonneg hj).symm⟩
  have hz2 : z = (y + vPt frame (n : ℤ)) + kPt frame i := by
    rw [hzeq, combine_eq frame]
    abel
  rw [hz2]
  have e2 : (y + vPt frame (n : ℤ)) + kPt frame i + frame.shortShift
      = (y + vPt frame (n : ℤ) + frame.shortShift) + kPt frame i := by abel
  rw [e2, F_Kpt frame hP i, F_Kpt frame hP i, slip1_nat frame hP n y]
  have hw := hslip y hy
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := Nat.cast_nonneg n
  linarith [hw.1]

/-- **The signed comparison from the slip range** (Q26 (1)): `F w − F (w − σ) ≤ 0` on the closed polygon. Two cases: on the zero
strip (`t w ≥ 1 − D`), both `F w` and `F (w − σ)` vanish; below it (`t w ≤ −D`), `t (w − σ) ≤ 0` and the slip step applies to `w − σ`. -/
theorem hsig_of_slip {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hslip : ∀ w ∈ frame.closedPolygon, 0 ≤ F w - F (w + frame.shortShift) ∧ F w - F (w + frame.shortShift) ≤ 2) :
    ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0 := by
  intro w hw
  obtain ⟨h1, h2, h3⟩ := frame.child_facts
  have hσ := FLatticePaper.W1Strips.tGrade_shortShift frame
  have hsub : frame.tGrade (w - frame.shortShift) = frame.tGrade w + 2 := by
    rw [sm_tG_sub frame, hσ]
    ring
  have hpoly := hw
  unfold ChildFrame.closedPolygon at hpoly
  simp only [Set.mem_setOf_eq] at hpoly
  by_cases hcase : 1 - frame.child.den ≤ frame.tGrade w
  · -- the zero strip at `w` and at `w − σ`
    have hup : frame.tGrade w + 2 ≤ frame.child.num + 2 * frame.child.den - 1 := by
      split_ifs at hpoly with he
      · omega
      · omega
    have hF0 : F w = 0 := hP.strips.1 w hcase (by omega)
    have hF1 : F (w - frame.shortShift) = 0 :=
      hP.strips.1 (w - frame.shortShift) (by rw [hsub]; omega) (by rw [hsub]; omega)
    rw [hF0, hF1]
    norm_num
  · -- `t (w − σ) ≤ 0`: the slip step at `w − σ` gives `F (w − σ) − F w ≥ 0`
    have hz : frame.tGrade (w - frame.shortShift) ≤ 0 := by
      rw [hsub]
      omega
    have hs := slip1_nonneg_of_tGrade_le frame hP hslip (w - frame.shortShift) hz
    rw [sub_add_cancel] at hs
    linarith

end FLatticePaper.SheetMonoChild
