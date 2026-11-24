import FLatticePaper.Plane.Induction.TwosZeroStrip
import FLatticePaper.Plane.Induction.TwosPriceE
import FLatticePaper.Plane.Induction.W1ZeroStrip

/-! Task 72 / twos base: the even zero line `zeroEvenLine` of `StrongResidual (2^(k+1))`, from `zeroEvenLine_field`.

The odd seed `hseed` (`F w = harmonicGrid w` on the odd line `sGrade = 2 − 3·den + num`, i.e. `d x₁ + x₂ = −d−1` with `d = 2k+4`)
reduces to one point, as in w2's `standardField_threes_harmonic_seed`:

* the odd line is `w₀ + ℤ·V` with `w₀ = (0, −(2k+5))` and `V = (−2, 2d)` the transverse period (`twos_odd_line`);
* `F − harmonicGrid` is `V`-invariant: both change by `cV − t(w)` under `V` (`twos_G_transverse`), with `t` the transverse grade;
* at the seed `F w₀ = harmonicGrid w₀ = −(k+2)²`, computed through the period `U+V` and the tile identity (`twos_seed_value`). -/

namespace FLatticePaper.Induction
open Farey Construction

/-- `harmonicGrid` shifts by `(d−1) x₁ − (d+1) x₂ + cV` under `V = (−2, 2d)`, with `cV = 1 − d² − 3d`. -/
theorem twos_harm_transverse (k : ℕ) (w : Site) :
    harmonicGrid (w + (-2, 4 * (k : ℤ) + 8)) =
      harmonicGrid w + ((2 * (k : ℤ) + 3) * w.1 - (2 * (k : ℤ) + 5) * w.2 +
        (1 - (2 * (k : ℤ) + 4) ^ 2 - 3 * (2 * (k : ℤ) + 4))) := by
  obtain ⟨w1, w2⟩ := w
  unfold harmonicGrid
  simp only [Prod.mk_add_mk]
  have hp : (w1 + -2 + (w2 + (4 * (k : ℤ) + 8))) % 2 = (w1 + w2) % 2 := by omega
  rw [hp]
  have hpoly : (w1 + -2) ^ 2 + 2 * (w1 + -2) * (w2 + (4 * (k : ℤ) + 8)) - (w2 + (4 * (k : ℤ) + 8)) ^ 2 -
      2 * (w2 + (4 * (k : ℤ) + 8)) - (w1 + w2) % 2 =
      (w1 ^ 2 + 2 * w1 * w2 - w2 ^ 2 - 2 * w2 - (w1 + w2) % 2) +
        4 * ((2 * (k : ℤ) + 3) * w1 - (2 * (k : ℤ) + 5) * w2 +
          (1 - (2 * (k : ℤ) + 4) ^ 2 - 3 * (2 * (k : ℤ) + 4))) := by
    ring
  rw [hpoly, Int.add_mul_ediv_left _ _ (by norm_num : (4 : ℤ) ≠ 0)]

/-- `F − harmonicGrid` is invariant under the transverse period `V`. -/
theorem twos_G_transverse (k : ℕ) (w : Site) :
    standardField (List.replicate (k + 1) Digit.two) (w + (-2, 4 * (k : ℤ) + 8)) -
        harmonicGrid (w + (-2, 4 * (k : ℤ) + 8)) =
      standardField (List.replicate (k + 1) Digit.two) w - harmonicGrid w := by
  have hT := period_transverse_apply (twos_standardField_hasPeriods k) w
  rw [twos_transverse_explicit, twos_transverseGrade_explicit, ladderEvenConstantV_eq] at hT
  rw [twos_harm_transverse, hT]
  ring

/-- `F − harmonicGrid` is constant on the whole transverse orbit `w₀ + ℤ·V`. -/
theorem twos_G_orbit (k : ℕ) (n : ℤ) :
    standardField (List.replicate (k + 1) Digit.two)
        ((0, -(2 * (k : ℤ) + 5)) + (n * (-2), n * (4 * (k : ℤ) + 8))) -
      harmonicGrid ((0, -(2 * (k : ℤ) + 5)) + (n * (-2), n * (4 * (k : ℤ) + 8))) =
    standardField (List.replicate (k + 1) Digit.two) (0, -(2 * (k : ℤ) + 5)) -
      harmonicGrid (0, -(2 * (k : ℤ) + 5)) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have e : (0, -(2 * (k : ℤ) + 5)) + (((i : ℤ) + 1) * (-2), ((i : ℤ) + 1) * (4 * (k : ℤ) + 8)) =
        ((0, -(2 * (k : ℤ) + 5)) + ((i : ℤ) * (-2), (i : ℤ) * (4 * (k : ℤ) + 8))) + (-2, 4 * (k : ℤ) + 8) := by
      rw [Prod.mk_add_mk, Prod.mk_add_mk, Prod.mk_add_mk]
      congr 1 <;> ring
    rw [e, twos_G_transverse, ih]
  | pred i ih =>
    have e : (0, -(2 * (k : ℤ) + 5)) + ((-(i : ℤ) - 1) * (-2), (-(i : ℤ) - 1) * (4 * (k : ℤ) + 8)) +
        (-2, 4 * (k : ℤ) + 8) = (0, -(2 * (k : ℤ) + 5)) + (-(i : ℤ) * (-2), -(i : ℤ) * (4 * (k : ℤ) + 8)) := by
      rw [Prod.mk_add_mk, Prod.mk_add_mk, Prod.mk_add_mk]
      congr 1 <;> ring
    rw [← ih, ← e, twos_G_transverse]

/-- The harmonic value at the seed `w₀ = (0, −(2k+5))`: `harmonicGrid w₀ = −(k+2)²`. -/
theorem twos_harm_seed (k : ℕ) : harmonicGrid (0, -(2 * (k : ℤ) + 5)) = -((k : ℤ) + 2) ^ 2 := by
  have hp : ((0 : ℤ) + -(2 * (k : ℤ) + 5)) % 2 = 1 := by omega
  have hval : harmonicGrid (0, -(2 * (k : ℤ) + 5)) =
      ((0 : ℤ) ^ 2 + 2 * 0 * (-(2 * (k : ℤ) + 5)) - (-(2 * (k : ℤ) + 5)) ^ 2 - 2 * (-(2 * (k : ℤ) + 5)) -
        ((0 : ℤ) + -(2 * (k : ℤ) + 5)) % 2) / 4 := rfl
  rw [hval, hp]
  apply Int.ediv_eq_of_eq_mul_right (by norm_num)
  ring

set_option maxHeartbeats 400000 in
/-- **The seed value.** `F(w₀) = −(k+2)²`, through `w₀ + U` and `w₁ = w₀ + U + V` (in the tile). -/
theorem twos_seed_value (k : ℕ) :
    standardField (List.replicate (k + 1) Digit.two) (0, -(2 * (k : ℤ) + 5)) = -((k : ℤ) + 2) ^ 2 := by
  have hP := twos_standardField_hasPeriods k
  have hK := period_kernel_apply hP (0, -(2 * (k : ℤ) + 5))
  rw [twos_kernel_explicit] at hK
  have e1 : (0, -(2 * (k : ℤ) + 5)) + (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3) = (2 * (k : ℤ) + 5, -2) := by
    rw [Prod.mk_add_mk]
    congr 1 <;> ring
  rw [e1] at hK
  have hT := period_transverse_apply hP (2 * (k : ℤ) + 5, -2)
  rw [twos_transverse_explicit, twos_transverseGrade_explicit, ladderEvenConstantV_eq] at hT
  have e2 : (2 * (k : ℤ) + 5, -2) + (-2, 4 * (k : ℤ) + 8) = (2 * (k : ℤ) + 3, 4 * (k : ℤ) + 6) := by
    rw [Prod.mk_add_mk]
    congr 1 <;> ring
  rw [e2] at hT
  dsimp only at hT
  have hxt : (2 * (k : ℤ) + 3, 4 * (k : ℤ) + 7) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
    simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
      Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Prod.mk.injEq, not_or]
    omega
  have hF1 := standardField_twos_eq_tile k (w := (2 * (k : ℤ) + 3, 4 * (k : ℤ) + 6))
    (x := (2 * (k : ℤ) + 3, 4 * (k : ℤ) + 7)) (by ext <;> (dsimp only; try ring)) hxt
  have hpn : paperNearLadderValue (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 3, 4 * (k : ℤ) + 7) =
      -((k : ℤ) + 2) ^ 2 - 2 * (k : ℤ) - 2 := by
    unfold paperNearLadderValue
    dsimp only
    have hq : (4 * (k : ℤ) + 7 - (2 * (k : ℤ) + 3)) ^ 2 / 4 = ((k : ℤ) + 2) ^ 2 := by
      rw [show 4 * (k : ℤ) + 7 - (2 * (k : ℤ) + 3) = 2 * ((k : ℤ) + 2) by ring, mul_pow,
        show (2 : ℤ) ^ 2 = 4 by norm_num, Int.mul_ediv_cancel_left _ (by norm_num)]
    rw [hq]
    simp only [min_def, max_def, Set.indicator_apply, Set.mem_union, paperNearLadderA, paperNearLadderB,
      Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
    split_ifs <;> omega
  have hval := twos_harm_seed k
  linear_combination -hK - hT + hF1 + hpn

/-- The odd seed line `d x₁ + x₂ = −d−1` (`d = 2k+4`) is the orbit `w₀ + ℤ·V`. -/
theorem twos_odd_line (k : ℕ) (w : Site) (hw : ¬ FLatticePaper.EvenSite w)
    (hs : (frameAt (List.replicate (k + 1) Digit.two)).sGrade w =
      2 - 3 * (frameAt (List.replicate (k + 1) Digit.two)).child.den +
        (frameAt (List.replicate (k + 1) Digit.two)).child.num) :
    ∃ m : ℤ, w = (0, -(2 * (k : ℤ) + 5)) + (-m * (-2), -m * (4 * (k : ℤ) + 8)) := by
  obtain ⟨hn, hd⟩ := twos_child_num_den k
  unfold ChildFrame.sGrade at hs
  rw [hn, hd] at hs
  have hs' : 4 * ((k : ℤ) * w.1) + 8 * w.1 + 2 * w.2 = -4 * (k : ℤ) - 10 := by linear_combination hs
  unfold FLatticePaper.EvenSite at hw
  have hm0 : w.1 % 2 = 0 := by omega
  obtain ⟨m, hm'⟩ : ∃ m, w.1 = 2 * m := ⟨w.1 / 2, by omega⟩
  have hkm : (k : ℤ) * w.1 = 2 * (k : ℤ) * m := by rw [hm']; ring
  have h2 : 2 * w.2 = 2 * (-(2 * (k : ℤ) + 5) + (-m) * (4 * (k : ℤ) + 8)) := by
    linear_combination hs' - 4 * hkm - 8 * hm'
  have hw2 : w.2 = -(2 * (k : ℤ) + 5) + (-m) * (4 * (k : ℤ) + 8) := by omega
  refine ⟨m, ?_⟩
  ext
  · simp only [Prod.fst_add]
    rw [hm']
    ring
  · simp only [Prod.snd_add]
    rw [hw2]

set_option maxHeartbeats 400000 in
/-- **The odd seed of `2^(k+1)`**: `F w = harmonicGrid w` on the odd line `sGrade = 2 − 3·den + num`. -/
theorem twos_hseed (k : ℕ) : ∀ w : Site, ¬ FLatticePaper.EvenSite w →
    (frameAt (List.replicate (k + 1) Digit.two)).sGrade w =
      2 - 3 * (frameAt (List.replicate (k + 1) Digit.two)).child.den +
        (frameAt (List.replicate (k + 1) Digit.two)).child.num →
      standardField (List.replicate (k + 1) Digit.two) w = harmonicGrid w := by
  intro w hw hs
  obtain ⟨m, rfl⟩ := twos_odd_line k w hw hs
  have hG := twos_G_orbit k (-m)
  rw [twos_seed_value, twos_harm_seed] at hG
  linarith

/-- **The even zero line of `2^(k+1)`**, from `zeroEvenLine_field` with the twos packet, the price range and the drifts, and the seed. -/
theorem twos_zeroEvenLine (k : ℕ) : ∀ x : Site, (x.1 + x.2) % 2 = 0 →
    parentN (List.replicate (k + 1) Digit.two) * x.1 - parentD (List.replicate (k + 1) Digit.two) * x.2 =
        -parentD (List.replicate (k + 1) Digit.two) →
      quarterTurnField (standardField (List.replicate (k + 1) Digit.two)) x = 0 :=
  FLatticePaper.W1ZeroStrip.zeroEvenLine_field (List.replicate (k + 1) Digit.two)
    (twos_packet_standard k (fun _ hz ht => twos_zero_strip k hz ht) (fun _ hz hs => twos_harm_strip k hz hs))
    (fun z hz => twos_priceRange_E k z hz)
    (fun z => by have := twos_price_drift_kernel k z; linarith)
    (fun z => by have := twos_price_drift_transverse k z; linarith)
    (twos_hseed k)

end FLatticePaper.Induction
