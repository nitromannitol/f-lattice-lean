import FLatticePaper.Plane.Induction.CoveredSW

/-! # Derived inputs of the even H NW-fan square (Q32 C.2)

The fan square `EvenHSquare.parentSquareOut_evenH_NW_fan` took two named inputs, the depth bound `3n − 2 ≤ d` and the apex
bound `n + 2 ≤ t(z+W)`. Both follow from the black corner `z+N` and the free set.

* `num_odd`: `n` is odd (the child fraction is even, so `n + d` is even, and `n`, `d` are coprime).
* `tGrade_mod_two`: `t(x,y) ≡ x + y (mod 2)`, since `n`, `d` are odd.
* `freeH_odd_t_num`: the only free odd H site with `t = n` is `hFirst` (the reduced fraction and the closed polygon).
* `apex_of_ne_hFirst`: a free odd H site other than `hFirst` has `t ≥ n + 2`.
* `depth_of_black_N`: if `d < 3n − 2`, the sites `z`, `z+(0,2)` and `z+(0,1)` lie in the zero windows, so `z+N` is white.
-/

namespace FLatticePaper.FanInputs

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.ShapeOneGeom FLatticePaper.CoveredSW

/-- `n` is odd. -/
theorem num_odd (frame : ChildFrame) : frame.child.num % 2 = 1 := by
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hred : IsCoprime frame.child.num frame.child.den := frame.child_reduced
  by_contra hc
  obtain ⟨p, hp⟩ : ∃ p, frame.child.num = 2 * p := ⟨frame.child.num / 2, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q, frame.child.den = 2 * q := ⟨frame.child.den / 2, by omega⟩
  obtain ⟨a, b, hab⟩ := hred
  rw [hp, hq] at hab
  have h2 : (2 : ℤ) ∣ 1 := ⟨a * p + b * q, by linear_combination -hab⟩
  norm_num at h2

/-- `t(x,y) ≡ x + y (mod 2)`. -/
theorem tGrade_mod_two (frame : ChildFrame) (W : Site) : frame.tGrade W % 2 = (W.1 + W.2) % 2 := by
  have hn := num_odd frame
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  obtain ⟨a, ha⟩ : ∃ a, frame.child.num = 2 * a + 1 := ⟨frame.child.num / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, frame.child.den = 2 * b + 1 := ⟨frame.child.den / 2, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, frame.tGrade W - (W.1 + W.2) = 2 * c := by
    refine ⟨a * W.1 - (b + 1) * W.2, ?_⟩
    unfold ChildFrame.tGrade
    rw [ha, hb]
    ring
  omega

/-- The child denominator is odd too, and the `t` of an H site has the parity of `x + y`. -/
theorem freeH_odd_t_num (frame : ChildFrame) {W : Site} (hW : W ∈ frame.freeH) (hodd : ¬ EvenSite W)
    (ht : frame.tGrade W = frame.child.num) : W = hFirst := by
  have hn := num_odd frame
  have hred : IsCoprime frame.child.num frame.child.den := frame.child_reduced
  obtain ⟨hpoly, -, -⟩ := hW
  obtain ⟨hn1, hnd, hdn2, hd3, hTdef⟩ := frame.child_facts
  rcases (frame.mem_closedPolygon_iff W).mp hpoly with ⟨he, -⟩ | ⟨-, -, -, hs1, hs2⟩
  · exact absurd he hodd
  obtain ⟨x, y⟩ := W
  unfold ChildFrame.tGrade at ht
  unfold ChildFrame.sGrade at hs1 hs2
  dsimp only at ht hs1 hs2
  have hdx : frame.child.den ∣ (x - 1) * frame.child.num := ⟨y, by linear_combination ht⟩
  obtain ⟨k, hk⟩ := (hred.symm).dvd_of_dvd_mul_right hdx
  have hd0 : frame.child.den ≠ 0 := by omega
  have hy : y = frame.child.num * k := by
    apply mul_left_cancel₀ hd0
    linear_combination (-1 : ℤ) * ht + (frame.child.num : ℤ) * hk
  have hx : x = frame.child.den * k + 1 := by linarith
  have hS : (frame.child.den + frame.child.num) * x + (frame.child.den - frame.child.num) * y
      = (frame.child.den + frame.child.num) + k * frame.child.periodDenominator := by
    rw [hTdef, hx, hy]
    ring
  have hTpos : 0 < frame.child.periodDenominator := by
    rw [hTdef]
    nlinarith
  have hk0 : k = 0 := by
    rcases lt_trichotomy k 0 with hneg | hz | hpos
    · exfalso
      have hkT : k * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ -1 - k by omega) hTpos.le]
      have hTbig : 2 * frame.child.den - 2 < frame.child.periodDenominator := by
        rw [hTdef]
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ frame.child.den - frame.child.num - 2 by omega)
          (show (0 : ℤ) ≤ frame.child.den + frame.child.num by omega),
          mul_nonneg (show (0 : ℤ) ≤ frame.child.den by omega) (show (0 : ℤ) ≤ frame.child.num by omega)]
      linarith
    · exact hz
    · exfalso
      have hkT : frame.child.periodDenominator ≤ k * frame.child.periodDenominator := by
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ k - 1 by omega) hTpos.le]
      linarith
  have h1 : x = 1 := by rw [hx, hk0]; ring
  have h0 : y = 0 := by rw [hy, hk0]; ring
  rw [h1, h0]
  rfl

/-- The apex of a free odd H site other than `hFirst`: `t ≥ n + 2`. -/
theorem apex_of_ne_hFirst (frame : ChildFrame) {W : Site} (hW : W ∈ frame.freeH) (hodd : ¬ EvenSite W)
    (hne : W ≠ hFirst) : frame.child.num + 2 ≤ frame.tGrade W := by
  have hn := num_odd frame
  have hpar := tGrade_mod_two frame W
  have hodd' : (W.1 + W.2) % 2 = 1 := by
    unfold EvenSite at hodd
    omega
  have hsp : frame.hSpectrum (frame.tGrade W) := hW.2.2
  unfold ChildFrame.hSpectrum at hsp
  have hlo : frame.child.num ≤ frame.tGrade W := by
    rcases hsp with ⟨h1, -⟩ | ⟨-, h2, -⟩
    · omega
    · exact h2
  have hne_t : frame.tGrade W ≠ frame.child.num := fun ht => hne (freeH_odd_t_num frame hW hodd ht)
  have hpar' : frame.tGrade W % 2 = 1 := by omega
  omega

/-- **The depth bound of the NW-fan square.** A black `z+N` at an even free H root forces `3n − 2 ≤ d`: for `d < 3n − 2` the
sites `z`, `z+(0,2)` and `z+N` lie in the zero windows and the zero strip, so `z+N` is white. -/
theorem depth_of_black_N {G : Field} {frame : ChildFrame}
    (hper : HasGeneratorPeriods frame.child G 0 frame.coherentConstantV)
    (hstrips : frame.HasStrips G)
    (hslip : ∀ z ∈ frame.closedPolygon, 0 ≤ frame.slip G 1 z)
    (hseed : ∀ z : Site, EvenSite z → frame.tGrade z = 2 - (frame.child.den + frame.child.num) → G z = 0)
    (hIsym : ∀ z : Site, G (FLatticePaper.W1Strips.iRefl z) = G z)
    {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z)
    (hWfree : (z.1 - 1, z.2) ∈ frame.freeH)
    (hN : laplacian G (z.1, z.2 + 1) = -1) :
    3 * frame.child.num - 2 ≤ frame.child.den := by
  have hn := num_odd frame
  obtain ⟨-, -, -, hd3, -⟩ := frame.child_facts
  by_contra hlt
  have hsp : frame.hSpectrum (frame.tGrade z) := hz.2.2
  unfold ChildFrame.hSpectrum at hsp
  have hevz : (z.1 + z.2) % 2 = 0 := hev
  have hzpar := tGrade_mod_two frame z
  have hWt : frame.child.num ≤ frame.tGrade (z.1 - 1, z.2) := by
    have hpW : frame.hSpectrum (frame.tGrade (z.1 - 1, z.2)) := hWfree.2.2
    unfold ChildFrame.hSpectrum at hpW
    have hpar := tGrade_mod_two frame (z.1 - 1, z.2)
    dsimp only at hpar
    rcases hpW with ⟨h1, -⟩ | ⟨-, h2, -⟩
    · omega
    · exact h2
  have htW : frame.tGrade (z.1 - 1, z.2) = frame.tGrade z - frame.child.num := by
    unfold ChildFrame.tGrade
    dsimp only
    ring
  have hsz : frame.child.den ≠ 0 := by omega
  rcases hsp with ⟨-, h2lo, hLhi⟩ | ⟨hm, -⟩
  swap
  · omega
  -- the three zero facts
  have hz0 : G z = 0 :=
    FLatticePaper.W1Strips.even_zero_full frame hper hstrips hslip hseed hIsym z hev
      (by omega) (by omega)
  have hE2ev : EvenSite (z.1, z.2 + 2) := by
    unfold EvenSite at hev ⊢
    dsimp only
    omega
  have htE2 : frame.tGrade (z.1, z.2 + 2) = frame.tGrade z - 2 * frame.child.den := by
    unfold ChildFrame.tGrade
    dsimp only
    ring
  have hE20 : G (z.1, z.2 + 2) = 0 :=
    FLatticePaper.W1Strips.even_zero_full frame hper hstrips hslip hseed hIsym (z.1, z.2 + 2) hE2ev
      (by omega) (by omega)
  have hNodd : ¬ EvenSite (z.1, z.2 + 1) := by
    unfold EvenSite
    dsimp only
    omega
  have htN : frame.tGrade (z.1, z.2 + 1) = frame.tGrade z - frame.child.den := by
    unfold ChildFrame.tGrade
    dsimp only
    ring
  have hN0 : G (z.1, z.2 + 1) = 0 :=
    zero_of_tGrade hstrips (by omega) (by omega)
  have hnegN : incomingNeg (z.1, z.2 + 1) = z := by
    unfold incomingNeg
    rw [if_neg hNodd]
    simp
  have hposN : incomingPos (z.1, z.2 + 1) = (z.1, z.2 + 2) := by
    unfold incomingPos
    rw [if_neg hNodd]
    congr 1
    ring
  have hlapN : laplacian G (z.1, z.2 + 1) = G z + G (z.1, z.2 + 2) - 2 * G (z.1, z.2 + 1) := by
    unfold laplacian
    rw [hnegN, hposN]
    ring
  rw [hlapN, hz0, hE20, hN0] at hN
  norm_num at hN

end FLatticePaper.FanInputs
