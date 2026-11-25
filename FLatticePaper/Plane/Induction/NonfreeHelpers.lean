import FLatticePaper.Plane.Induction.FaceRows
import FLatticePaper.Plane.Induction.W1CollarFrame

/-! # Nonfreeness of the three helper corners of the collar faces (Q33 (1), the forced rows)

The helper corners `(−1,1)` (even), `(2,−2)` (even) and `(−1,−2)` (odd) are nonfree: no deck translate of them is a free H or V site.
A deck vector `combine i j` shifts `t = n x − d y` by `−j T` and `s = L x + (d−n) y` by `i T`, with `T = d² + 2dn − n²`, `L = d + n`.
The closed rectangle and the spectra bound `(i, j)`; in conjugate frames `n ≡ d (mod 2)`, so `L` is even. -/

namespace FLatticePaper.NonfreeHelpers

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.W1OffCollar FLatticePaper.W1CollarFrame

/-- The deck vector `combine i j` in coordinates. -/
theorem combine_eq (frame : ChildFrame) (i j : ℤ) :
    frame.child.modifiedDeck.combine i j =
      (i * frame.child.den + j * (frame.child.num - frame.child.den),
        i * frame.child.num + j * (frame.child.num + frame.child.den)) := by
  unfold PeriodDeck.combine
  rw [frame.kernel_coords, frame.child_modifiedDeck_transverse]

/-- **The helper `(−1,1)` is nonfree.** -/
theorem nonfree_m11_one (frame : ChildFrame) : Nonfree frame ((-1 : ℤ), (1 : ℤ)) := by
  unfold Nonfree
  intro v hv hmem
  obtain ⟨i, j, rfl⟩ := hv
  obtain ⟨hn1, hnd, hdn, hd3, hTdef⟩ := frame.child_facts
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  rw [combine_eq] at hmem
  simp only [Prod.mk_add_mk] at hmem
  rw [Set.mem_union] at hmem
  set n := frame.child.num with hn
  set d := frame.child.den with hd
  set T := frame.child.periodDenominator with hTd
  have hTT : T = d ^ 2 + 2 * d * n - n ^ 2 := hTdef
  have hTL : 2 * (d + n) < T := by rw [hTT]; nlinarith
  have hT4 : 4 * n < T := by rw [hTT]; nlinarith
  have hTpos : 0 < T := by linarith
  have ht : n * ((-1 : ℤ) + (i * d + j * (n - d))) - d * ((1 : ℤ) + (i * n + j * (n + d))) =
      -(d + n) - j * T := by
    rw [hTT]
    ring
  have hs : (d + n) * ((-1 : ℤ) + (i * d + j * (n - d))) + (d - n) * ((1 : ℤ) + (i * n + j * (n + d))) =
      -2 * n + i * T := by
    rw [hTT]
    ring
  obtain ⟨m, hm⟩ : ∃ m, n + d = 2 * m := ⟨(n + d) / 2, by omega⟩
  have hEven : EvenSite ((-1 : ℤ) + (i * d + j * (n - d)), (1 : ℤ) + (i * n + j * (n + d))) := by
    unfold EvenSite
    have key : ((-1 : ℤ) + (i * d + j * (n - d)) + ((1 : ℤ) + (i * n + j * (n + d)))) = 2 * (i * m + j * n) := by
      linear_combination i * hm
    rw [key]
    simp
  rcases hmem with hH | hV
  · rw [freeH_iff] at hH
    obtain ⟨-, -, hsp⟩ := hH
    unfold w1t at hsp
    unfold hSp at hsp
    rw [ht] at hsp
    rcases lt_or_ge j 0 with hj | hj
    · have hj' : j ≤ -1 := by omega
      have : j * T ≤ -1 * T := mul_le_mul_of_nonneg_right hj' hTpos.le
      rcases hsp with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> linarith
    · have : 0 ≤ j * T := mul_nonneg hj hTpos.le
      rcases hsp with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> linarith
  · rw [freeV_iff] at hV
    obtain ⟨hcl, -, hsp⟩ := hV
    rw [closedRect_iff] at hcl
    rcases hcl with ⟨-, hb⟩ | ⟨hodd, -⟩
    · obtain ⟨-, -, hs0, -⟩ := hb
      unfold w1s at hs0 hsp
      unfold vSp at hsp
      rw [hs] at hs0 hsp
      obtain ⟨-, hsr⟩ := hsp
      rcases lt_or_ge i 1 with hi | hi
      · have hi' : i ≤ 0 := by omega
        have : i * T ≤ 0 := by nlinarith
        linarith
      · have : 1 * T ≤ i * T := mul_le_mul_of_nonneg_right hi hTpos.le
        rcases hsr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    · exact absurd hEven hodd

/-- **The helper `(2,−2)` is nonfree.** Its grades are `t = 2L − jT` and `s = 4n + iT`: the H spectrum forces `t` into `[1, L]`, which
fails for every `j`; the closed rectangle forces `j = 1`, `i = 0`, and then the left neighbour of the translate is in the closed rectangle. -/
theorem nonfree_2m2 (frame : ChildFrame) : Nonfree frame ((2 : ℤ), (-2 : ℤ)) := by
  unfold Nonfree
  intro v hv hmem
  obtain ⟨i, j, rfl⟩ := hv
  obtain ⟨hn1, hnd, hdn, hd3, hTdef⟩ := frame.child_facts
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  rw [combine_eq] at hmem
  simp only [Prod.mk_add_mk] at hmem
  rw [Set.mem_union] at hmem
  set n := frame.child.num with hn
  set d := frame.child.den with hd
  set T := frame.child.periodDenominator with hTd
  have hTT : T = d ^ 2 + 2 * d * n - n ^ 2 := hTdef
  have hw : w1T frame.child.num frame.child.den = T := by
    unfold w1T
    rw [hTT]
  have hTL : 2 * (d + n) < T := by rw [hTT]; nlinarith
  have hT4 : 4 * n < T := by rw [hTT]; nlinarith
  have hTpos : 0 < T := by linarith
  have ht : n * ((2 : ℤ) + (i * d + j * (n - d))) - d * ((-2 : ℤ) + (i * n + j * (n + d))) =
      2 * (d + n) - j * T := by
    rw [hTT]
    ring
  have hs : (d + n) * ((2 : ℤ) + (i * d + j * (n - d))) + (d - n) * ((-2 : ℤ) + (i * n + j * (n + d))) =
      4 * n + i * T := by
    rw [hTT]
    ring
  obtain ⟨m, hm⟩ : ∃ m, n + d = 2 * m := ⟨(n + d) / 2, by omega⟩
  have hEven : EvenSite ((2 : ℤ) + (i * d + j * (n - d)), (-2 : ℤ) + (i * n + j * (n + d))) := by
    unfold EvenSite
    have key : ((2 : ℤ) + (i * d + j * (n - d)) + ((-2 : ℤ) + (i * n + j * (n + d)))) = 2 * (i * m + j * n) := by
      linear_combination i * hm
    rw [key]
    simp
  rcases hmem with hH | hV
  · rw [freeH_iff] at hH
    obtain ⟨-, -, hsp⟩ := hH
    unfold w1t at hsp
    unfold hSp at hsp
    rw [ht] at hsp
    rcases lt_or_ge j 1 with hj | hj
    · have hj' : j ≤ 0 := by omega
      have : j * T ≤ 0 := by nlinarith
      rcases hsp with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> linarith
    · have : 1 * T ≤ j * T := mul_le_mul_of_nonneg_right hj hTpos.le
      rcases hsp with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> linarith
  · rw [freeV_iff] at hV
    obtain ⟨hcl, hnot, -⟩ := hV
    rw [closedRect_iff] at hcl
    rcases hcl with ⟨-, hb⟩ | ⟨hodd, -⟩
    · obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
      unfold w1t at hb1 hb2
      unfold w1s at hb3 hb4
      rw [ht] at hb1 hb2
      rw [hs] at hb3 hb4
      have hj1 : 1 ≤ j := by
        by_contra hc
        have hj0 : j ≤ 0 := by omega
        have : j * T ≤ 0 := by nlinarith
        linarith
      have hj2 : j ≤ 1 := by
        by_contra hc
        have hj2' : 2 ≤ j := by omega
        have : 2 * T ≤ j * T := mul_le_mul_of_nonneg_right hj2' hTpos.le
        linarith
      have hj : j = 1 := by omega
      have hi : i = 0 := by
        rcases lt_trichotomy i 0 with hi | hi | hi
        · have : i * T ≤ -1 * T := mul_le_mul_of_nonneg_right (by omega) hTpos.le
          linarith
        · exact hi
        · have : 1 * T ≤ i * T := mul_le_mul_of_nonneg_right (by omega) hTpos.le
          linarith
      subst hi
      subst hj
      apply hnot
      rw [closedRect_iff]
      right
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · unfold EvenSite
        omega
      · simp only [w1t]
        nlinarith
      · simp only [w1t]
        nlinarith
      · simp only [w1s]
        nlinarith
      · simp only [w1s]
        nlinarith
    · exact absurd hEven hodd

/-- **The helper `(−1,−2)` is nonfree.** Its grades are `t = 2d − n − jT` and `s = −3d + n + iT`; the odd closed rectangle and the spectra
force `j = 1` (then `t < 0`) in the H case and `i = 1` (then `s` is outside the V spectrum) in the V case. -/
theorem nonfree_m1m2 (frame : ChildFrame) : Nonfree frame ((-1 : ℤ), (-2 : ℤ)) := by
  unfold Nonfree
  intro v hv hmem
  obtain ⟨i, j, rfl⟩ := hv
  obtain ⟨hn1, hnd, hdn, hd3, hTdef⟩ := frame.child_facts
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  rw [combine_eq] at hmem
  simp only [Prod.mk_add_mk] at hmem
  rw [Set.mem_union] at hmem
  set n := frame.child.num with hn
  set d := frame.child.den with hd
  set T := frame.child.periodDenominator with hTd
  have hTT : T = d ^ 2 + 2 * d * n - n ^ 2 := hTdef
  have hw : w1T frame.child.num frame.child.den = T := by
    unfold w1T
    rw [hTT]
  have hT2 : 2 * d < T := by rw [hTT]; nlinarith
  have hT4 : 4 * d < T := by rw [hTT]; nlinarith
  have hT3 : 3 * d + n < T := by rw [hTT]; nlinarith
  have hTpos : 0 < T := by linarith
  have ht : n * ((-1 : ℤ) + (i * d + j * (n - d))) - d * ((-2 : ℤ) + (i * n + j * (n + d))) =
      2 * d - n - j * T := by
    rw [hTT]
    ring
  have hs : (d + n) * ((-1 : ℤ) + (i * d + j * (n - d))) + (d - n) * ((-2 : ℤ) + (i * n + j * (n + d))) =
      -3 * d + n + i * T := by
    rw [hTT]
    ring
  obtain ⟨m, hm⟩ : ∃ m, n + d = 2 * m := ⟨(n + d) / 2, by omega⟩
  have hOdd : ¬ EvenSite ((-1 : ℤ) + (i * d + j * (n - d)), (-2 : ℤ) + (i * n + j * (n + d))) := by
    unfold EvenSite
    have key : ((-1 : ℤ) + (i * d + j * (n - d)) + ((-2 : ℤ) + (i * n + j * (n + d)))) = 2 * (i * m + j * n) - 3 := by
      linear_combination i * hm
    rw [key]
    omega
  rcases hmem with hH | hV
  · rw [freeH_iff] at hH
    obtain ⟨hcl, -, hsp⟩ := hH
    rw [closedRect_iff] at hcl
    rcases hcl with ⟨hev, -⟩ | ⟨-, hb⟩
    · exact absurd hev hOdd
    · obtain ⟨hb1, hb2, -, -⟩ := hb
      rw [hw] at hb1
      unfold w1t at hb1 hb2
      rw [ht] at hb1 hb2
      have hj1 : 1 ≤ j := by
        by_contra hc
        have hj0 : j ≤ 0 := by omega
        have : j * T ≤ 0 := by nlinarith
        linarith
      have hj : j = 1 := by
        by_contra hc
        have hj2' : 2 ≤ j := by omega
        have : 2 * T ≤ j * T := mul_le_mul_of_nonneg_right hj2' hTpos.le
        linarith
      subst hj
      unfold w1t at hsp
      unfold hSp at hsp
      rw [ht] at hsp
      rcases hsp with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ <;> linarith
  · rw [freeV_iff] at hV
    obtain ⟨hcl, -, hsp⟩ := hV
    rw [closedRect_iff] at hcl
    rcases hcl with ⟨hev, -⟩ | ⟨-, hb⟩
    · exact absurd hev hOdd
    · obtain ⟨-, -, hb3, hb4⟩ := hb
      rw [hw] at hb4
      unfold w1s at hb3 hb4
      rw [hs] at hb3 hb4
      have hi1 : 1 ≤ i := by
        by_contra hc
        have hi0 : i ≤ 0 := by omega
        have : i * T ≤ 0 := by nlinarith
        linarith
      have hi : i = 1 := by
        by_contra hc
        have hi2' : 2 ≤ i := by omega
        have : 2 * T ≤ i * T := mul_le_mul_of_nonneg_right hi2' hTpos.le
        linarith
      subst hi
      unfold w1s at hsp
      unfold vSp at hsp
      rw [hs] at hsp
      obtain ⟨-, hsr⟩ := hsp
      rcases hsr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

end FLatticePaper.NonfreeHelpers
