import FLatticePaper.Plane.Induction.FreeTraceBox
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.W1Exit
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.W1Strips
import FLatticePaper.Plane.Induction.ContactCone
import FLatticePaper.Plane.BellmanRank
import Mathlib.RingTheory.Coprime.Basic

/-! # The short route from an ordinary odd H midpoint (Q23, step 3, the case `d ≤ 3n`)

Let `b` be an ordinary odd free H site (`b ∈ freeH`, `b ≠ H_{d−1}`) with `t(b) ≥ N + 2`, the cone start convention (`t(H_i) = t(H_i − U)`,
and `F (z + U) = F z`, so the base is `b = H_i` in `E`, the note's `H_i − U` on `E − U`).

The route is `b → v = north(b) → e = east(v) → s = south(e)`. The short argument needs no cap:
* `F v = F w = F e = F s = 0` by the zero strip, since their t-grades lie in `[1 − d, n + 2d − 1]`, except `F n₂ = 0` for `n₂ = north(e)`,
  whose t-grade `t(b) + n − 2d` is in the even zero extension `[2 − L, 1 − d]` exactly when `d ≤ 3n` (`2 − L ≤ t(b) + n − 2d` iff
  `d + 2 ≤ t(b) + 2n` and `t(b) ≥ n + 2`);
* so `v` is a zero contact with zero laplacian, hence white: both inputs `w, e` lie in `S` (`IsIncomingFort`);
* `e` is a zero contact with zero laplacian (its inputs `s, n₂` vanish), hence white: both inputs lie in `S`, in particular `s`;
* `s` is a zero contact on the closed polygon, outside the open rectangle (`t(s) = t(b) + n ≥ 2`).

`s` is the exit of the short route. The `s`-range of a free H site is `[L, T − C]` (`freeH_box`), which places `v` in the open rectangle. -/

namespace FLatticePaper.ShortRoute

open FLatticePaper FLatticePaper.Induction FLatticePaper.ContactCone

/-- The internal free H sites have `t ≤ d − 2`: `t ≤ d` (odd spectrum), `t ≠ d` unless the site is `H_{d−1}`. -/
theorem freeH_tGrade_add_two_le (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z)
    (hne : z ≠ frame.hLast) : frame.tGrade z + 2 ≤ frame.child.den := by
  have hbox := FLatticePaper.Induction.FreeTraceBox.freeH_box frame hz
  obtain ⟨hx1, hxd, hy0, hyn⟩ := hbox
  have hz' := hz
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz'
  obtain ⟨-, -, hsp⟩ := hz'
  have hpar : frame.tGrade z % 2 = 1 := by
    rw [FLatticePaper.Induction.tGrade_parity frame z]
    have : ¬ (z.1 + z.2) % 2 = 0 := hodd
    omega
  have hsp' : frame.tGrade z ≤ frame.child.den ∧ frame.child.num ≤ frame.tGrade z := by
    unfold ChildFrame.hSpectrum at hsp
    rcases hsp with ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · exact ⟨h.2, h.1⟩
  have hne' : frame.tGrade z ≠ frame.child.den := by
    intro heq
    apply hne
    have ht : frame.tGrade z = frame.child.num * z.1 - frame.child.den * z.2 := rfl
    rw [ht] at heq
    have hcop : IsCoprime frame.child.den frame.child.num := IsCoprime.symm frame.child_reduced
    have hdvd : frame.child.den ∣ frame.child.num * z.1 := ⟨z.2 + 1, by linear_combination heq⟩
    obtain ⟨k, hk⟩ : frame.child.den ∣ z.1 := hcop.dvd_of_dvd_mul_left hdvd
    obtain ⟨hn1, hnd, -⟩ := frame.child_facts
    have hD : (0 : ℤ) < frame.child.den := by omega
    have hk1 : k = 1 := by
      have h1 : 1 ≤ k := by
        by_contra h
        have h' := not_le.mp h
        nlinarith
      have h2 : k ≤ 1 := by
        by_contra h
        have h' := not_le.mp h
        nlinarith
      omega
    have hx : z.1 = frame.child.den := by rw [hk, hk1]; ring
    have hy : z.2 = frame.child.num - 1 := by
      have h2 : frame.child.den * (z.2 - (frame.child.num - 1)) = 0 := by
        rw [hx] at heq
        linear_combination -heq
      rcases mul_eq_zero.mp h2 with h | h
      · omega
      · omega
    unfold ChildFrame.hLast
    exact Prod.ext hx hy
  obtain ⟨-, hdp⟩ := FLatticePaper.W1Exit.child_parity frame
  omega

/-- The `s`-range of a free H site: `L ≤ s ≤ T − C` (`H_0 = (1,0)` at the bottom left, `H_{d−1}` at the top right). -/
theorem freeH_sGrade_bounds (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) :
    frame.child.den + frame.child.num ≤ frame.sGrade z ∧
      frame.sGrade z ≤ frame.child.periodDenominator - (frame.child.den - frame.child.num) := by
  have hbox := FLatticePaper.Induction.FreeTraceBox.freeH_box frame hz
  obtain ⟨hx1, hxd, hy0, hyn⟩ := hbox
  obtain ⟨hn1, hnd, -, hd3, hT⟩ := frame.child_facts
  have hs : frame.sGrade z = (frame.child.den + frame.child.num) * z.1 + (frame.child.den - frame.child.num) * z.2 := rfl
  rw [hs, hT]
  constructor
  · nlinarith
  · nlinarith

/-- The north neighbour of an ordinary odd free H site lies in the open rectangle: its `t` is `t(b) − d < 2`, its `s` is `s(b) + c`
with `2d ≤ s(b) + c ≤ T` (strict below `H_{d−1}`). -/
theorem north_open (frame : ChildFrame) {b : Site} (hb : b ∈ frame.freeH) (hodd : ¬ EvenSite b)
    (hne : b ≠ frame.hLast) (hbt : frame.child.num + 2 ≤ frame.tGrade b) :
    frame.openRect (b.1, b.2 + 1) := by
  have hlt := freeH_tGrade_add_two_le frame hb hodd hne
  obtain ⟨hL, hsT⟩ := freeH_sGrade_bounds frame hb
  obtain ⟨hn1, hnd, -, hd3, hT⟩ := frame.child_facts
  have hbox := FLatticePaper.Induction.FreeTraceBox.freeH_box frame hb
  obtain ⟨hx1, hxd, hy0, hyn⟩ := hbox
  -- the strict top: `s(b) < T − C` (only `H_{d−1}` has equality)
  have hstrict : frame.sGrade b < frame.child.periodDenominator - (frame.child.den - frame.child.num) := by
    rcases lt_or_eq_of_le hsT with h | h
    · exact h
    · exfalso
      apply hne
      have hs : frame.sGrade b = (frame.child.den + frame.child.num) * b.1 + (frame.child.den - frame.child.num) * b.2 := rfl
      rw [hs, hT] at h
      have hA : 0 ≤ (frame.child.den + frame.child.num) * (frame.child.den - b.1) := by
        apply mul_nonneg <;> omega
      have hB : 0 ≤ (frame.child.den - frame.child.num) * (frame.child.num - 1 - b.2) := by
        apply mul_nonneg <;> omega
      have hA0 : (frame.child.den + frame.child.num) * (frame.child.den - b.1) = 0 := by nlinarith
      have hB0 : (frame.child.den - frame.child.num) * (frame.child.num - 1 - b.2) = 0 := by nlinarith
      have hx : b.1 = frame.child.den := by
        rcases mul_eq_zero.mp hA0 with h' | h'
        · omega
        · omega
      have hy : b.2 = frame.child.num - 1 := by
        rcases mul_eq_zero.mp hB0 with h' | h'
        · omega
        · omega
      unfold ChildFrame.hLast
      exact Prod.ext hx hy
  have hev : EvenSite (b.1, b.2 + 1) := by
    unfold EvenSite
    have : ¬ (b.1 + b.2) % 2 = 0 := hodd
    simp only
    omega
  have hs' : frame.sGrade (b.1, b.2 + 1) = frame.sGrade b + (frame.child.den - frame.child.num) := by
    unfold ChildFrame.sGrade
    ring
  have ht' : frame.tGrade (b.1, b.2 + 1) = frame.tGrade b - frame.child.den := by
    unfold ChildFrame.tGrade
    ring
  have hTbig : 2 * frame.child.den + frame.child.num - 2 < frame.child.periodDenominator := by
    rw [hT]
    nlinarith
  unfold ChildFrame.openRect
  rw [if_pos hev]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht']
    linarith
  · rw [ht']
    linarith
  · rw [hs']
    linarith
  · rw [hs']
    linarith

/-- **The short route exit** (Q23 step 3, `d ≤ 3n`). For an ordinary odd free H site `b` (`b ≠ H_{d−1}`, `t(b) ≥ n + 2`) whose north input
`v` lies in `S`: `v` and `e = east(v)` are white zero contacts, and `s = south(e)` is in `S`. The exit `s` is a contact on the parabola of
`b` on the closed polygon, outside the open rectangle. The zero values come from the strip, except `F (north e) = 0`, which is the even
zero extension `hEZ` (its `t`-grade `t(b) + n − 2d` is in `[2 − L, 1 − d]` exactly when `d ≤ 3n`). -/
theorem short_H_exit {F : Field} (frame : ChildFrame) (hP : frame.Packet F) {S : Set Site}
    (hfort : IsIncomingFort F S) {b : Site} (hb : b ∈ frame.freeH) (hodd : ¬ EvenSite b) (hne : b ≠ frame.hLast)
    (hbt : frame.child.num + 2 ≤ frame.tGrade b) (hD : frame.child.den ≤ 3 * frame.child.num)
    (hEZ : ∀ z : Site, EvenSite z → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade z →
      frame.tGrade z ≤ 1 - frame.child.den → F z = 0)
    (hvS : (b.1, b.2 + 1) ∈ S) :
    ∃ w : Site, w ∈ S ∧ F w = parabolaField b.2 w ∧ w ∈ frame.closedPolygon ∧ ¬ frame.openRect w := by
  have hlt := freeH_tGrade_add_two_le frame hb hodd hne
  obtain ⟨hL, hsT⟩ := freeH_sGrade_bounds frame hb
  obtain ⟨hn1, hnd, -, hd3, hT⟩ := frame.child_facts
  have hodd' : ¬ (b.1 + b.2) % 2 = 0 := hodd
  -- the t-grades of the route
  have tv : frame.tGrade (b.1, b.2 + 1) = frame.tGrade b - frame.child.den := by
    unfold ChildFrame.tGrade; ring
  have tw : frame.tGrade (b.1 - 1, b.2 + 1) = frame.tGrade b - frame.child.num - frame.child.den := by
    unfold ChildFrame.tGrade; ring
  have te : frame.tGrade (b.1 + 1, b.2 + 1) = frame.tGrade b + frame.child.num - frame.child.den := by
    unfold ChildFrame.tGrade; ring
  have ts : frame.tGrade (b.1 + 1, b.2) = frame.tGrade b + frame.child.num := by
    unfold ChildFrame.tGrade; ring
  have tn2 : frame.tGrade (b.1 + 1, b.2 + 2) = frame.tGrade b + frame.child.num - 2 * frame.child.den := by
    unfold ChildFrame.tGrade; ring
  have hss : frame.sGrade (b.1 + 1, b.2) = frame.sGrade b + (frame.child.den + frame.child.num) := by
    unfold ChildFrame.sGrade; ring
  -- zero values
  have hzero : ∀ z : Site, 1 - frame.child.den ≤ frame.tGrade z → frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 1 →
      F z = 0 := fun z h1 h2 => hP.strips.1 z h1 h2
  have Fv : F (b.1, b.2 + 1) = 0 := hzero _ (by rw [tv]; omega) (by rw [tv]; omega)
  have Fw : F (b.1 - 1, b.2 + 1) = 0 := hzero _ (by rw [tw]; omega) (by rw [tw]; omega)
  have Fe : F (b.1 + 1, b.2 + 1) = 0 := hzero _ (by rw [te]; omega) (by rw [te]; omega)
  have Fs : F (b.1 + 1, b.2) = 0 := hzero _ (by rw [ts]; omega) (by rw [ts]; omega)
  have Fn2 : F (b.1 + 1, b.2 + 2) = 0 := by
    by_cases h : 1 - frame.child.den ≤ frame.tGrade (b.1 + 1, b.2 + 2)
    · exact hzero _ h (by rw [tn2]; omega)
    · apply hEZ
      · unfold EvenSite
        simp only
        omega
      · rw [tn2]; omega
      · rw [tn2]; omega
  -- the north input `v` is white: both its inputs `w, e` lie in `S`
  have hinV_neg : incomingNeg (b.1, b.2 + 1) = (b.1 - 1, b.2 + 1) := by
    have hev : EvenSite (b.1, b.2 + 1) := by unfold EvenSite; simp only; omega
    unfold incomingNeg; rw [if_pos hev]
  have hinV_pos : incomingPos (b.1, b.2 + 1) = (b.1 + 1, b.2 + 1) := by
    have hev : EvenSite (b.1, b.2 + 1) := by unfold EvenSite; simp only; omega
    unfold incomingPos; rw [if_pos hev]
  have lapV : laplacian F (b.1, b.2 + 1) = 0 := by
    unfold laplacian
    rw [hinV_neg, hinV_pos, Fw, Fe, Fv]
    ring
  have heS : (b.1 + 1, b.2 + 1) ∈ S := by
    rcases hfort (b.1, b.2 + 1) hvS with ⟨hl, -⟩ | ⟨-, -, hp⟩
    · omega
    · rw [hinV_pos] at hp
      exact hp
  -- the east site `e` is white (its inputs `s, n₂` vanish): both inputs lie in `S`, in particular `s`
  have hinE_neg : incomingNeg (b.1 + 1, b.2 + 1) = (b.1 + 1, b.2) := by
    have hev : ¬ EvenSite (b.1 + 1, b.2 + 1) := by unfold EvenSite; simp only; omega
    unfold incomingNeg; rw [if_neg hev]; dsimp only; congr 1; ring
  have hinE_pos : incomingPos (b.1 + 1, b.2 + 1) = (b.1 + 1, b.2 + 2) := by
    have hev : ¬ EvenSite (b.1 + 1, b.2 + 1) := by unfold EvenSite; simp only; omega
    unfold incomingPos; rw [if_neg hev]; dsimp only; congr 1; ring
  have lapE : laplacian F (b.1 + 1, b.2 + 1) = 0 := by
    unfold laplacian
    rw [hinE_neg, hinE_pos, Fs, Fn2, Fe]
    ring
  have hsS : (b.1 + 1, b.2) ∈ S := by
    rcases hfort (b.1 + 1, b.2 + 1) heS with ⟨hl, -⟩ | ⟨-, hn, -⟩
    · omega
    · rw [hinE_neg] at hn
      exact hn
  -- the exit `s`
  have hsc : F (b.1 + 1, b.2) = parabolaField b.2 (b.1 + 1, b.2) := by
    unfold parabolaField
    show F (b.1 + 1, b.2) = FLatticePaper.QuadraticCap.capMin (b.2 - b.2)
    rw [sub_self, FLatticePaper.QuadraticCap.capMin_zero, Fs]
  have hcl : (b.1 + 1, b.2) ∈ frame.closedPolygon := by
    rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_pos (by unfold EvenSite; simp only; omega)]
    have hTpos : 2 ≤ frame.child.periodDenominator := by
      rw [hT]
      nlinarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [ts]; omega
    · rw [ts]; omega
    · rw [hss]; omega
    · rw [hss]; omega
  have hnot : ¬ frame.openRect (b.1 + 1, b.2) := by
    unfold ChildFrame.openRect
    rw [if_pos (by unfold EvenSite; simp only; omega)]
    intro h
    have h2 := h.2.1
    rw [ts] at h2
    omega
  exact ⟨(b.1 + 1, b.2), hsS, hsc, hcl, hnot⟩

/-- **The short route exit with the even zero extension derived**: `hEZ` is `W1Strips.even_zero_lower`, from the seed
`F = 0` on the line `t = 2 − L` (`hseed`) and the slip range (`hslip`, the `slipRange` of the word). -/
theorem short_H_exit_of_seed {F : Field} (frame : ChildFrame) (hP : frame.Packet F) {S : Set Site}
    (hfort : IsIncomingFort F S) {b : Site} (hb : b ∈ frame.freeH) (hodd : ¬ EvenSite b) (hne : b ≠ frame.hLast)
    (hbt : frame.child.num + 2 ≤ frame.tGrade b) (hD : frame.child.den ≤ 3 * frame.child.num)
    (hslip : ∀ z ∈ frame.closedPolygon, 0 ≤ frame.slip F 1 z)
    (hseed : ∀ z : Site, EvenSite z → frame.tGrade z = 2 - (frame.child.den + frame.child.num) → F z = 0)
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV)
    (hvS : (b.1, b.2 + 1) ∈ S) :
    ∃ w : Site, w ∈ S ∧ F w = parabolaField b.2 w ∧ w ∈ frame.closedPolygon ∧ ¬ frame.openRect w :=
  short_H_exit frame hP hfort hb hodd hne hbt hD
    (fun z hz h1 h2 => FLatticePaper.W1Strips.even_zero_lower frame hper hP.strips hslip hseed z hz h1 h2) hvS

end FLatticePaper.ShortRoute
