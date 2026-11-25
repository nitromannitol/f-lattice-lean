import FLatticePaper.Plane.Induction.EndpointRows
import FLatticePaper.Plane.Induction.FanInputs

/-! # The endpoint facts from the strips and the spectra

`EndpointFacts frame G` is the colour and freeness table of the endpoint rows. Its origin entries are read off the strips of `G`
(`ChildFrame.HasStrips`: `G = 0` on the t-window `[1−d, n+2d−1]`, `G = harmonicGrid` on the s-window `[1−2d, 2(d+n)−1]`); the
laplacian is the sum over the two incoming neighbours. The frame entries use the same strips and the discrete harmonicity of
`harmonicGrid`. The freeness entries are the closed polygon and the spectra. -/

namespace FLatticePaper.EndpointStrips

open FLatticePaper FLatticePaper.Induction FLatticePaper.EndpointRows

theorem lap_even_eq (G : Field) (z : Site) (h : EvenSite z) :
    laplacian G z = G (z.1 - 1, z.2) + G (z.1 + 1, z.2) - 2 * G z := by
  unfold laplacian incomingNeg incomingPos
  rw [if_pos h, if_pos h]
  ring

theorem lap_odd_eq (G : Field) (z : Site) (h : ¬ EvenSite z) :
    laplacian G z = G (z.1, z.2 - 1) + G (z.1, z.2 + 1) - 2 * G z := by
  unfold laplacian incomingNeg incomingPos
  rw [if_neg h, if_neg h]
  ring

theorem tG (frame : ChildFrame) (x y : ℤ) :
    frame.tGrade (x, y) = frame.child.num * x - frame.child.den * y := rfl

theorem sG (frame : ChildFrame) (x y : ℤ) :
    frame.sGrade (x, y) = (frame.child.den + frame.child.num) * x + (frame.child.den - frame.child.num) * y := rfl

/-- The zero strip, with the t-grade given as a value. -/
theorem zeroAt {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) (x y t : ℤ)
    (ht : frame.tGrade (x, y) = t) (h1 : 1 - frame.child.den ≤ t) (h2 : t ≤ frame.child.num + 2 * frame.child.den - 1) :
    G (x, y) = 0 := by
  rw [← ht] at h1 h2
  exact hS.1 (x, y) h1 h2

/-- The harmonic strip, with the s-grade given as a value. -/
theorem harmAt {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) (x y s : ℤ)
    (hs : frame.sGrade (x, y) = s) (h1 : 1 - 2 * frame.child.den ≤ s)
    (h2 : s ≤ 2 * (frame.child.den + frame.child.num) - 1) :
    G (x, y) = harmonicGrid (x, y) := by
  rw [← hs] at h1 h2
  exact hS.2 (x, y) h1 h2

theorem hg01 : harmonicGrid (0, 1) = -1 := by unfold harmonicGrid; norm_num
theorem hg02 : harmonicGrid (0, 2) = -2 := by unfold harmonicGrid; norm_num
theorem hg1m2 : harmonicGrid (1, -2) = -1 := by unfold harmonicGrid; norm_num
theorem hg1m3 : harmonicGrid (1, -3) = -2 := by unfold harmonicGrid; norm_num
theorem hgm11 : harmonicGrid (-1, 1) = -1 := by unfold harmonicGrid; norm_num
theorem hg2m2 : harmonicGrid (2, -2) = -1 := by unfold harmonicGrid; norm_num

/-! ## The origin entries -/

theorem lap_b11 {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) : laplacian G (1, 1) = -1 := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  rw [lap_even_eq G (1, 1) (by norm_num [EvenSite])]
  have g01 : G (0, 1) = -1 :=
    (harmAt hS 0 1 (frame.child.den - frame.child.num) (by rw [sG]; ring) (by omega) (by omega)).trans hg01
  have g21 : G (2, 1) = 0 :=
    zeroAt hS 2 1 (2 * frame.child.num - frame.child.den) (by rw [tG]; ring) (by omega) (by omega)
  have g11 : G (1, 1) = 0 :=
    zeroAt hS 1 1 (frame.child.num - frame.child.den) (by rw [tG]; ring) (by omega) (by omega)
  show G (0, 1) + G (2, 1) - 2 * G (1, 1) = -1
  rw [g01, g21, g11]
  norm_num

theorem lap_b0m2 {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) : laplacian G (0, -2) = -1 := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  rw [lap_even_eq G (0, -2) (by norm_num [EvenSite])]
  have gm : G (-1, -2) = 0 :=
    zeroAt hS (-1) (-2) (2 * frame.child.den - frame.child.num) (by rw [tG]; ring) (by omega) (by omega)
  have g1 : G (1, -2) = -1 :=
    (harmAt hS 1 (-2) (3 * frame.child.num - frame.child.den) (by rw [sG]; ring) (by omega) (by omega)).trans hg1m2
  have g0 : G (0, -2) = 0 :=
    zeroAt hS 0 (-2) (2 * frame.child.den) (by rw [tG]; ring) (by omega) (by omega)
  show G (-1, -2) + G (1, -2) - 2 * G (0, -2) = -1
  rw [gm, g1, g0]
  norm_num

theorem lap_bm10 {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) : laplacian G (-1, 0) = -1 := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  rw [lap_odd_eq G (-1, 0) (by norm_num [EvenSite])]
  have gA : G (-1, -1) = 0 :=
    zeroAt hS (-1) (-1) (frame.child.den - frame.child.num) (by rw [tG]; ring) (by omega) (by omega)
  have gB : G (-1, 1) = -1 :=
    (harmAt hS (-1) 1 (-2 * frame.child.num) (by rw [sG]; ring) (by omega) (by omega)).trans hgm11
  have gC : G (-1, 0) = 0 :=
    zeroAt hS (-1) 0 (-frame.child.num) (by rw [tG]; ring) (by omega) (by omega)
  show G (-1, -1) + G (-1, 1) - 2 * G (-1, 0) = -1
  rw [gA, gB, gC]
  norm_num

theorem lap_b2m1 {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) : laplacian G (2, -1) = -1 := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  rw [lap_odd_eq G (2, -1) (by norm_num [EvenSite])]
  have gA : G (2, -2) = -1 :=
    (harmAt hS 2 (-2) (4 * frame.child.num) (by rw [sG]; ring) (by omega) (by omega)).trans hg2m2
  have gB : G (2, 0) = 0 :=
    zeroAt hS 2 0 (2 * frame.child.num) (by rw [tG]; ring) (by omega) (by omega)
  have gC : G (2, -1) = 0 :=
    zeroAt hS 2 (-1) (2 * frame.child.num + frame.child.den) (by rw [tG]; ring) (by omega) (by omega)
  show G (2, -2) + G (2, 0) - 2 * G (2, -1) = -1
  rw [gA, gB, gC]
  norm_num

/-! ## The white origin entries -/

theorem lap_w10 {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) : laplacian G (1, 0) = 0 := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  rw [lap_odd_eq G (1, 0) (by norm_num [EvenSite])]
  have gA : G (1, -1) = 0 :=
    zeroAt hS 1 (-1) (frame.child.num + frame.child.den) (by rw [tG]; ring) (by omega) (by omega)
  have gB : G (1, 1) = 0 :=
    zeroAt hS 1 1 (frame.child.num - frame.child.den) (by rw [tG]; ring) (by omega) (by omega)
  have gC : G (1, 0) = 0 :=
    zeroAt hS 1 0 frame.child.num (by rw [tG]; ring) (by omega) (by omega)
  show G (1, -1) + G (1, 1) - 2 * G (1, 0) = 0
  rw [gA, gB, gC]
  norm_num

theorem lap_w00 {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) : laplacian G (0, 0) = 0 := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  rw [lap_even_eq G (0, 0) (by norm_num [EvenSite])]
  have gA : G (-1, 0) = 0 :=
    zeroAt hS (-1) 0 (-frame.child.num) (by rw [tG]; ring) (by omega) (by omega)
  have gB : G (1, 0) = 0 :=
    zeroAt hS 1 0 frame.child.num (by rw [tG]; ring) (by omega) (by omega)
  have gC : G (0, 0) = 0 :=
    zeroAt hS 0 0 0 (by rw [tG]; ring) (by omega) (by omega)
  show G (-1, 0) + G (1, 0) - 2 * G (0, 0) = 0
  rw [gA, gB, gC]
  norm_num

theorem lap_w01 {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) : laplacian G (0, 1) = 0 := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  rw [lap_odd_eq G (0, 1) (by norm_num [EvenSite])]
  have gA : G (0, 0) = 0 :=
    zeroAt hS 0 0 0 (by rw [tG]; ring) (by omega) (by omega)
  have gB : G (0, 2) = -2 :=
    (harmAt hS 0 2 (2 * (frame.child.den - frame.child.num)) (by rw [sG]; ring) (by omega) (by omega)).trans hg02
  have gC : G (0, 1) = -1 :=
    (harmAt hS 0 1 (frame.child.den - frame.child.num) (by rw [sG]; ring) (by omega) (by omega)).trans hg01
  show G (0, 0) + G (0, 2) - 2 * G (0, 1) = 0
  rw [gA, gB, gC]
  norm_num

theorem lap_w20 {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) : laplacian G (2, 0) = 0 := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  rw [lap_even_eq G (2, 0) (by norm_num [EvenSite])]
  have gA : G (1, 0) = 0 :=
    zeroAt hS 1 0 frame.child.num (by rw [tG]; ring) (by omega) (by omega)
  have gB : G (3, 0) = 0 :=
    zeroAt hS 3 0 (3 * frame.child.num) (by rw [tG]; ring) (by omega) (by omega)
  have gC : G (2, 0) = 0 :=
    zeroAt hS 2 0 (2 * frame.child.num) (by rw [tG]; ring) (by omega) (by omega)
  show G (1, 0) + G (3, 0) - 2 * G (2, 0) = 0
  rw [gA, gB, gC]
  norm_num

theorem lap_w0m1 {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) : laplacian G (0, -1) = 0 := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  rw [lap_odd_eq G (0, -1) (by norm_num [EvenSite])]
  have gA : G (0, -2) = 0 :=
    zeroAt hS 0 (-2) (2 * frame.child.den) (by rw [tG]; ring) (by omega) (by omega)
  have gB : G (0, 0) = 0 :=
    zeroAt hS 0 0 0 (by rw [tG]; ring) (by omega) (by omega)
  have gC : G (0, -1) = 0 :=
    zeroAt hS 0 (-1) frame.child.den (by rw [tG]; ring) (by omega) (by omega)
  show G (0, -2) + G (0, 0) - 2 * G (0, -1) = 0
  rw [gA, gB, gC]
  norm_num

theorem lap_wm11 {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) : laplacian G (-1, -1) = 0 := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  rw [lap_even_eq G (-1, -1) (by norm_num [EvenSite])]
  have gA : G (-2, -1) = 0 :=
    zeroAt hS (-2) (-1) (frame.child.den - 2 * frame.child.num) (by rw [tG]; ring) (by omega) (by omega)
  have gB : G (0, -1) = 0 :=
    zeroAt hS 0 (-1) frame.child.den (by rw [tG]; ring) (by omega) (by omega)
  have gC : G (-1, -1) = 0 :=
    zeroAt hS (-1) (-1) (frame.child.den - frame.child.num) (by rw [tG]; ring) (by omega) (by omega)
  show G (-2, -1) + G (0, -1) - 2 * G (-1, -1) = 0
  rw [gA, gB, gC]
  norm_num

theorem lap_w1m1 {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) : laplacian G (1, -1) = 0 := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  rw [lap_even_eq G (1, -1) (by norm_num [EvenSite])]
  have gA : G (0, -1) = 0 :=
    zeroAt hS 0 (-1) frame.child.den (by rw [tG]; ring) (by omega) (by omega)
  have gB : G (2, -1) = 0 :=
    zeroAt hS 2 (-1) (2 * frame.child.num + frame.child.den) (by rw [tG]; ring) (by omega) (by omega)
  have gC : G (1, -1) = 0 :=
    zeroAt hS 1 (-1) (frame.child.num + frame.child.den) (by rw [tG]; ring) (by omega) (by omega)
  show G (0, -1) + G (2, -1) - 2 * G (1, -1) = 0
  rw [gA, gB, gC]
  norm_num

theorem lap_w1m2 {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) : laplacian G (1, -2) = 0 := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  rw [lap_odd_eq G (1, -2) (by norm_num [EvenSite])]
  have gA : G (1, -3) = -2 :=
    (harmAt hS 1 (-3) (4 * frame.child.num - 2 * frame.child.den) (by rw [sG]; ring) (by omega) (by omega)).trans hg1m3
  have gB : G (1, -1) = 0 :=
    zeroAt hS 1 (-1) (frame.child.num + frame.child.den) (by rw [tG]; ring) (by omega) (by omega)
  have gC : G (1, -2) = -1 :=
    (harmAt hS 1 (-2) (3 * frame.child.num - frame.child.den) (by rw [sG]; ring) (by omega) (by omega)).trans hg1m2
  show G (1, -3) + G (1, -1) - 2 * G (1, -2) = 0
  rw [gA, gB, gC]
  norm_num

/-! ## The frame endpoints -/

/-- The period denominator in the closed form, and the bound `2d + n + 2 ≤ T` that the freeness inequalities use. -/
theorem period_bound (frame : ChildFrame) :
    frame.child.periodDenominator
        = frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num - frame.child.num * frame.child.num ∧
      2 * frame.child.den + frame.child.num + 2 ≤ frame.child.periodDenominator := by
  obtain ⟨hn0, hnd, hdn2, hd3, hPT⟩ := frame.child_facts
  have hT : frame.child.periodDenominator
      = frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num - frame.child.num * frame.child.num := by
    rw [hPT]
    ring
  refine ⟨hT, ?_⟩
  rw [hT]
  nlinarith [mul_nonneg (show (0:ℤ) ≤ frame.child.den - frame.child.num - 2 by omega)
      (show (0:ℤ) ≤ frame.child.den + frame.child.num by omega),
    mul_nonneg (show (0:ℤ) ≤ frame.child.den by omega) (show (0:ℤ) ≤ frame.child.num - 1 by omega)]

theorem lap_hL {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) : laplacian G frame.hLast = 0 := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  show laplacian G (frame.child.den, frame.child.num - 1) = 0
  rw [lap_odd_eq G (frame.child.den, frame.child.num - 1) (show ¬ EvenSite (frame.child.den, frame.child.num - 1) from by
    unfold EvenSite
    dsimp only
    omega)]
  dsimp only
  have gA : G (frame.child.den, frame.child.num - 1 - 1) = 0 :=
    zeroAt hS _ _ (2 * frame.child.den) (by rw [tG]; ring) (by omega) (by omega)
  have gB : G (frame.child.den, frame.child.num - 1 + 1) = 0 :=
    zeroAt hS _ _ 0 (by rw [tG]; ring) (by omega) (by omega)
  have gC : G (frame.child.den, frame.child.num - 1) = 0 :=
    zeroAt hS _ _ frame.child.den (by rw [tG]; ring) (by omega) (by omega)
  rw [gA, gB, gC]
  norm_num

theorem lap_hP {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) :
    laplacian G (frame.child.den - 1, frame.child.num - 1) = 0 := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  rw [lap_even_eq G _ (show EvenSite (frame.child.den - 1, frame.child.num - 1) from by
    unfold EvenSite
    dsimp only
    omega)]
  dsimp only
  have gA : G (frame.child.den - 1 - 1, frame.child.num - 1) = 0 :=
    zeroAt hS _ _ (frame.child.den - 2 * frame.child.num) (by rw [tG]; ring) (by omega) (by omega)
  have gB : G (frame.child.den - 1 + 1, frame.child.num - 1) = 0 :=
    zeroAt hS _ _ frame.child.den (by rw [tG]; ring) (by omega) (by omega)
  have gC : G (frame.child.den - 1, frame.child.num - 1) = 0 :=
    zeroAt hS _ _ (frame.child.den - frame.child.num) (by rw [tG]; ring) (by omega) (by omega)
  rw [gA, gB, gC]
  norm_num

theorem lap_vL {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) : laplacian G frame.vLast = 0 := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  show laplacian G (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 1) = 0
  rw [lap_even_eq G _ (show EvenSite (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 1) from by
    unfold EvenSite
    dsimp only
    omega)]
  dsimp only
  have hA : G (frame.child.num - frame.child.den + 1 - 1, frame.child.num + frame.child.den - 1)
      = harmonicGrid (frame.child.num - frame.child.den + 1 - 1, frame.child.num + frame.child.den - 1) :=
    harmAt hS _ _ (frame.child.num - frame.child.den) (by rw [sG]; ring) (by omega) (by omega)
  have hB : G (frame.child.num - frame.child.den + 1 + 1, frame.child.num + frame.child.den - 1)
      = harmonicGrid (frame.child.num - frame.child.den + 1 + 1, frame.child.num + frame.child.den - 1) :=
    harmAt hS _ _ (frame.child.den + 3 * frame.child.num) (by rw [sG]; ring) (by omega) (by omega)
  have hC : G (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 1)
      = harmonicGrid (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 1) :=
    harmAt hS _ _ (2 * frame.child.num) (by rw [sG]; ring) (by omega) (by omega)
  have hh := harmonicGrid_harmonic (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 1)
  rw [lap_even_eq harmonicGrid _ (show EvenSite (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 1)
    from by
      unfold EvenSite
      dsimp only
      omega)] at hh
  dsimp only at hh
  rw [hA, hB, hC]
  linarith [hh]

theorem lap_vP {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) :
    laplacian G (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) = 0 := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  rw [lap_odd_eq G _ (show ¬ EvenSite (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) from by
    unfold EvenSite
    dsimp only
    omega)]
  dsimp only
  have hA : G (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2 - 1)
      = harmonicGrid (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2 - 1) :=
    harmAt hS _ _ (4 * frame.child.num - 2 * frame.child.den) (by rw [sG]; ring) (by omega) (by omega)
  have hB : G (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2 + 1)
      = harmonicGrid (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2 + 1) :=
    harmAt hS _ _ (2 * frame.child.num) (by rw [sG]; ring) (by omega) (by omega)
  have hC : G (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2)
      = harmonicGrid (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) :=
    harmAt hS _ _ (3 * frame.child.num - frame.child.den) (by rw [sG]; ring) (by omega) (by omega)
  have hh := harmonicGrid_harmonic (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2)
  rw [lap_odd_eq harmonicGrid _ (show ¬ EvenSite (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2)
    from by
      unfold EvenSite
      dsimp only
      omega)] at hh
  dsimp only at hh
  rw [hA, hB, hC]
  linarith [hh]

/-! ## The freeness entries -/

theorem fH10 (frame : ChildFrame) : (1, 0) ∈ frame.freeH := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  obtain ⟨hT, hT2⟩ := period_bound frame
  have hodd : frame.child.num % 2 = 1 := FLatticePaper.FanInputs.num_odd frame
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  simp only [ChildFrame.freeH, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [FLatticePaper.Induction.mem_closedPolygon_iff,
      if_neg (show ¬ EvenSite (1, 0) from by unfold EvenSite; dsimp only; omega)]
    simp only [tG, sG]
    omega
  · intro h
    try dsimp only at h
    rw [FLatticePaper.Induction.mem_closedPolygon_iff,
      if_pos (show EvenSite (1, 0 - 1) from by unfold EvenSite; dsimp only; omega)] at h
    simp only [tG, sG] at h
    omega
  · simp only [tG]
    unfold ChildFrame.hSpectrum
    right
    omega

theorem fV00 (frame : ChildFrame) : (0, 0) ∈ frame.freeV := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  obtain ⟨hT, hT2⟩ := period_bound frame
  have hodd : frame.child.num % 2 = 1 := FLatticePaper.FanInputs.num_odd frame
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  simp only [ChildFrame.freeV, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [FLatticePaper.Induction.mem_closedPolygon_iff,
      if_pos (show EvenSite (0, 0) from by unfold EvenSite; dsimp only; omega)]
    simp only [tG, sG]
    omega
  · intro h
    try dsimp only at h
    rw [FLatticePaper.Induction.mem_closedPolygon_iff,
      if_neg (show ¬ EvenSite (0 - 1, 0) from by unfold EvenSite; dsimp only; omega)] at h
    simp only [tG, sG] at h
    omega
  · simp only [sG]
    unfold ChildFrame.vSpectrum
    omega

theorem fV01 (frame : ChildFrame) : (0, 1) ∈ frame.freeV := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  obtain ⟨hT, hT2⟩ := period_bound frame
  have hodd : frame.child.num % 2 = 1 := FLatticePaper.FanInputs.num_odd frame
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  simp only [ChildFrame.freeV, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [FLatticePaper.Induction.mem_closedPolygon_iff,
      if_neg (show ¬ EvenSite (0, 1) from by unfold EvenSite; dsimp only; omega)]
    simp only [tG, sG]
    omega
  · intro h
    try dsimp only at h
    rw [FLatticePaper.Induction.mem_closedPolygon_iff,
      if_pos (show EvenSite (0 - 1, 1) from by unfold EvenSite; dsimp only; omega)] at h
    simp only [tG, sG] at h
    omega
  · simp only [sG]
    unfold ChildFrame.vSpectrum
    omega

theorem fH20 (frame : ChildFrame) : (2, 0) ∈ frame.freeH := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  obtain ⟨hT, hT2⟩ := period_bound frame
  have hodd : frame.child.num % 2 = 1 := FLatticePaper.FanInputs.num_odd frame
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  simp only [ChildFrame.freeH, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [FLatticePaper.Induction.mem_closedPolygon_iff,
      if_pos (show EvenSite (2, 0) from by unfold EvenSite; dsimp only; omega)]
    simp only [tG, sG]
    omega
  · intro h
    try dsimp only at h
    rw [FLatticePaper.Induction.mem_closedPolygon_iff,
      if_neg (show ¬ EvenSite (2, 0 - 1) from by unfold EvenSite; dsimp only; omega)] at h
    simp only [tG, sG] at h
    omega
  · simp only [tG]
    unfold ChildFrame.hSpectrum
    left
    omega

theorem fHL (frame : ChildFrame) : (frame.child.den, frame.child.num - 1) ∈ frame.freeH := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  obtain ⟨hT, hT2⟩ := period_bound frame
  have hodd : frame.child.num % 2 = 1 := FLatticePaper.FanInputs.num_odd frame
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have tHL : frame.tGrade (frame.child.den, frame.child.num - 1) = frame.child.den := by rw [tG]; ring
  have sHL : frame.sGrade (frame.child.den, frame.child.num - 1)
      = frame.child.periodDenominator - frame.child.den + frame.child.num := by
    rw [sG, hT]
    ring
  have t2 : frame.tGrade (frame.child.den, frame.child.num - 1 - 1) = 2 * frame.child.den := by rw [tG]; ring
  simp only [ChildFrame.freeH, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [FLatticePaper.Induction.mem_closedPolygon_iff,
      if_neg (show ¬ EvenSite (frame.child.den, frame.child.num - 1) from by unfold EvenSite; dsimp only; omega)]
    rw [tHL, sHL]
    omega
  · intro h
    try dsimp only at h
    rw [FLatticePaper.Induction.mem_closedPolygon_iff,
      if_pos (show EvenSite (frame.child.den, frame.child.num - 1 - 1) from by unfold EvenSite; dsimp only; omega)] at h
    rw [t2] at h
    omega
  · rw [tHL]
    unfold ChildFrame.hSpectrum
    right
    omega

theorem fHP (frame : ChildFrame) : (frame.child.den - 1, frame.child.num - 1) ∈ frame.freeH := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  obtain ⟨hT, hT2⟩ := period_bound frame
  have hodd : frame.child.num % 2 = 1 := FLatticePaper.FanInputs.num_odd frame
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have tHP : frame.tGrade (frame.child.den - 1, frame.child.num - 1) = frame.child.den - frame.child.num := by
    rw [tG]; ring
  have sHP : frame.sGrade (frame.child.den - 1, frame.child.num - 1)
      = frame.child.periodDenominator - 2 * frame.child.den := by
    rw [sG, hT]; ring
  have t2 : frame.tGrade (frame.child.den - 1, frame.child.num - 1 - 1) = 2 * frame.child.den - frame.child.num := by
    rw [tG]; ring
  simp only [ChildFrame.freeH, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [FLatticePaper.Induction.mem_closedPolygon_iff,
      if_pos (show EvenSite (frame.child.den - 1, frame.child.num - 1) from by unfold EvenSite; dsimp only; omega)]
    rw [tHP, sHP]
    omega
  · intro h
    try dsimp only at h
    rw [FLatticePaper.Induction.mem_closedPolygon_iff,
      if_neg (show ¬ EvenSite (frame.child.den - 1, frame.child.num - 1 - 1) from by unfold EvenSite; dsimp only; omega)] at h
    rw [t2] at h
    omega
  · rw [tHP]
    unfold ChildFrame.hSpectrum
    left
    omega

theorem fVL (frame : ChildFrame) : (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 1) ∈ frame.freeV := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  obtain ⟨hT, hT2⟩ := period_bound frame
  have hodd : frame.child.num % 2 = 1 := FLatticePaper.FanInputs.num_odd frame
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have tVL : frame.tGrade (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 1)
      = -frame.child.periodDenominator + frame.child.den + frame.child.num := by
    rw [tG, hT]; ring
  have sVL : frame.sGrade (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 1)
      = 2 * frame.child.num := by
    rw [sG]; ring
  have sVLl : frame.sGrade (frame.child.num - frame.child.den + 1 - 1, frame.child.num + frame.child.den - 1)
      = frame.child.num - frame.child.den := by
    rw [sG]; ring
  simp only [ChildFrame.freeV, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [FLatticePaper.Induction.mem_closedPolygon_iff,
      if_pos (show EvenSite (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 1) from by
        unfold EvenSite; dsimp only; omega)]
    rw [tVL, sVL]
    omega
  · intro h
    try dsimp only at h
    rw [FLatticePaper.Induction.mem_closedPolygon_iff,
      if_neg (show ¬ EvenSite (frame.child.num - frame.child.den + 1 - 1, frame.child.num + frame.child.den - 1) from by
        unfold EvenSite; dsimp only; omega)] at h
    rw [sVLl] at h
    omega
  · rw [sVL]
    unfold ChildFrame.vSpectrum
    omega

theorem fVP (frame : ChildFrame) : (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) ∈ frame.freeV := by
  obtain ⟨hn0, hnd, hdn2, hd3, -⟩ := frame.child_facts
  obtain ⟨hT, hT2⟩ := period_bound frame
  have hodd : frame.child.num % 2 = 1 := FLatticePaper.FanInputs.num_odd frame
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have tVP : frame.tGrade (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2)
      = -frame.child.periodDenominator + frame.child.num + 2 * frame.child.den := by
    rw [tG, hT]; ring
  have sVP : frame.sGrade (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2)
      = 3 * frame.child.num - frame.child.den := by
    rw [sG]; ring
  have sVPl : frame.sGrade (frame.child.num - frame.child.den + 1 - 1, frame.child.num + frame.child.den - 2)
      = -2 * (frame.child.den - frame.child.num) := by
    rw [sG]; ring
  simp only [ChildFrame.freeV, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [FLatticePaper.Induction.mem_closedPolygon_iff,
      if_neg (show ¬ EvenSite (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) from by
        unfold EvenSite; dsimp only; omega)]
    rw [tVP, sVP]
    omega
  · intro h
    try dsimp only at h
    rw [FLatticePaper.Induction.mem_closedPolygon_iff,
      if_pos (show EvenSite (frame.child.num - frame.child.den + 1 - 1, frame.child.num + frame.child.den - 2) from by
        unfold EvenSite; dsimp only; omega)] at h
    rw [sVPl] at h
    omega
  · rw [sVP]
    unfold ChildFrame.vSpectrum
    omega

/-- **The endpoint facts from the strips and the spectra.** -/
theorem endpointFacts_of_strips {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) : EndpointFacts frame G :=
  { b11 := lap_b11 hS, b0m2 := lap_b0m2 hS, bm10 := lap_bm10 hS, b2m1 := lap_b2m1 hS,
    w10 := lap_w10 hS, w00 := lap_w00 hS, w01 := lap_w01 hS, w20 := lap_w20 hS,
    w0m1 := lap_w0m1 hS, wm11 := lap_wm11 hS, w1m1 := lap_w1m1 hS, w1m2 := lap_w1m2 hS,
    fH10 := fH10 frame, fV00 := fV00 frame, fV01 := fV01 frame, fH20 := fH20 frame,
    wHL := lap_hL hS, fHL := fHL frame, wHP := lap_hP hS, fHP := fHP frame,
    wVL := lap_vL hS, fVL := fVL frame, wVP := lap_vP hS, fVP := fVP frame }

end FLatticePaper.EndpointStrips
