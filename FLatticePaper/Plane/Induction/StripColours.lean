import FLatticePaper.Plane.Induction.Binary
import FLatticePaper.Plane.Induction.DeckSelection

/-! # The strip colours: `laplacian = -1` at the black sites of a binary standard field

If a field `G` has the zero strip and the harmonic strip of a child frame (`frame.HasStrips G`), its Laplacian is `-1` at the
four seeds `(1,1)`, `(-1,0)`, `(0,-2)`, `(2,-1)`. Each is read off its five-point stencil from the strip values alone (no
reflection is needed).

The translates `(d-1, n)`, `R - (1,1) = (n, 2n+d-2)` (with `R = (n+1, 2n+d-1)`) and `vLast + (1,0) = V + (2,-1)` (with
`V = (n-d, n+d)`) follow from the seeds by the deck span: the modified deck's kernel is `(d, n)` because `n + d` is even, its
transverse vector is `(n-d, n+d)`, and `DeckSelection.laplacian_add_span` gives Laplacian periodicity along both. -/

namespace FLatticePaper.StripColours

open FLatticePaper FLatticePaper.Induction FLatticePaper.Farey FLatticePaper.DeckSelection

/-- The Laplacian at an even site, as the two horizontal differences. -/
theorem lap_of_even {G : Field} {x : Site} (h : EvenSite x) :
    laplacian G x = (G (x.1 - 1, x.2) - G x) + (G (x.1 + 1, x.2) - G x) := by
  unfold laplacian
  simp only [incomingNeg, incomingPos, if_pos h]

/-- The Laplacian at an odd site, as the two vertical differences. -/
theorem lap_of_odd {G : Field} {x : Site} (h : ¬ EvenSite x) :
    laplacian G x = (G (x.1, x.2 - 1) - G x) + (G (x.1, x.2 + 1) - G x) := by
  unfold laplacian
  simp only [incomingNeg, incomingPos, if_neg h]

/-- The even stencil with its two neighbours named. -/
theorem lap_of_even' {G : Field} {x a b : Site} (h : EvenSite x) (ha : a = (x.1 - 1, x.2))
    (hb : b = (x.1 + 1, x.2)) : laplacian G x = (G a - G x) + (G b - G x) := by
  subst ha hb
  exact lap_of_even h

/-- The odd stencil with its two neighbours named. -/
theorem lap_of_odd' {G : Field} {x a b : Site} (h : ¬ EvenSite x) (ha : a = (x.1, x.2 - 1))
    (hb : b = (x.1, x.2 + 1)) : laplacian G x = (G a - G x) + (G b - G x) := by
  subst ha hb
  exact lap_of_odd h

/-- The seed `(1,1)`: `G(1,1) = 0` (zero strip, `t = n - d`), `G(0,1) = h0(0,1) = -1` (harmonic, `s = d - n`),
`G(2,1) = 0` (zero strip, `t = 2n - d`). -/
theorem lap_one_one (frame : ChildFrame) {G : Field} (hS : frame.HasStrips G) :
    laplacian G (1, 1) = -1 := by
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := frame.child_facts
  have hev : EvenSite ((1 : ℤ), (1 : ℤ)) := by unfold EvenSite; norm_num
  have z1 : G (1, 1) = 0 := hS.1 _ (by simp only [ChildFrame.tGrade]; omega)
    (by simp only [ChildFrame.tGrade]; omega)
  have z2 : G (2, 1) = 0 := hS.1 _ (by simp only [ChildFrame.tGrade]; omega)
    (by simp only [ChildFrame.tGrade]; omega)
  have h01 : G (0, 1) = -1 := by
    rw [hS.2 _ (by simp only [ChildFrame.sGrade]; omega) (by simp only [ChildFrame.sGrade]; omega)]
    norm_num [harmonicGrid]
  rw [lap_of_even' hev (a := (0, 1)) (b := (2, 1)) (by norm_num) (by norm_num), z1, h01, z2]
  norm_num

/-- The seed `(-1,0)`: `G(-1,0) = 0` (zero strip, `t = -n`), `G(-1,-1) = 0` (zero strip, `t = d - n`), `G(-1,1) = h0(-1,1) = -1`
(harmonic, `s = -2n`). -/
theorem lap_neg_one_zero (frame : ChildFrame) {G : Field} (hS : frame.HasStrips G) :
    laplacian G (-1, 0) = -1 := by
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := frame.child_facts
  have hodd : ¬ EvenSite ((-1 : ℤ), (0 : ℤ)) := by unfold EvenSite; norm_num
  have z0 : G (-1, 0) = 0 := hS.1 _ (by simp only [ChildFrame.tGrade]; omega)
    (by simp only [ChildFrame.tGrade]; omega)
  have zm : G (-1, -1) = 0 := hS.1 _ (by simp only [ChildFrame.tGrade]; omega)
    (by simp only [ChildFrame.tGrade]; omega)
  have hp : G (-1, 1) = -1 := by
    rw [hS.2 _ (by simp only [ChildFrame.sGrade]; omega) (by simp only [ChildFrame.sGrade]; omega)]
    norm_num [harmonicGrid]
  rw [lap_of_odd' hodd (a := (-1, -1)) (b := (-1, 1)) (by norm_num) (by norm_num), z0, zm, hp]
  norm_num

/-- The seed `(0,-2)`: `G(0,-2) = 0` (zero strip, `t = 2d`), `G(-1,-2) = 0` (zero strip, `t = 2d - n`), `G(1,-2) = h0(1,-2) = -1`
(harmonic, `s = 3n - d`). -/
theorem lap_zero_neg_two (frame : ChildFrame) {G : Field} (hS : frame.HasStrips G) :
    laplacian G (0, -2) = -1 := by
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := frame.child_facts
  have hev : EvenSite ((0 : ℤ), (-2 : ℤ)) := by unfold EvenSite; norm_num
  have z0 : G (0, -2) = 0 := hS.1 _ (by simp only [ChildFrame.tGrade]; omega)
    (by simp only [ChildFrame.tGrade]; omega)
  have zm : G (-1, -2) = 0 := hS.1 _ (by simp only [ChildFrame.tGrade]; omega)
    (by simp only [ChildFrame.tGrade]; omega)
  have hp : G (1, -2) = -1 := by
    rw [hS.2 _ (by simp only [ChildFrame.sGrade]; omega) (by simp only [ChildFrame.sGrade]; omega)]
    norm_num [harmonicGrid]
  rw [lap_of_even' hev (a := (-1, -2)) (b := (1, -2)) (by norm_num) (by norm_num), z0, zm, hp]
  norm_num

/-- The seed `(2,-1)`: `G(2,-1) = 0` (zero strip, `t = 2n + d`), `G(2,-2) = h0(2,-2) = -1` (harmonic, `s = 4n`), `G(2,0) = 0`
(zero strip, `t = 2n`). -/
theorem lap_two_neg_one (frame : ChildFrame) {G : Field} (hS : frame.HasStrips G) :
    laplacian G (2, -1) = -1 := by
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := frame.child_facts
  have hodd : ¬ EvenSite ((2 : ℤ), (-1 : ℤ)) := by unfold EvenSite; norm_num
  have z0 : G (2, -1) = 0 := hS.1 _ (by simp only [ChildFrame.tGrade]; omega)
    (by simp only [ChildFrame.tGrade]; omega)
  have zt : G (2, 0) = 0 := hS.1 _ (by simp only [ChildFrame.tGrade]; omega)
    (by simp only [ChildFrame.tGrade]; omega)
  have hb : G (2, -2) = -1 := by
    rw [hS.2 _ (by simp only [ChildFrame.sGrade]; omega) (by simp only [ChildFrame.sGrade]; omega)]
    norm_num [harmonicGrid]
  rw [lap_of_odd' hodd (a := (2, -2)) (b := (2, 0)) (by norm_num) (by norm_num), z0, zt, hb]
  norm_num

/-! ### The deck: the kernel is `(d, n)` and the transverse vector is `(n-d, n+d)` -/

/-- The modified deck's kernel is `(d, n)`, since `n + d` is even (the multiplicity is `1`). -/
theorem kernel_eq (frame : ChildFrame) :
    frame.child.modifiedDeck.kernel = (frame.child.den, frame.child.num) := by
  have hm : frame.child.periodMultiplicity = 1 := by
    have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
    unfold Fraction.periodMultiplicity
    rw [if_pos hpar]
  simp only [Fraction.modifiedDeck, hm, one_mul]

/-- The modified deck's transverse vector is `(n-d, n+d)`. -/
theorem transverse_eq (frame : ChildFrame) :
    frame.child.modifiedDeck.transverse = (frame.child.num - frame.child.den, frame.child.num + frame.child.den) :=
  rfl

/-- The Laplacian is periodic under translation by `(d, n)`. -/
theorem lap_add_kernel (frame : ChildFrame) {G : Field} {cU cV : ℤ}
    (hF : HasGeneratorPeriods frame.child G cU cV) (x : Site) :
    laplacian G (x + (frame.child.den, frame.child.num)) = laplacian G x := by
  have h := laplacian_add_span frame hF 1 0 x
  rw [kernel_eq frame] at h
  simpa using h

/-- The Laplacian is periodic under translation by the transverse vector `(n-d, n+d)`. -/
theorem lap_add_transverse (frame : ChildFrame) {G : Field} {cU cV : ℤ}
    (hF : HasGeneratorPeriods frame.child G cU cV) (x : Site) :
    laplacian G (x + (frame.child.num - frame.child.den, frame.child.num + frame.child.den)) = laplacian G x := by
  have h := laplacian_add_span frame hF 0 1 x
  rw [transverse_eq frame] at h
  simpa using h

/-! ### The translates -/

/-- `(d-1, n) = (-1, 0) + (d, n)`. -/
theorem lap_den_sub_one (frame : ChildFrame) {G : Field} {cU cV : ℤ} (hS : frame.HasStrips G)
    (hF : HasGeneratorPeriods frame.child G cU cV) :
    laplacian G (frame.child.den - 1, frame.child.num) = -1 := by
  have h := lap_add_kernel frame hF (-1, 0)
  have e : ((-1 : ℤ), (0 : ℤ)) + (frame.child.den, frame.child.num) = (frame.child.den - 1, frame.child.num) :=
    Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
  rw [e, lap_neg_one_zero frame hS] at h
  exact h

/-- `R - (1,1) = (n, 2n+d-2)`, with `R = (n+1, 2n+d-1)`: `(0,-2) + (d, n) + (n-d, n+d)`. -/
theorem lap_R_sub_one_one (frame : ChildFrame) {G : Field} {cU cV : ℤ} (hS : frame.HasStrips G)
    (hF : HasGeneratorPeriods frame.child G cU cV) :
    laplacian G (frame.child.num, 2 * frame.child.num + frame.child.den - 2) = -1 := by
  have h1 := lap_add_kernel frame hF (0, -2)
  have h2 := lap_add_transverse frame hF ((0, -2) + (frame.child.den, frame.child.num))
  have e : ((0 : ℤ), (-2 : ℤ)) + (frame.child.den, frame.child.num)
      + (frame.child.num - frame.child.den, frame.child.num + frame.child.den)
      = (frame.child.num, 2 * frame.child.num + frame.child.den - 2) :=
    Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
  rw [e] at h2
  rw [h2, h1, lap_zero_neg_two frame hS]

/-- `vLast + (1,0) = (2,-1) + (n-d, n+d)`: the east middle of `vLast` is the translate `V + (2,-1)`. -/
theorem lap_vLast_east (frame : ChildFrame) {G : Field} {cU cV : ℤ} (hS : frame.HasStrips G)
    (hF : HasGeneratorPeriods frame.child G cU cV) :
    laplacian G (frame.vLast.1 + 1, frame.vLast.2) = -1 := by
  have h := lap_add_transverse frame hF (2, -1)
  have e : ((2 : ℤ), (-1 : ℤ)) + (frame.child.num - frame.child.den, frame.child.num + frame.child.den)
      = (frame.vLast.1 + 1, frame.vLast.2) :=
    Prod.ext (by simp only [ChildFrame.vLast, Prod.fst_add]; ring) (by simp only [ChildFrame.vLast, Prod.snd_add]; ring)
  rw [e] at h
  rw [h, lap_two_neg_one frame hS]

end FLatticePaper.StripColours
