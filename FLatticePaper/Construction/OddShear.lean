import FLatticePaper.Construction.OddAlternateCopies

/-! # The shear identity of the odd alternate copies (task 46)

The raw odd alternate target of `w` and the standard odd target of its first copy differ, on the sites of the first copy, by a
constant. The identity has three ingredients, each proved here:

* the parents of the swapped word `u = w.map swap` are explicit in the parents of `w`: `even(u) = (D − N, N + D)` for the odd parent
  `(N, D)` of `w` (`parentsAt_swap_spec`, by induction on the word);
* the standard field of `u` has the kernel period `U = (den, num)` of the child of `u` with zero constant (the packet of the
  standard field, `ChildFrame.coherentConstantU_eq_zero`), and `Rot(oT) = σ_u − U` (the transverse vector of the odd parent of `w`,
  rotated, is the midpoint shift of `u` minus that period), so the two sheets of the midpoint are equal at the rotated points;
* the harmonic grid changes by a linear function `−(N y1 − D y2)` under the shift `oT`, which cancels the slope of the odd target.

Consequence (phase one): on the sites where the gap of `u` at the quarter-turned point lies in `[1, 2]`, the raw odd target is the
standard odd target at the chart-shifted point, plus one and a constant. -/

namespace FLatticePaper.Construction

open Farey FLatticePaper FLatticePaper.Induction HeightTile

/-! ## The parents of the swapped word -/

theorem count_one_map_swap (w : Word) :
    (w.map Digit.swapTwoThree).count Digit.one = w.count Digit.one := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [Digit.swapTwoThree, ih]

theorem phase_map_swap (w : Word) : phase (w.map Digit.swapTwoThree) = phase w := by
  unfold phase
  rw [count_one_map_swap]

/-- The parents of the swapped word, in terms of the parents of the word (for all words): the odd parent of the swapped word has
`2 · num = den(even) − num(even)` and `2 · den = num(even) + den(even)`, and the even parent of the swapped word is
`(den(odd) − num(odd), num(odd) + den(odd))`. -/
theorem parentsAt_swap_spec (w : Word) :
    2 * (parentsAt (w.map Digit.swapTwoThree)).odd.num = (parentsAt w).even.den - (parentsAt w).even.num ∧
    2 * (parentsAt (w.map Digit.swapTwoThree)).odd.den = (parentsAt w).even.num + (parentsAt w).even.den ∧
    (parentsAt (w.map Digit.swapTwoThree)).even.num = (parentsAt w).odd.den - (parentsAt w).odd.num ∧
    (parentsAt (w.map Digit.swapTwoThree)).even.den = (parentsAt w).odd.num + (parentsAt w).odd.den := by
  induction w using List.reverseRecOn with
  | nil => simp [parentsAt, Parents.walk, root]
  | append_singleton w d ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [List.map_append, List.map_cons, List.map_nil, parentsAt_append_singleton]
    cases d <;> simp [Parents.step, Parents.current, Parents.combine, Digit.swapTwoThree] <;> omega

/-! ## The kernel period of the standard field of a word -/

/-- The kernel period of the child frame of a word is `(den, num)` of the even parent: the modified deck of an even fraction has
multiplicity one. -/
theorem child_modifiedDeck_kernel_eq (u : Word) :
    (frameAt u).child.modifiedDeck.kernel = ((frameAt u).child.den, (frameAt u).child.num) := by
  have hev : ((frameAt u).child.num + (frameAt u).child.den) % 2 = 0 := by
    have h := (parentsAt_valid u).current_even_parity
    exact h
  unfold Fraction.modifiedDeck Fraction.periodMultiplicity
  simp [hev]

/-- **The standard field of a word is periodic along the kernel of its child**, with zero constant (from the packet of the standard
field, which is a hypothesis of the development, and the zero constant of the child frame). -/
theorem standardField_child_kernel_period (u : Word) (hpk : (frameAt u).Packet (standardField u)) (y : Site) :
    standardField u (y + ((frameAt u).child.den, (frameAt u).child.num)) = standardField u y := by
  have hU := hpk.periods.1 y
  rw [child_modifiedDeck_kernel_eq, ChildFrame.coherentConstantU_eq_zero] at hU
  simpa using hU

/-! ## The harmonic grid under the transverse shift of the odd parent -/

/-- The harmonic grid changes by the linear function `−(N y1 − D y2)` under the shift by `(N − D, N + D)`, up to a constant. -/
theorem harmonicGrid_shift (N D : ℤ) :
    ∃ c : ℤ, ∀ y : Site, harmonicGrid (y - (N - D, N + D)) = harmonicGrid y - (N * y.1 - D * y.2) + c := by
  obtain ⟨p, hp⟩ := Int.even_mul_succ_self N
  obtain ⟨q, hq⟩ := Int.even_mul_succ_self (D - 1)
  refine ⟨p - q - N * D, fun y => ?_⟩
  unfold harmonicGrid
  simp only [Prod.fst_sub, Prod.snd_sub]
  have hmod : ((y.1 - (N - D)) + (y.2 - (N + D))) % 2 = (y.1 + y.2) % 2 := by
    omega
  rw [hmod]
  have hnum : (y.1 - (N - D)) ^ 2 + 2 * (y.1 - (N - D)) * (y.2 - (N + D)) - (y.2 - (N + D)) ^ 2
      - 2 * (y.2 - (N + D)) - (y.1 + y.2) % 2 =
      (y.1 ^ 2 + 2 * y.1 * y.2 - y.2 ^ 2 - 2 * y.2 - (y.1 + y.2) % 2) +
        (-(N * y.1) + D * y.2 + (p - q - N * D)) * 4 := by
    have hp' : N * (N + 1) = p + p := hp
    have hq' : (D - 1) * (D - 1 + 1) = q + q := hq
    linear_combination (2 : ℤ) * hp' - (2 : ℤ) * hq'
  rw [hnum, Int.add_mul_ediv_right _ _ (by norm_num : (4 : ℤ) ≠ 0)]
  ring

/-! ## The shear identity of the first copy (phase one) -/

/-- The standard odd target of a word is the quarter turn of the standard field of the swapped word. -/
theorem planeTarget_odd_eq (w : Word) :
    planeTarget w .odd = quarterTurnField (standardField (w.map Digit.swapTwoThree)) := by
  unfold planeTarget
  rw [oddBirthPrefix_append_one]

/-- The sigma of the swapped word is the transverse vector of the odd parent of the word plus the kernel period of the child of the swapped
word, in phase one. -/
theorem alternateSigma_eq_rot_add_period (w : Word) (hph : phase w = 1) :
    alternateSigma (w.map Digit.swapTwoThree) =
      (-((parentsAt w).odd.num + (parentsAt w).odd.den), (parentsAt w).odd.num - (parentsAt w).odd.den) +
        ((frameAt (w.map Digit.swapTwoThree)).child.den, (frameAt (w.map Digit.swapTwoThree)).child.num) := by
  have hphu : phase (w.map Digit.swapTwoThree) = 1 := (phase_map_swap w).trans hph
  have hsig : alternateSigma (w.map Digit.swapTwoThree) =
      (2 * (parentsAt (w.map Digit.swapTwoThree)).odd.den, 2 * (parentsAt (w.map Digit.swapTwoThree)).odd.num) := by
    unfold alternateSigma
    rw [frameAt_eps, if_neg (by rw [hphu]; norm_num)]
    simp
  have hchild : (frameAt (w.map Digit.swapTwoThree)).child =
      ((parentsAt (w.map Digit.swapTwoThree)).current .even) := rfl
  obtain ⟨_, _, h3, h4⟩ := parentsAt_swap_spec w
  have hcd : (frameAt (w.map Digit.swapTwoThree)).child.den =
      2 * (parentsAt (w.map Digit.swapTwoThree)).odd.den + (parentsAt (w.map Digit.swapTwoThree)).even.den := by
    rw [hchild]
    simp [Parents.current, Parents.combine]
  have hcn : (frameAt (w.map Digit.swapTwoThree)).child.num =
      2 * (parentsAt (w.map Digit.swapTwoThree)).odd.num + (parentsAt (w.map Digit.swapTwoThree)).even.num := by
    rw [hchild]
    simp [Parents.current, Parents.combine]
  rw [hsig, hcd, hcn, h3, h4]
  ext
  · simp
    ring
  · simp
    ring

/-- On a gap of at least one, the minimum of `a` and `b + 1` is `b + 1`. -/
theorem min_shear_aux (a b : ℤ) (h : 1 ≤ a - b) : min a (b + 1) = b + 1 :=
  min_eq_right (by linarith)

/-- **The shear identity, phase one.** On the sites where the gap of the swapped word at the quarter-turned point lies in `[1, 2]`, the
raw odd alternate target is the standard odd target at the chart-shifted point, plus `1` and a constant (independent of the site). -/
theorem alternateOddRawTarget_eq_planeTarget_add_one (w : Word) (hph : phase w = 1)
    (hpk : (frameAt (w.map Digit.swapTwoThree)).Packet (standardField (w.map Digit.swapTwoThree))) :
    ∃ c : ℤ, ∀ x : Site,
      1 ≤ standardField (w.map Digit.swapTwoThree)
          (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta w)) -
        standardField (w.map Digit.swapTwoThree)
          (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta w) +
            alternateSigma (w.map Digit.swapTwoThree)) →
      standardField (w.map Digit.swapTwoThree)
          (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta w)) -
        standardField (w.map Digit.swapTwoThree)
          (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta w) +
            alternateSigma (w.map Digit.swapTwoThree)) ≤ 2 →
      alternateOddRawTarget w x = planeTarget w .odd (x - oddStdChart w) + 1 + c := by
  obtain ⟨ch, hch⟩ := harmonicGrid_shift (parentsAt w).odd.num (parentsAt w).odd.den
  refine ⟨ch - ((parentsAt w).odd.num * (parentsAt w).even.den - (parentsAt w).odd.den * (parentsAt w).even.num),
    fun x hg1 hg2 => ?_⟩
  have hδ : alternateOddDelta w = ((parentsAt w).odd.num - (parentsAt w).odd.den - (parentsAt w).even.den,
      (parentsAt w).odd.num + (parentsAt w).odd.den - (parentsAt w).even.num) := by
    unfold alternateOddDelta
    simp [hph, transverseJet, kernelJet]
  have hchart : oddStdChart w = (-(parentsAt w).even.den, -(parentsAt w).even.num) := by
    unfold oddStdChart
    simp [hph, kernelJet]
  have hslope : alternateOddSlope w = ((parentsAt w).odd.num, -(parentsAt w).odd.den) := by
    unfold alternateOddSlope
    simp [hph]
  have hzrot : QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta w) +
      (-((parentsAt w).odd.num + (parentsAt w).odd.den), (parentsAt w).odd.num - (parentsAt w).odd.den) =
      QuarterTurn.counterclockwise.mapSite (0, -1) (x - oddStdChart w) := by
    rw [quarterTurn_site, quarterTurn_site, hδ, hchart]
    ext
    · simp
      ring
    · simp
      ring
  have hσ := alternateSigma_eq_rot_add_period w hph
  have hper : ∀ y : Site, standardField (w.map Digit.swapTwoThree)
      (y + ((frameAt (w.map Digit.swapTwoThree)).child.den, (frameAt (w.map Digit.swapTwoThree)).child.num)) =
      standardField (w.map Digit.swapTwoThree) y :=
    fun y => standardField_child_kernel_period _ hpk y
  have hFσ : standardField (w.map Digit.swapTwoThree)
      (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta w) +
        alternateSigma (w.map Digit.swapTwoThree)) =
      standardField (w.map Digit.swapTwoThree)
        (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta w) +
          (-((parentsAt w).odd.num + (parentsAt w).odd.den), (parentsAt w).odd.num - (parentsAt w).odd.den)) := by
    rw [hσ, ← add_assoc]
    exact hper _
  have hh : harmonicGrid (x - alternateOddDelta w) =
      harmonicGrid (x - oddStdChart w) -
        ((parentsAt w).odd.num * (x - oddStdChart w).1 - (parentsAt w).odd.den * (x - oddStdChart w).2) + ch := by
    rw [← hch]
    congr 1
    rw [hδ, hchart]
    ext
    · simp
      ring
    · simp
      ring
  have hmin : alternateTarget (w.map Digit.swapTwoThree)
      (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta w)) =
      standardField (w.map Digit.swapTwoThree)
        (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta w) +
          alternateSigma (w.map Digit.swapTwoThree)) + 1 := by
    rw [alternateTarget_eq_min (word := w.map Digit.swapTwoThree)
      (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta w)) (by linarith) hg2,
      min_shear_aux _ _ hg1]
  have hS : standardField (w.map Digit.swapTwoThree)
      (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta w) +
        alternateSigma (w.map Digit.swapTwoThree)) =
      standardField (w.map Digit.swapTwoThree)
        (QuarterTurn.counterclockwise.mapSite (0, -1) (x - oddStdChart w)) := by
    rw [hFσ, hzrot]
  unfold alternateOddRawTarget
  rw [planeTarget_odd_eq]
  unfold quarterTurnField
  rw [hmin, hS, hh, hslope]
  simp only [hchart, Prod.fst_sub, Prod.snd_sub]
  ring

/-! ## The first copy of the odd alternate, from the shear identity -/

/-- The gap of the swapped word at the quarter-turned point of a site: the drop of the standard field of the swapped word between the
point and its `σ`-translate. -/
noncomputable def shearGap (w : Word) (s : Site) : ℤ :=
  standardField (w.map Digit.swapTwoThree)
      (QuarterTurn.counterclockwise.mapSite (0, -1) (s - alternateOddDelta w)) -
    standardField (w.map Digit.swapTwoThree)
      (QuarterTurn.counterclockwise.mapSite (0, -1) (s - alternateOddDelta w) + alternateSigma (w.map Digit.swapTwoThree))

/-- **The first copy of the odd ordinary alternate agrees with the raw odd target in phase one**, with the shear constant supplied by
the shear identity. The only named input left on the copy's sites is the window `1 ≤ gap ≤ 2` (the sheet fact of the first copy). -/
theorem ordinaryAlternate_odd_first_agrees_of_gap (parents : TileParents) (beforePush : Word) (digit : Digit) {g : ℤ}
    (hph : phase (beforePush ++ [digit]) = 1)
    (hpk : (frameAt ((beforePush ++ [digit]).map Digit.swapTwoThree)).Packet
      (standardField ((beforePush ++ [digit]).map Digit.swapTwoThree)))
    (hstd : (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 0).val.Agrees
      (fun y => planeTarget (beforePush ++ [digit]) .odd (y - oddStdChart (beforePush ++ [digit]))) g)
    (hgap : ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 0).val.sites,
      1 ≤ shearGap (beforePush ++ [digit]) s ∧ shearGap (beforePush ++ [digit]) s ≤ 2) :
    ∃ k : ℤ, (ordinaryAlternateSchedule parents beforePush digit .odd).first.val.Agrees
      (alternateOddRawTarget (beforePush ++ [digit])) (g - k) := by
  obtain ⟨c, hc⟩ := alternateOddRawTarget_eq_planeTarget_add_one (beforePush ++ [digit]) hph hpk
  refine ⟨1 + c, ordinaryAlternate_odd_first_agrees parents beforePush digit hstd ?_⟩
  intro s hs
  have h := hgap s hs
  rw [hc s h.1 h.2]
  ring

/-! ## Phase zero: the shear and the copies that are F-pure -/

theorem oddStdChart_phase_zero (w : Word) (h : phase w = 0) : oddStdChart w = 0 := by
  unfold oddStdChart
  simp [h]

/-- **The phase-zero shear.** In phase zero the odd target is the standard odd target at zero shift, and on the window
`0 ≤ gap ≤ 2` the raw odd target is that target plus `min 0 (1 − gap)`: the gap is the drop of the standard field of the swapped word
at the quarter-turned point, and the alternate target takes the minimum of the field and its translate plus one. -/
theorem alternateOddRawTarget_eq_planeTarget_phase_zero (w : Word) (hph : phase w = 0) (x : Site)
    (h0 : 0 ≤ shearGap w x) (h2 : shearGap w x ≤ 2) :
    alternateOddRawTarget w x = planeTarget w .odd x + min 0 (1 - shearGap w x) := by
  have hδ : alternateOddDelta w = 0 := by
    unfold alternateOddDelta
    simp [hph]
  have hs : alternateOddSlope w = 0 := by
    unfold alternateOddSlope
    simp [hph]
  have hg : shearGap w x =
      standardField (w.map Digit.swapTwoThree) (QuarterTurn.counterclockwise.mapSite (0, -1) x) -
        standardField (w.map Digit.swapTwoThree)
          (QuarterTurn.counterclockwise.mapSite (0, -1) x + alternateSigma (w.map Digit.swapTwoThree)) := by
    unfold shearGap
    rw [hδ, sub_zero]
  have hmin : alternateTarget (w.map Digit.swapTwoThree) (QuarterTurn.counterclockwise.mapSite (0, -1) x) =
      min (standardField (w.map Digit.swapTwoThree) (QuarterTurn.counterclockwise.mapSite (0, -1) x))
        (standardField (w.map Digit.swapTwoThree)
          (QuarterTurn.counterclockwise.mapSite (0, -1) x + alternateSigma (w.map Digit.swapTwoThree)) + 1) :=
    alternateTarget_eq_min (QuarterTurn.counterclockwise.mapSite (0, -1) x) (by linarith) (by linarith)
  unfold alternateOddRawTarget
  rw [planeTarget_odd_eq, hδ, hs]
  unfold quarterTurnField
  simp only [sub_zero, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero]
  rw [hmin]
  omega

/-- **The first copy of the odd ordinary alternate agrees with the raw odd target in phase zero**, on the window `0 ≤ gap ≤ 1`
of its sites (the copy is F-pure there, and the shear constant is zero). -/
theorem ordinaryAlternate_odd_first_agrees_phase_zero (parents : TileParents) (beforePush : Word) (digit : Digit) {g : ℤ}
    (hph : phase (beforePush ++ [digit]) = 0)
    (hstd : (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 0).val.Agrees
      (fun y => planeTarget (beforePush ++ [digit]) .odd (y - oddStdChart (beforePush ++ [digit]))) g)
    (hgap : ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 0).val.sites,
      0 ≤ shearGap (beforePush ++ [digit]) s ∧ shearGap (beforePush ++ [digit]) s ≤ 1) :
    (ordinaryAlternateSchedule parents beforePush digit .odd).first.val.Agrees
      (alternateOddRawTarget (beforePush ++ [digit])) g := by
  have hshear : ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 0).val.sites,
      alternateOddRawTarget (beforePush ++ [digit]) s =
        planeTarget (beforePush ++ [digit]) .odd (s - oddStdChart (beforePush ++ [digit])) + 0 := by
    intro s hs
    have h := hgap s hs
    rw [alternateOddRawTarget_eq_planeTarget_phase_zero _ hph s h.1 (by linarith [h.2]),
      oddStdChart_phase_zero _ hph, sub_zero, min_eq_left (by linarith [h.2]), add_zero]
  simpa using ordinaryAlternate_odd_first_agrees parents beforePush digit hstd hshear

/-- **The copy in slot four of the odd ordinary alternate agrees with the raw odd target in phase zero**, on the window `0 ≤ gap ≤ 1`
of the standard copy five on its sites (F-pure, zero shear). -/
theorem ordinaryAlternate_odd_copy_four_agrees_phase_zero (parents : TileParents) (word : Word) (h : phase word = 0) {g : ℤ}
    (hstd : (ordinaryStandardCopy parents word .odd 5).val.Agrees (planeTarget word .odd) g)
    (hgap : ∀ s ∈ (ordinaryStandardCopy parents word .odd 5).val.sites,
      0 ≤ shearGap word s ∧ shearGap word s ≤ 1) :
    (placedBySlot (alternateJets word .odd) (standardSources parents .even) 4).val.Agrees
      (alternateOddRawTarget word) g := by
  have hshear : ∀ s ∈ (ordinaryStandardCopy parents word .odd 5).val.sites,
      alternateOddRawTarget word s = planeTarget word .odd s + 0 := by
    intro s hs
    have h' := hgap s hs
    rw [alternateOddRawTarget_eq_planeTarget_phase_zero word h s h'.1 (by linarith [h'.2]),
      min_eq_left (by linarith [h'.2]), add_zero]
  simpa using ordinaryAlternate_odd_copy_four_agrees parents word h hstd hshear

/-! ## The copies by their standard type: the G-branch, the chart shear on the whole window, and the coincident copies -/

theorem min_shift_aux (a b : ℤ) : min a (b + 1) = b + min (a - b) 1 := by
  omega

/-- The G-branch standard target of an odd word: the standard field of the swapped word at the quarter-turned point translated by
`σ`, with the harmonic grid and the transverse slope of the raw target. -/
noncomputable def alternateOddGPlane (word : Word) : Field := fun x =>
  standardField (word.map Digit.swapTwoThree)
      (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta word) +
        alternateSigma (word.map Digit.swapTwoThree)) +
    harmonicGrid (x - alternateOddDelta word) +
    ((alternateOddSlope word).1 * x.1 + (alternateOddSlope word).2 * x.2)

/-- **The raw odd target is the G-branch target plus the capped gap**, on the window `0 ≤ gap ≤ 2` (both phases): the alternate target
is `F(· + σ) + min(gap, 1)` there, so the raw target is `alternateOddGPlane + min(gap, 1)` with no constant. -/
theorem alternateOddRawTarget_eq_gPlane_add_min (word : Word) (x : Site)
    (hlo : 0 ≤ shearGap word x) (hhi : shearGap word x ≤ 2) :
    alternateOddRawTarget word x = alternateOddGPlane word x + min (shearGap word x) 1 := by
  have hmin := alternateTarget_eq_min (word := word.map Digit.swapTwoThree)
    (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta word)) hlo hhi
  unfold alternateOddRawTarget alternateOddGPlane quarterTurnField
  rw [hmin, min_shift_aux]
  unfold shearGap
  ring

/-- **A copy on the G-branch agrees with the raw odd target**, with constant `g − 1`, when the gap of its sites lies in `[1, 2]` (there
the capped gap is one). -/
theorem HeightTile.Agrees.alternateOddRawTarget_of_gPlane {word : Word} {tile : HeightTile Site} {g : ℤ}
    (h : tile.Agrees (alternateOddGPlane word) g)
    (hwin : ∀ s ∈ tile.sites, 1 ≤ shearGap word s ∧ shearGap word s ≤ 2) :
    tile.Agrees (alternateOddRawTarget word) (g - 1) := by
  intro s
  have hw := hwin s.1 s.2
  rw [h s, alternateOddRawTarget_eq_gPlane_add_min word s.1 (by linarith [hw.1]) hw.2, min_eq_right hw.1]
  ring

/-- **The chart shear on the whole window** (phase one): on the sites where the gap lies in `[0, 2]`, the raw odd target is the
standard odd target at the chart-shifted point, plus `min(gap, 1)` and a constant independent of the site. -/
theorem alternateOddRawTarget_eq_planeTarget_chart_min (word : Word) (hph : phase word = 1)
    (hpk : (frameAt (word.map Digit.swapTwoThree)).Packet (standardField (word.map Digit.swapTwoThree))) :
    ∃ c : ℤ, ∀ x : Site, 0 ≤ shearGap word x → shearGap word x ≤ 2 →
      alternateOddRawTarget word x = planeTarget word .odd (x - oddStdChart word) + min (shearGap word x) 1 + c := by
  obtain ⟨ch, hch⟩ := harmonicGrid_shift (parentsAt word).odd.num (parentsAt word).odd.den
  refine ⟨ch - ((parentsAt word).odd.num * (parentsAt word).even.den - (parentsAt word).odd.den * (parentsAt word).even.num),
    fun x hg1 hg2 => ?_⟩
  have hδ : alternateOddDelta word = ((parentsAt word).odd.num - (parentsAt word).odd.den - (parentsAt word).even.den,
      (parentsAt word).odd.num + (parentsAt word).odd.den - (parentsAt word).even.num) := by
    unfold alternateOddDelta
    simp [hph, transverseJet, kernelJet]
  have hchart : oddStdChart word = (-(parentsAt word).even.den, -(parentsAt word).even.num) := by
    unfold oddStdChart
    simp [hph, kernelJet]
  have hslope : alternateOddSlope word = ((parentsAt word).odd.num, -(parentsAt word).odd.den) := by
    unfold alternateOddSlope
    simp [hph]
  have hzrot : QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta word) +
      (-((parentsAt word).odd.num + (parentsAt word).odd.den), (parentsAt word).odd.num - (parentsAt word).odd.den) =
      QuarterTurn.counterclockwise.mapSite (0, -1) (x - oddStdChart word) := by
    rw [quarterTurn_site, quarterTurn_site, hδ, hchart]
    ext
    · simp
      ring
    · simp
      ring
  have hσ := alternateSigma_eq_rot_add_period word hph
  have hper : ∀ y : Site, standardField (word.map Digit.swapTwoThree)
      (y + ((frameAt (word.map Digit.swapTwoThree)).child.den, (frameAt (word.map Digit.swapTwoThree)).child.num)) =
      standardField (word.map Digit.swapTwoThree) y :=
    fun y => standardField_child_kernel_period _ hpk y
  have hFσ : standardField (word.map Digit.swapTwoThree)
      (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta word) + alternateSigma (word.map Digit.swapTwoThree)) =
      standardField (word.map Digit.swapTwoThree)
        (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta word) +
          (-((parentsAt word).odd.num + (parentsAt word).odd.den), (parentsAt word).odd.num - (parentsAt word).odd.den)) := by
    rw [hσ, ← add_assoc]
    exact hper _
  have hS : standardField (word.map Digit.swapTwoThree)
      (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta word) + alternateSigma (word.map Digit.swapTwoThree)) =
      standardField (word.map Digit.swapTwoThree) (QuarterTurn.counterclockwise.mapSite (0, -1) (x - oddStdChart word)) := by
    rw [hFσ, hzrot]
  have hh : harmonicGrid (x - alternateOddDelta word) =
      harmonicGrid (x - oddStdChart word) -
        ((parentsAt word).odd.num * (x - oddStdChart word).1 - (parentsAt word).odd.den * (x - oddStdChart word).2) + ch := by
    rw [← hch]
    congr 1
    rw [hδ, hchart]
    ext
    · simp
      ring
    · simp
      ring
  have hmin : alternateTarget (word.map Digit.swapTwoThree)
      (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta word)) =
      standardField (word.map Digit.swapTwoThree)
          (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta word) +
            alternateSigma (word.map Digit.swapTwoThree)) +
        min (standardField (word.map Digit.swapTwoThree)
            (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta word)) -
          standardField (word.map Digit.swapTwoThree)
            (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta word) +
              alternateSigma (word.map Digit.swapTwoThree))) 1 := by
    rw [alternateTarget_eq_min (word := word.map Digit.swapTwoThree)
      (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta word)) hg1 hg2, min_shift_aux]
  unfold shearGap
  unfold alternateOddRawTarget
  rw [planeTarget_odd_eq]
  unfold quarterTurnField
  rw [hmin, hS, hh, hslope]
  simp only [hchart, Prod.fst_sub, Prod.snd_sub]
  ring

/-- **A coincident copy agrees with the raw odd target** (phase one). A copy that is the standard odd target at zero shift, on the
window `0 ≤ gap ≤ 2`, agrees with the raw target when the chart-shifted target plus the capped gap is the zero-shift target plus a
constant `κ` on its sites (the branch identity, named). The agreement constant is `g − κ − c`. -/
theorem HeightTile.Agrees.alternateOddRawTarget_of_coincident {word : Word} (hph : phase word = 1)
    (hpk : (frameAt (word.map Digit.swapTwoThree)).Packet (standardField (word.map Digit.swapTwoThree)))
    {tile : HeightTile Site} {g κ : ℤ}
    (htile : tile.Agrees (planeTarget word .odd) g)
    (hwin : ∀ s ∈ tile.sites, 0 ≤ shearGap word s ∧ shearGap word s ≤ 2)
    (hbr : ∀ s ∈ tile.sites, planeTarget word .odd (s - oddStdChart word) + min (shearGap word s) 1 =
      planeTarget word .odd s + κ) :
    ∃ k : ℤ, tile.Agrees (alternateOddRawTarget word) k := by
  obtain ⟨c, hc⟩ := alternateOddRawTarget_eq_planeTarget_chart_min word hph hpk
  refine ⟨g - κ - c, ?_⟩
  intro s
  have hw := hwin s.1 s.2
  have hb := hbr s.1 s.2
  rw [htile s, hc s.1 hw.1 hw.2, hb]
  ring

/-! ## The sheet facts of the odd alternate copies, and the copy list -/

/-- The tile in slot `k` of the odd ordinary alternate of `w` (the placed copy). -/
noncomputable def oddSlotTile (parents : TileParents) (w : Word) (k : Fin 6) : HeightTile Site :=
  (placedBySlot (alternateJets w .odd) (standardSources parents .even) k).val

/-- **The named sheet facts and window facts of the copies of the odd ordinary alternate of `w`.** Each copy is, on its sites, one of
the standard expressions of the swapped word (the F-branch `alternateOddPlane`, the G-branch `alternateOddGPlane`, or the zero-shift
standard target `planeTarget`), or a copy of the raw target itself; the windows are the gap ranges of the copies on their sites. The
standard identities and windows are checked numerically for the odd words of length at most three
(`scripts/odd_copy_candidates.py`, `scripts/odd_copy_gap.py`). -/
structure OddAlternateFacts (parents : TileParents) (w : Word) : Prop where
  firstStd : ∃ g : ℤ, (ordinaryStandardCopy parents w .odd 0).val.Agrees
    (fun y => planeTarget w .odd (y - oddStdChart w)) g
  firstWin1 : phase w = 1 → ∀ s ∈ (ordinaryStandardCopy parents w .odd 0).val.sites,
    1 ≤ shearGap w s ∧ shearGap w s ≤ 2
  firstWin0 : phase w = 0 → ∀ s ∈ (ordinaryStandardCopy parents w .odd 0).val.sites,
    0 ≤ shearGap w s ∧ shearGap w s ≤ 1
  coStd4 : phase w = 1 → ∃ g : ℤ, (ordinaryStandardCopy parents w .odd 4).val.Agrees (planeTarget w .odd) g
  coWin4 : phase w = 1 → ∀ s ∈ (ordinaryStandardCopy parents w .odd 4).val.sites,
    0 ≤ shearGap w s ∧ shearGap w s ≤ 2
  coBr4 : phase w = 1 → ∀ s ∈ (ordinaryStandardCopy parents w .odd 4).val.sites,
    planeTarget w .odd (s - oddStdChart w) + min (shearGap w s) 1 = planeTarget w .odd s + 1
  coStd5 : phase w = 0 → ∃ g : ℤ, (ordinaryStandardCopy parents w .odd 5).val.Agrees (planeTarget w .odd) g
  coWin5 : phase w = 0 → ∀ s ∈ (ordinaryStandardCopy parents w .odd 5).val.sites,
    0 ≤ shearGap w s ∧ shearGap w s ≤ 1
  plane1 : phase w = 1 → ∃ g : ℤ, (oddSlotTile parents w 1).Agrees (alternateOddPlane w) g
  planeWin1 : phase w = 1 → ∀ s ∈ (oddSlotTile parents w 1).sites, 0 ≤ shearGap w s ∧ shearGap w s ≤ 1
  plane3 : phase w = 1 → ∃ g : ℤ, (oddSlotTile parents w 3).Agrees (alternateOddPlane w) g
  planeWin3 : phase w = 1 → ∀ s ∈ (oddSlotTile parents w 3).sites, 0 ≤ shearGap w s ∧ shearGap w s ≤ 1
  gplane4 : phase w = 1 → ∃ g : ℤ, (oddSlotTile parents w 4).Agrees (alternateOddGPlane w) g
  gWin4 : phase w = 1 → ∀ s ∈ (oddSlotTile parents w 4).sites, 1 ≤ shearGap w s ∧ shearGap w s ≤ 2
  coincident5 : phase w = 1 → ∃ g : ℤ, (oddSlotTile parents w 5).Agrees (planeTarget w .odd) g
  coWin5' : phase w = 1 → ∀ s ∈ (oddSlotTile parents w 5).sites, 0 ≤ shearGap w s ∧ shearGap w s ≤ 2
  coBr5 : phase w = 1 → ∀ s ∈ (oddSlotTile parents w 5).sites,
    planeTarget w .odd (s - oddStdChart w) + min (shearGap w s) 1 = planeTarget w .odd s + 2
  gplane1 : phase w = 0 → ∃ g : ℤ, (oddSlotTile parents w 1).Agrees (alternateOddGPlane w) g
  gWin1 : phase w = 0 → ∀ s ∈ (oddSlotTile parents w 1).sites, 1 ≤ shearGap w s ∧ shearGap w s ≤ 2
  gplane3 : phase w = 0 → ∃ g : ℤ, (oddSlotTile parents w 3).Agrees (alternateOddGPlane w) g
  gWin3 : phase w = 0 → ∀ s ∈ (oddSlotTile parents w 3).sites, 1 ≤ shearGap w s ∧ shearGap w s ≤ 2
  raw2 : phase w = 0 → ∃ k : ℤ, (oddSlotTile parents w 2).Agrees (alternateOddRawTarget w) k
  raw5 : phase w = 0 → ∃ k : ℤ, (oddSlotTile parents w 5).Agrees (alternateOddRawTarget w) k

/-- **The slots of the odd alternate other than the copies two and four (phase one) and two and four (phase zero)**, discharged from the
named sheet facts: in phase one the slots one and three are on the F-branch, slot four on the G-branch, slot five is the coincident
copy; in phase zero the slots one and three are on the G-branch, and the slots two and five are named as copies of the raw target. -/
theorem ordinaryAlternate_odd_hslot_of_facts (parents : TileParents) (w : Word)
    (hpk : (frameAt (w.map Digit.swapTwoThree)).Packet (standardField (w.map Digit.swapTwoThree)))
    (F : OddAlternateFacts parents w) :
    ∀ s ∈ afterSeventhAlternate .odd, (phase w = 1 → s ≠ 2) → (phase w = 0 → s ≠ 4) → ∃ g : ℤ,
      (placedBySlot (alternateJets w .odd) (standardSources parents .even) s).val.Agrees
        (alternateOddRawTarget w) g := by
  intro s hs h1s h0s
  simp only [afterSeventhAlternate, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases phase_eq_zero_or_one w with hph | hph
  · rcases hs with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨k, hk⟩ := F.raw2 hph
      exact ⟨k, hk⟩
    · obtain ⟨g, hg⟩ := F.gplane3 hph
      exact ⟨g - 1, HeightTile.Agrees.alternateOddRawTarget_of_gPlane hg (F.gWin3 hph)⟩
    · obtain ⟨g, hg⟩ := F.gplane1 hph
      exact ⟨g - 1, HeightTile.Agrees.alternateOddRawTarget_of_gPlane hg (F.gWin1 hph)⟩
    · exact absurd rfl (h0s hph)
    · obtain ⟨k, hk⟩ := F.raw5 hph
      exact ⟨k, hk⟩
  · rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl (h1s hph)
    · obtain ⟨g, hg⟩ := F.plane3 hph
      exact ⟨g, HeightTile.Agrees.alternateOddRawTarget_of_branch hg (F.planeWin3 hph)⟩
    · obtain ⟨g, hg⟩ := F.plane1 hph
      exact ⟨g, HeightTile.Agrees.alternateOddRawTarget_of_branch hg (F.planeWin1 hph)⟩
    · obtain ⟨g, hg⟩ := F.gplane4 hph
      exact ⟨g - 1, HeightTile.Agrees.alternateOddRawTarget_of_gPlane hg (F.gWin4 hph)⟩
    · obtain ⟨g, hg⟩ := F.coincident5 hph
      exact HeightTile.Agrees.alternateOddRawTarget_of_coincident hph hpk hg (F.coWin5' hph) (F.coBr5 hph)

/-- **The copy list of the odd ordinary alternate, down to the named sheet facts.** The identity of `ordinaryAlternate_odd_identifies_copies`
with its shear hypotheses discharged from the window facts (the first copy and the standard copies four and five, by the phase-one
and phase-zero shears), and its slot hypothesis discharged by `ordinaryAlternate_odd_hslot_of_facts`. -/
theorem ordinaryAlternate_odd_identifies_copies_of_facts (parents : TileParents) (beforePush : Word) (digit : Digit)
    (hnb : ¬ FLatticePaper.Tiles.Standard.IsBase (beforePush ++ [digit]))
    (context : String)
    (hpk : (frameAt ((beforePush ++ [digit]).map Digit.swapTwoThree)).Packet
      (standardField ((beforePush ++ [digit]).map Digit.swapTwoThree)))
    (F : OddAlternateFacts parents (beforePush ++ [digit]))
    {g0 : ℤ} (hdonor : parents.alternateEven.val.Agrees (alternateTarget beforePush) g0)
    (hmid : ¬ FLatticePaper.Tiles.Standard.IsBase (beforePush ++ [digit]) → ∃ k : ℤ,
      ∀ s ∈ (alternateOddSeventhCopy parents beforePush digit).val.sites,
        alternateOddRawTarget (beforePush ++ [digit]) s =
          alternateTarget beforePush
              (s - ((seventhAlternateJet beforePush digit .odd).1 +
                alternateRestoration (beforePush ++ [digit]) .even)) +
            ((seventhAlternateJet beforePush digit .odd).2.1 * s.1 +
              (seventhAlternateJet beforePush digit .odd).2.2 * s.2) + k)
    (hcon : HeightTile.OrderedContacts (ordinaryAlternateSchedule parents beforePush digit .odd).first.val.sites
      (ordinaryAlternateSchedule parents beforePush digit .odd).copies) :
    ∃ result, (ordinaryAlternateSchedule parents beforePush digit .odd).eval .tile context = .ok result ∧
      ∃ g : ℤ, result.val.Agrees
        (fun site => alternateOddRawTarget (beforePush ++ [digit]) (site +
          ((ordinaryAlternateSchedule parents beforePush digit .odd).raw hcon).val.boxOrigin
            ((ordinaryAlternateSchedule parents beforePush digit .odd).raw hcon).property)) g := by
  have hshear0 : ∃ k : ℤ, ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 0).val.sites,
      alternateOddRawTarget (beforePush ++ [digit]) s =
        planeTarget (beforePush ++ [digit]) .odd (s - oddStdChart (beforePush ++ [digit])) + k := by
    rcases phase_eq_zero_or_one (beforePush ++ [digit]) with hph | hph
    · refine ⟨0, fun s hs => ?_⟩
      have h := F.firstWin0 hph s hs
      rw [alternateOddRawTarget_eq_planeTarget_phase_zero _ hph s h.1 (by linarith [h.2]),
        oddStdChart_phase_zero _ hph, sub_zero, min_eq_left (by linarith [h.2]), add_zero]
    · obtain ⟨c, hc⟩ := alternateOddRawTarget_eq_planeTarget_chart_min _ hph hpk
      refine ⟨1 + c, fun s hs => ?_⟩
      have h := F.firstWin1 hph s hs
      rw [hc s (by linarith [h.1]) h.2, min_eq_right h.1]
      ring
  have hco1 : phase (beforePush ++ [digit]) = 1 →
      (∃ g : ℤ, (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 4).val.Agrees
        (planeTarget (beforePush ++ [digit]) .odd) g) ∧
      (∃ k : ℤ, ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 4).val.sites,
        alternateOddRawTarget (beforePush ++ [digit]) s = planeTarget (beforePush ++ [digit]) .odd s + k) := by
    intro hph
    refine ⟨F.coStd4 hph, ?_⟩
    obtain ⟨c, hc⟩ := alternateOddRawTarget_eq_planeTarget_chart_min _ hph hpk
    refine ⟨1 + c, fun s hs => ?_⟩
    have hw := F.coWin4 hph s hs
    have hb := F.coBr4 hph s hs
    rw [hc s hw.1 hw.2, hb]
    ring
  have hco0 : phase (beforePush ++ [digit]) = 0 →
      (∃ g : ℤ, (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 5).val.Agrees
        (planeTarget (beforePush ++ [digit]) .odd) g) ∧
      (∃ k : ℤ, ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 5).val.sites,
        alternateOddRawTarget (beforePush ++ [digit]) s = planeTarget (beforePush ++ [digit]) .odd s + k) := by
    intro hph
    refine ⟨F.coStd5 hph, 0, fun s hs => ?_⟩
    have h := F.coWin5 hph s hs
    rw [alternateOddRawTarget_eq_planeTarget_phase_zero _ hph s h.1 (by linarith [h.2]),
      min_eq_left (by linarith [h.2]), add_zero]
  exact ordinaryAlternate_odd_identifies_copies parents beforePush digit hnb context F.firstStd hshear0 hco1 hco0
    hdonor hmid (ordinaryAlternate_odd_hslot_of_facts parents (beforePush ++ [digit]) hpk F) hcon

end FLatticePaper.Construction
