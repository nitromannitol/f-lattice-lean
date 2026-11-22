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

end FLatticePaper.Construction
