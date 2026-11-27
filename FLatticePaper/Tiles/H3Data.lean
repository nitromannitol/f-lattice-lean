import FLatticePaper.Tiles.CellExtremes
import FLatticePaper.Tiles.RegisterTiles
import FLatticePaper.Tiles.SubOddCopy
import FLatticePaper.Tiles.SubEvenCopy
import FLatticePaper.Tiles.SiteHullOdd

/-! The data of (H3) in item (d) of `lemma:standard_tile_properties`: the parents of a non-base word and the bounds of the
functionals on the standard tiles.

* The registers of a word `w` hold the tiles of its source words (`RegisterTiles.tOdd_eq_oddTile`), whose current fractions are
  the parents of `w` (`src_odd_frac`, `src_even_frac`). For a non-base word both parents lie strictly inside `(0,1)`
  (`odd_parent_interior`, `even_parent_interior`).
* The parents `p₁ = n₁/d₁`, `q₁ = n₂/d₂` have `n₁ d₂ - n₂ d₁ = 1` when the phase is `1` and `-1` otherwise (`eps_det`), and
  either both satisfy `2n ≤ d` or both satisfy `d ≤ 2n` (`half_dichotomy`), and either both satisfy `d ≤ 3n` or both `3n ≤ d`
  (`third_dichotomy`). The first two are steps 3.1 and 3.3 of the proof of (H3); the third is the same statement for the rotated
  quadruple, used for the same-sign pairs.
* Property (ii) of the proof of (H3) (`Λ_r(z) = d y - n x ≥ -max(d, 2n)`) holds on the whole standard tile, read off the closed
  form of the tile (`SubOddCopy.mem_oddTile_iff`, `SubEvenCopy.mem_evenTile_iff`): `lam_bound_odd`, `lam_bound_even`. The text
  proves (ii) on the bottom walk by induction along the recursion; here it is a direct consequence of the closed form. The slope
  bound of the closed form (`sig_bound_odd`, `sig_bound_even`) is the corresponding bound for the vertical direction. -/

namespace FLatticePaper.Tiles.H3Data

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.SiteInduction
  FLatticePaper.Tiles.RecursionIdentity

/-! ### Non-base words and their registers -/

theorem nonbase_one_two {w : Word} (hw : ¬ IsBase w) : ∃ y ∈ w, y = Digit.one ∨ y = Digit.two := by
  by_contra h
  apply hw
  refine Or.inr (Or.inl fun d hd => ?_)
  cases d with
  | one => exact absurd ⟨Digit.one, hd, Or.inl rfl⟩ h
  | two => exact absurd ⟨Digit.two, hd, Or.inr rfl⟩ h
  | three => rfl

theorem nonbase_one_three {w : Word} (hw : ¬ IsBase w) : ∃ y ∈ w, y = Digit.one ∨ y = Digit.three := by
  by_contra h
  apply hw
  refine Or.inr (Or.inr fun d hd => ?_)
  cases d with
  | one => exact absurd ⟨Digit.one, hd, Or.inl rfl⟩ h
  | three => exact absurd ⟨Digit.three, hd, Or.inr rfl⟩ h
  | two => rfl

theorem exists_prefix_of_snoc {u : Word} {x : Digit} {P : Digit → Prop} (h : ∃ y ∈ u ++ [x], P y) (hx : ¬ P x) :
    ∃ y ∈ u, P y := by
  obtain ⟨y, hy, hy'⟩ := h
  rcases List.mem_append.mp hy with hy | hy
  · exact ⟨y, hy, hy'⟩
  · simp at hy
    subst hy
    exact absurd hy' hx

/-- The source of the odd register carries the odd parent as its current odd fraction. -/
theorem src_odd_frac (w : Word) (h : ∃ y ∈ w, y = Digit.one ∨ y = Digit.two) :
    curO (srcOf w).1 = (parentsAt w).odd := by
  induction w using List.reverseRecOn with
  | nil => simp at h
  | append_singleton u x ih =>
    have hsrc : (srcOf (u ++ [x])).1 = if x = Digit.one ∨ x = Digit.two then u else (srcOf u).1 := by
      unfold srcOf
      rw [srcFrom_snoc]
      simp
    rw [hsrc, parentsAt_append_singleton]
    cases x with
    | one => simp [Parents.step]
    | two => simp [Parents.step]
    | three =>
      have h' := exists_prefix_of_snoc h (by decide)
      simp only [Parents.step]
      simpa using ih h'

/-- The source of the even register carries the even parent as its current even fraction. -/
theorem src_even_frac (w : Word) (h : ∃ y ∈ w, y = Digit.one ∨ y = Digit.three) :
    curE (srcOf w).2 = (parentsAt w).even := by
  induction w using List.reverseRecOn with
  | nil => simp at h
  | append_singleton u x ih =>
    have hsrc : (srcOf (u ++ [x])).2 = if x = Digit.one ∨ x = Digit.three then u else (srcOf u).2 := by
      unfold srcOf
      rw [srcFrom_snoc]
      simp
    rw [hsrc, parentsAt_append_singleton]
    cases x with
    | one => simp [Parents.step]
    | three => simp [Parents.step]
    | two =>
      have h' := exists_prefix_of_snoc h (by decide)
      simp only [Parents.step]
      simpa using ih h'

theorem odd_parent_interior (w : Word) (h : ∃ y ∈ w, y = Digit.one ∨ y = Digit.two) :
    (parentsAt w).odd.Interior := by
  rw [← src_odd_frac w h]
  exact (parentsAt_valid _).current_interior .odd

theorem even_parent_interior (w : Word) (h : ∃ y ∈ w, y = Digit.one ∨ y = Digit.three) :
    (parentsAt w).even.Interior := by
  rw [← src_even_frac w h]
  exact (parentsAt_valid _).current_interior .even

/-! ### The determinant and the two dichotomies -/

/-- `n₁ d₂ - n₂ d₁ = 1` for phase `1` and `-1` for phase `0` (step 3.1 of the proof of (H3)). -/
theorem eps_det (w : Word) :
    (parentsAt w).odd.num * (parentsAt w).even.den - (parentsAt w).even.num * (parentsAt w).odd.den =
      if phase w = 1 then 1 else -1 := by
  have h := Parents.det_walk root w
  have hroot : root.odd.det root.even = -1 := by decide
  rw [hroot] at h
  change (parentsAt w).odd.det (parentsAt w).even = _ at h
  unfold Fraction.det at h
  rw [h]
  unfold phase
  rcases Nat.even_or_odd (w.count Digit.one) with he | ho
  · rw [he.neg_one_pow, if_neg (by rw [Nat.even_iff.1 he]; decide)]
    ring
  · rw [ho.neg_one_pow, if_pos (Nat.odd_iff.1 ho)]
    ring

/-- Both parents at most `1/2`. -/
def HalfLow (P : Parents) : Prop := 2 * P.odd.num ≤ P.odd.den ∧ 2 * P.even.num ≤ P.even.den

/-- Both parents at least `1/2`. -/
def HalfHigh (P : Parents) : Prop := P.odd.den ≤ 2 * P.odd.num ∧ P.even.den ≤ 2 * P.even.num

/-- Both parents at least `1/3`. -/
def ThirdHigh (P : Parents) : Prop := P.odd.den ≤ 3 * P.odd.num ∧ P.even.den ≤ 3 * P.even.num

/-- Both parents at most `1/3`. -/
def ThirdLow (P : Parents) : Prop := 3 * P.odd.num ≤ P.odd.den ∧ 3 * P.even.num ≤ P.even.den

theorem halfLow_walk (v : Word) : ∀ P : Parents, HalfLow P → HalfLow (P.walk v) := by
  induction v with
  | nil => intro P h; exact h
  | cons d v ih =>
    intro P h
    rw [Parents.walk_cons]
    apply ih
    unfold HalfLow at *
    cases d <;> simp only [Parents.step, Parents.current, Parents.combine] <;> omega

theorem halfHigh_walk (v : Word) : ∀ P : Parents, HalfHigh P → HalfHigh (P.walk v) := by
  induction v with
  | nil => intro P h; exact h
  | cons d v ih =>
    intro P h
    rw [Parents.walk_cons]
    apply ih
    unfold HalfHigh at *
    cases d <;> simp only [Parents.step, Parents.current, Parents.combine] <;> omega

theorem thirdHigh_walk (v : Word) : ∀ P : Parents, ThirdHigh P → ThirdHigh (P.walk v) := by
  induction v with
  | nil => intro P h; exact h
  | cons d v ih =>
    intro P h
    rw [Parents.walk_cons]
    apply ih
    unfold ThirdHigh at *
    cases d <;> simp only [Parents.step, Parents.current, Parents.combine] <;> omega

theorem thirdLow_walk (v : Word) : ∀ P : Parents, ThirdLow P → ThirdLow (P.walk v) := by
  induction v with
  | nil => intro P h; exact h
  | cons d v ih =>
    intro P h
    rw [Parents.walk_cons]
    apply ih
    unfold ThirdLow at *
    cases d <;> simp only [Parents.step, Parents.current, Parents.combine] <;> omega

/-- Step 3.3 of the proof of (H3): the parents of a nonempty word are both at most `1/2` or both at least `1/2`. -/
theorem half_dichotomy (w : Word) (hw : w ≠ []) : HalfLow (parentsAt w) ∨ HalfHigh (parentsAt w) := by
  cases w with
  | nil => exact absurd rfl hw
  | cons x v =>
    change HalfLow (root.walk (x :: v)) ∨ HalfHigh (root.walk (x :: v))
    rw [Parents.walk_cons]
    cases x
    · exact Or.inl (halfLow_walk v _ (by norm_num [HalfLow, root, Parents.step, Parents.current, Parents.combine]))
    · exact Or.inr (halfHigh_walk v _ (by norm_num [HalfHigh, root, Parents.step, Parents.current, Parents.combine]))
    · exact Or.inl (halfLow_walk v _ (by norm_num [HalfLow, root, Parents.step, Parents.current, Parents.combine]))

/-- The same dichotomy at `1/3` (the dichotomy at `1/2` of the rotated quadruple). -/
theorem third_dichotomy (w : Word) (hw : w ≠ []) : ThirdHigh (parentsAt w) ∨ ThirdLow (parentsAt w) := by
  cases w with
  | nil => exact absurd rfl hw
  | cons x v =>
    change ThirdHigh (root.walk (x :: v)) ∨ ThirdLow (root.walk (x :: v))
    rw [Parents.walk_cons]
    cases x
    · exact Or.inl (thirdHigh_walk v _ (by norm_num [ThirdHigh, root, Parents.step, Parents.current, Parents.combine]))
    · exact Or.inl (thirdHigh_walk v _ (by norm_num [ThirdHigh, root, Parents.step, Parents.current, Parents.combine]))
    · exact Or.inr (thirdLow_walk v _ (by norm_num [ThirdLow, root, Parents.step, Parents.current, Parents.combine]))

/-! ### The bounds of the closed form -/

/-- Property (ii) of (H3) on the closed form `H_f`: `d y - n x ≥ -max(d, 2n)` at every point of `H_f`. -/
theorem lam_bound_InH (f : Fraction) (hn : 0 ≤ f.num) (z : GInt) (hz : InH f z) :
    -(max f.den (2 * f.num)) ≤ f.den * z.2 - f.num * z.1 := by
  obtain ⟨-, h2, -, -⟩ := hz
  unfold tCo aOf at h2
  generalize f.num * z.1 = A at h2 ⊢
  generalize f.den * z.2 = B at h2 ⊢
  split_ifs at h2 <;> omega

/-- The slope bound of the closed form `H_f`. -/
theorem sig_bound_InH (f : Fraction) (z : GInt) (hz : InH f z) :
    (f.den + f.num) * z.1 + (f.den - f.num) * z.2 ≤
      SiteInduction.muOf f * tOf f + 2 * f.num - min 0 (min (f.den - f.num) (3 * f.num - f.den)) := by
  obtain ⟨-, -, -, h4⟩ := hz
  unfold sCo lOf at h4
  have m1 := min_le_left (0 : ℤ) (min (f.den - f.num) (3 * f.num - f.den))
  have m2 := min_le_right (0 : ℤ) (min (f.den - f.num) (3 * f.num - f.den))
  split_ifs at h4 <;> linarith

theorem muOf_of_odd (f : Fraction) (h : (f.num + f.den) % 2 = 1) : SiteInduction.muOf f = 2 := by
  unfold SiteInduction.muOf
  rw [if_pos h]

theorem muOf_of_even (f : Fraction) (h : (f.num + f.den) % 2 = 0) : SiteInduction.muOf f = 1 := by
  unfold SiteInduction.muOf
  rw [if_neg (by omega)]

/-- **Property (ii) of (H3) on the whole odd tile**: `d y - n x ≥ -max(d, 2n)` for the current odd fraction `n/d`. -/
theorem lam_bound_odd (u : Word) (z : GInt) (hz : z ∈ oddTile u) :
    -(max (curO u).den (2 * (curO u).num)) ≤ (curO u).den * z.2 - (curO u).num * z.1 :=
  lam_bound_InH (curO u) (le_of_lt (FLatticePaper.Tiles.SiteHullOdd.curO_pos_lt u).1) z
    ((FLatticePaper.Tiles.SubOddCopy.mem_oddTile_iff u z).1 hz)

/-- **Property (ii) of (H3) on the whole even tile.** -/
theorem lam_bound_even (u : Word) (z : GInt) (hz : z ∈ evenTile u) :
    -(max (curE u).den (2 * (curE u).num)) ≤ (curE u).den * z.2 - (curE u).num * z.1 :=
  lam_bound_InH (curE u) (le_of_lt ((parentsAt_valid u).current_interior .even).1) z
    ((FLatticePaper.Tiles.SubEvenCopy.mem_evenTile_iff u z).1 hz)

/-- The slope bound of the closed form on the odd tile. -/
theorem sig_bound_odd (u : Word) (z : GInt) (hz : z ∈ oddTile u) :
    ((curO u).den + (curO u).num) * z.1 + ((curO u).den - (curO u).num) * z.2 ≤
      2 * tOf (curO u) + 2 * (curO u).num -
        min 0 (min ((curO u).den - (curO u).num) (3 * (curO u).num - (curO u).den)) := by
  have h := sig_bound_InH (curO u) z ((FLatticePaper.Tiles.SubOddCopy.mem_oddTile_iff u z).1 hz)
  rwa [muOf_of_odd (curO u) (FLatticePaper.Tiles.SiteHullOdd.curO_odd u)] at h

/-- The slope bound of the closed form on the even tile. -/
theorem sig_bound_even (u : Word) (z : GInt) (hz : z ∈ evenTile u) :
    ((curE u).den + (curE u).num) * z.1 + ((curE u).den - (curE u).num) * z.2 ≤
      tOf (curE u) + 2 * (curE u).num -
        min 0 (min ((curE u).den - (curE u).num) (3 * (curE u).num - (curE u).den)) := by
  have h := sig_bound_InH (curE u) z ((FLatticePaper.Tiles.SubEvenCopy.mem_evenTile_iff u z).1 hz)
  rwa [muOf_of_even (curE u) (parentsAt_valid u).current_even_parity, one_mul] at h

/-! ### The sums of the boundary words -/

theorem sum_oddBottom_eq (u : Word) :
    F2Word.sum (oddBottom u) = (2 * (curO u).den, 2 * (curO u).num - 1) := by
  have h := FLatticePaper.Tiles.StandardBoundary.sum_oddBottom u
  unfold almostV₁ at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  rw [show fracOdd u = curO u from rfl] at h1 h2
  simp only [Prod.fst_add, Prod.snd_add, gI, texV1Odd] at h1 h2
  ext <;> simp only <;> omega

theorem sum_oddRight_eq (u : Word) :
    F2Word.sum (oddRight u) = ((curO u).num - (curO u).den + 1, (curO u).num + (curO u).den) := by
  have h := FLatticePaper.Tiles.StandardBoundary.sum_oddRight u
  unfold almostV₂ at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  rw [show fracOdd u = curO u from rfl] at h1 h2
  simp only [Prod.fst_sub, Prod.snd_sub, gOne, texV2] at h1 h2
  ext <;> simp only <;> omega

theorem sum_evenBottom_eq (u : Word) :
    F2Word.sum (evenBottom u) = ((curE u).den, (curE u).num - 1) := by
  have h := FLatticePaper.Tiles.StandardBoundary.sum_evenBottom u
  unfold almostV₁ at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  rw [show fracEven u = curE u from rfl] at h1 h2
  simp only [Prod.fst_add, Prod.snd_add, gI, texV1Even] at h1 h2
  ext <;> simp only <;> omega

theorem sum_evenRight_eq (u : Word) :
    F2Word.sum (evenRight u) = ((curE u).num - (curE u).den + 1, (curE u).num + (curE u).den) := by
  have h := FLatticePaper.Tiles.StandardBoundary.sum_evenRight u
  unfold almostV₂ at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  rw [show fracEven u = curE u from rfl] at h1 h2
  simp only [Prod.fst_sub, Prod.snd_sub, gOne, texV2] at h1 h2
  ext <;> simp only <;> omega

end FLatticePaper.Tiles.H3Data
