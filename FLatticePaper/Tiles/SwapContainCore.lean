import FLatticePaper.Tiles.SwapDisjoint
import FLatticePaper.Tiles.ClosedPathExcluded

/-! # The overlap of a meeting swapped pair: the separation of the other copies (tools)

At a word `w = u d` whose swapped pair of copies of a register tile meets, the overlap lies in one copy `G` of a grandparent tile
of the register's decomposition (text, lines 4545-4561). Here the overlap is reduced to the pairs of copies `A`, `B` of the two
frames other than `G`, which are separated by the strip functionals at the mediant of the parents of `u`
(`SameParentCopies`). This file has the shared intervals of both parent tiles (`stripPQ`), the separation of two copies of
different tiles, and the vectors of the parents of `u d` in terms of those of `u`. -/

namespace FLatticePaper.Tiles.SwapContainCore

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.H3Bounds FLatticePaper.Tiles.H3Pairs
  FLatticePaper.Tiles.SameParentCopies

/-! ### The vectors of the children -/

theorem tv1o_cur (P : Parents) : texV1Odd (P.current .odd) = texV1Odd P.odd + texV1Even P.even + texV1Even P.even := by
  ext <;> simp [texV1Odd, texV1Even, Parents.current, Parents.combine] <;> ring

theorem tv2_curO (P : Parents) : texV2 (P.current .odd) = texV2 P.odd + texV2 P.even := by
  ext <;> simp [texV2, Parents.current, Parents.combine] <;> ring

theorem tv1e_cur (P : Parents) : texV1Even (P.current .even) = texV1Odd P.odd + texV1Even P.even := by
  ext <;> simp [texV1Odd, texV1Even, Parents.current, Parents.combine]

theorem tv2_curE (P : Parents) : texV2 (P.current .even) = texV2 P.odd + texV2 P.odd + texV2 P.even := by
  ext <;> simp [texV2, Parents.current, Parents.combine] <;> ring

/-! ### The intervals of both parent tiles, with one choice of the cases -/

theorem stripPQ (w : Word) (hw : ¬ IsBase w) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt w).odd)
    (hU2 : curE U2 = (parentsAt w).even) :
    ∃ A A' : Bool,
      ((∀ z ∈ oddTile U1, mLP A (eW w) (nM w) (dM w) ≤ lam (nM w) (dM w) z) ∧
        (∀ z ∈ oddTile U1, lam (nM w) (dM w) z ≤
          lam (nM w) (dM w) (texV1Odd (parentsAt w).odd - gI + (texV2 (parentsAt w).odd + gOne)) -
            mLP A (eW w) (nM w) (dM w)) ∧
        (∀ z ∈ oddTile U1, sig (nM w) (dM w) (texV2 (parentsAt w).odd + gOne) - mSP A' (eW w) (nM w) (dM w) ≤
          sig (nM w) (dM w) z) ∧
        (∀ z ∈ oddTile U1, sig (nM w) (dM w) z ≤
          sig (nM w) (dM w) (texV1Odd (parentsAt w).odd - gI) + mSP A' (eW w) (nM w) (dM w))) ∧
      ((∀ z ∈ evenTile U2, mLQ A (eW w) 1 (nM w) (dM w) ≤ lam (nM w) (dM w) z) ∧
        (∀ z ∈ evenTile U2, lam (nM w) (dM w) z ≤
          lam (nM w) (dM w) (texV1Even (parentsAt w).even - gI + (texV2 (parentsAt w).even + gOne)) -
            mLQ A (eW w) 1 (nM w) (dM w)) ∧
        (∀ z ∈ evenTile U2, sig (nM w) (dM w) (texV2 (parentsAt w).even + gOne) - mSQ A' (eW w) 1 (nM w) (dM w) ≤
          sig (nM w) (dM w) z) ∧
        (∀ z ∈ evenTile U2, sig (nM w) (dM w) z ≤
          sig (nM w) (dM w) (texV1Even (parentsAt w).even - gI) + mSQ A' (eW w) 1 (nM w) (dM w))) := by
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior w (H3Data.nonbase_one_two hw)
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior w (H3Data.nonbase_one_three hw)
  have hne : w ≠ [] := fun h => hw (Or.inl h)
  have hn0 : nM w = 1 * (parentsAt w).odd.num + (parentsAt w).even.num := by unfold nM; ring
  have hd0 : dM w = 1 * (parentsAt w).odd.den + (parentsAt w).even.den := by unfold dM; ring
  have bP := fun (A A' : Bool) hA hB hA' hB' => odd_bounds U1 _ _ hU1 1 (eW w) _ _ A A' hn0 hd0 le_rfl (by omega) hd1
    (by omega) hd2 (H3Data.eps_det w) (eW_cases w) hA hB hA' hB'
  have bQ := fun (A A' : Bool) hA hB hA' hB' => even_bounds U2 _ _ hU2 1 (eW w) _ _ A A' hn0 hd0 le_rfl (by omega) hd1
    (by omega) hd2 (H3Data.eps_det w) (eW_cases w) hA hB hA' hB'
  rcases H3Data.half_dichotomy w hne with hh | hh <;> rcases H3Data.third_dichotomy w hne with ht | ht
  · exact ⟨true, true, bP true true (fun _ => hh.1) (fun h => absurd h (by decide)) (fun _ => ht.1)
      (fun h => absurd h (by decide)), bQ true true (fun _ => hh.2) (fun h => absurd h (by decide)) (fun _ => ht.2)
      (fun h => absurd h (by decide))⟩
  · exact ⟨true, false, bP true false (fun _ => hh.1) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun _ => ht.1), bQ true false (fun _ => hh.2) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun _ => ht.2)⟩
  · exact ⟨false, true, bP false true (fun h => absurd h (by decide)) (fun _ => hh.1) (fun _ => ht.1)
      (fun h => absurd h (by decide)), bQ false true (fun h => absurd h (by decide)) (fun _ => hh.2) (fun _ => ht.2)
      (fun h => absurd h (by decide))⟩
  · exact ⟨false, false, bP false false (fun h => absurd h (by decide)) (fun _ => hh.1) (fun h => absurd h (by decide))
      (fun _ => ht.1), bQ false false (fun h => absurd h (by decide)) (fun _ => hh.2) (fun h => absurd h (by decide))
      (fun _ => ht.2)⟩

/-! ### Separation of copies of the two parent tiles

`tile a` and `tile b` stand for `oddTile U1` (`P`) or `evenTile U2` (`Q`); the copy at `a` is on the side of the smaller values. -/

/-- The bounds of a tile kind in the strips: `true` is `P`, `false` is `Q`. -/
def loL (w : Word) (k A : Bool) : ℤ := if k then mLP A (eW w) (nM w) (dM w) else mLQ A (eW w) 1 (nM w) (dM w)

def hiL (w : Word) (k A : Bool) : ℤ :=
  if k then lam (nM w) (dM w) (texV1Odd (parentsAt w).odd - gI + (texV2 (parentsAt w).odd + gOne)) - mLP A (eW w) (nM w) (dM w)
  else lam (nM w) (dM w) (texV1Even (parentsAt w).even - gI + (texV2 (parentsAt w).even + gOne)) -
    mLQ A (eW w) 1 (nM w) (dM w)

def loS (w : Word) (k A' : Bool) : ℤ :=
  if k then sig (nM w) (dM w) (texV2 (parentsAt w).odd + gOne) - mSP A' (eW w) (nM w) (dM w)
  else sig (nM w) (dM w) (texV2 (parentsAt w).even + gOne) - mSQ A' (eW w) 1 (nM w) (dM w)

def hiS (w : Word) (k A' : Bool) : ℤ :=
  if k then sig (nM w) (dM w) (texV1Odd (parentsAt w).odd - gI) + mSP A' (eW w) (nM w) (dM w)
  else sig (nM w) (dM w) (texV1Even (parentsAt w).even - gI) + mSQ A' (eW w) 1 (nM w) (dM w)

/-- The tile of a kind. -/
def tileK (U1 U2 : Word) (k : Bool) : Finset Site := if k then oddTile U1 else evenTile U2

theorem bounds_K (w : Word) (hw : ¬ IsBase w) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt w).odd)
    (hU2 : curE U2 = (parentsAt w).even) :
    ∃ A A' : Bool, ∀ k : Bool, ∀ z ∈ tileK U1 U2 k, loL w k A ≤ lam (nM w) (dM w) z ∧ lam (nM w) (dM w) z ≤ hiL w k A ∧
      loS w k A' ≤ sig (nM w) (dM w) z ∧ sig (nM w) (dM w) z ≤ hiS w k A' := by
  obtain ⟨A, A', ⟨p1, p2, p3, p4⟩, ⟨q1, q2, q3, q4⟩⟩ := stripPQ w hw U1 U2 hU1 hU2
  refine ⟨A, A', fun k z hz => ?_⟩
  cases k
  · simp only [tileK, loL, hiL, loS, hiS, Bool.false_eq_true, if_false] at hz ⊢
    exact ⟨q1 z hz, q2 z hz, q3 z hz, q4 z hz⟩
  · simp only [tileK, loL, hiL, loS, hiS, if_true] at hz ⊢
    exact ⟨p1 z hz, p2 z hz, p3 z hz, p4 z hz⟩

/-- **Separation by `Λ₀`** of a copy of the tile of kind `ka` at `a` and one of kind `kb` at `b`. -/
theorem sep_lam (w : Word) (hw : ¬ IsBase w) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt w).odd)
    (hU2 : curE U2 = (parentsAt w).even) (ka kb : Bool) {a b : Site}
    (h : ∀ A : Bool, hiL w ka A - loL w kb A < lam (nM w) (dM w) b - lam (nM w) (dM w) a) {z : Site}
    (ha : z - a ∈ tileK U1 U2 ka) (hb : z - b ∈ tileK U1 U2 kb) : False := by
  obtain ⟨A, A', hB⟩ := bounds_K w hw U1 U2 hU1 hU2
  obtain ⟨-, h1, -, -⟩ := hB ka _ ha
  obtain ⟨h2, -, -, -⟩ := hB kb _ hb
  rw [lam_sub] at h1 h2
  linarith [h A]

/-- **Separation by `S₀`** of a copy of the tile of kind `ka` at `a` and one of kind `kb` at `b`. -/
theorem sep_sig (w : Word) (hw : ¬ IsBase w) (U1 U2 : Word) (hU1 : curO U1 = (parentsAt w).odd)
    (hU2 : curE U2 = (parentsAt w).even) (ka kb : Bool) {a b : Site}
    (h : ∀ A' : Bool, hiS w ka A' - loS w kb A' < sig (nM w) (dM w) b - sig (nM w) (dM w) a) {z : Site}
    (ha : z - a ∈ tileK U1 U2 ka) (hb : z - b ∈ tileK U1 U2 kb) : False := by
  obtain ⟨A, A', hB⟩ := bounds_K w hw U1 U2 hU1 hU2
  obtain ⟨-, -, -, h1⟩ := hB ka _ ha
  obtain ⟨-, -, h2, -⟩ := hB kb _ hb
  rw [sig_sub] at h1 h2
  linarith [h A']

/-! ### Two more bounds from the parents of the shorter word -/

/-- After a `3`: the even parent of the shorter word has a positive numerator. -/
theorem rel_three_qnum (w : Word) (hw : ¬ IsBase w) (h : w.getLast? = some Digit.three) :
    2 * dM w ≤ lam (nM w) (dM w) (texV2 (parentsAt w).even) - 2 * lam (nM w) (dM w) (texV2 (parentsAt w).odd) := by
  have hs := parents_last w _ h
  obtain ⟨hc1, hc2⟩ := mediant_bounds w hw
  have hn := SameParentAlt.even_num_pos w.dropLast
  obtain ⟨hd, -, -⟩ := (parentsAt_valid w.dropLast).even_bounds
  have ho : (parentsAt w).odd = (parentsAt w.dropLast).odd := by
    rw [hs]; simp [Parents.step]
  have he : (parentsAt w).even = ⟨2 * (parentsAt w.dropLast).odd.num + (parentsAt w.dropLast).even.num,
      2 * (parentsAt w.dropLast).odd.den + (parentsAt w.dropLast).even.den⟩ := by
    rw [hs]; simp [Parents.step, Parents.current, Parents.combine]
  rw [lam_texV2, lam_texV2, ho, he]
  have h1 := mul_le_mul_of_nonneg_left hn (show (0 : ℤ) ≤ dM w - nM w by omega)
  have h2 := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ (parentsAt w.dropLast).even.den by omega)
    (show (0 : ℤ) ≤ dM w + nM w by omega)
  nlinarith [h1, h2]

/-- After a `2`, when the shorter word has a `1` or a `2`: its odd parent is interior. -/
theorem rel_two_pint (w : Word) (hw : ¬ IsBase w) (h : w.getLast? = some Digit.two)
    (hp : ∃ y ∈ w.dropLast, y = Digit.one ∨ y = Digit.two) :
    3 * dM w + nM w ≤ lam (nM w) (dM w) (texV2 (parentsAt w).odd) - lam (nM w) (dM w) (texV2 (parentsAt w).even) := by
  have hs := parents_last w _ h
  obtain ⟨hc1, hc2⟩ := mediant_bounds w hw
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior w.dropLast hp
  have ho : (parentsAt w).odd = ⟨(parentsAt w.dropLast).odd.num + (parentsAt w.dropLast).even.num,
      (parentsAt w.dropLast).odd.den + (parentsAt w.dropLast).even.den⟩ := by
    rw [hs]; simp [Parents.step, Parents.current, Parents.combine]
  have he : (parentsAt w).even = (parentsAt w.dropLast).even := by
    rw [hs]; simp [Parents.step]
  rw [lam_texV2, lam_texV2, ho, he]
  have h1 := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ (parentsAt w.dropLast).odd.num by omega)
    (show (0 : ℤ) ≤ dM w - nM w by omega)
  have h2 := mul_le_mul_of_nonneg_left (show (2 : ℤ) ≤ (parentsAt w.dropLast).odd.den by omega)
    (show (0 : ℤ) ≤ dM w + nM w by omega)
  nlinarith [h1, h2]

/-- After a `2` at a non-base word: the shorter word has a `1` or a `3`, so its even parent is interior. -/
theorem rel_two_qint (w : Word) (hw : ¬ IsBase w) (h : w.getLast? = some Digit.two) :
    3 * dM w + nM w ≤ lam (nM w) (dM w) (texV2 (parentsAt w).even) := by
  have hs := parents_last w _ h
  obtain ⟨hc1, hc2⟩ := mediant_bounds w hw
  have hq : ∃ y ∈ w.dropLast, y = Digit.one ∨ y = Digit.three := by
    by_contra hc
    simp only [not_exists, not_and, not_or] at hc
    refine hw (Or.inr (Or.inr fun d hd => ?_))
    rw [SameParentAlt.eq_snoc_of_getLast w _ h] at hd
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · cases d with
      | one => exact absurd rfl (hc _ hd).1
      | two => rfl
      | three => exact absurd rfl (hc _ hd).2
    · rfl
  obtain ⟨hn1, hd1⟩ := H3Data.even_parent_interior w.dropLast hq
  have he : (parentsAt w).even = (parentsAt w.dropLast).even := by
    rw [hs]; simp [Parents.step]
  rw [lam_texV2, he]
  have h1 := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ (parentsAt w.dropLast).even.num by omega)
    (show (0 : ℤ) ≤ dM w - nM w by omega)
  have h2 := mul_le_mul_of_nonneg_left (show (2 : ℤ) ≤ (parentsAt w.dropLast).even.den by omega)
    (show (0 : ℤ) ≤ dM w + nM w by omega)
  nlinarith [h1, h2]

/-- After a `3` at a non-base word: the shorter word has a `1` or a `2`, so its odd parent is interior. -/
theorem rel_three_pint (w : Word) (hw : ¬ IsBase w) (h : w.getLast? = some Digit.three) :
    3 * dM w + nM w ≤ lam (nM w) (dM w) (texV2 (parentsAt w).odd) := by
  have hs := parents_last w _ h
  obtain ⟨hc1, hc2⟩ := mediant_bounds w hw
  have hp : ∃ y ∈ w.dropLast, y = Digit.one ∨ y = Digit.two := by
    by_contra hc
    simp only [not_exists, not_and, not_or] at hc
    refine hw (Or.inr (Or.inl fun d hd => ?_))
    rw [SameParentAlt.eq_snoc_of_getLast w _ h] at hd
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · cases d with
      | one => exact absurd rfl (hc _ hd).1
      | two => exact absurd rfl (hc _ hd).2
      | three => rfl
    · rfl
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior w.dropLast hp
  have ho : (parentsAt w).odd = (parentsAt w.dropLast).odd := by
    rw [hs]; simp [Parents.step]
  rw [lam_texV2, ho]
  have h1 := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ (parentsAt w.dropLast).odd.num by omega)
    (show (0 : ℤ) ≤ dM w - nM w by omega)
  have h2 := mul_le_mul_of_nonneg_left (show (2 : ℤ) ≤ (parentsAt w.dropLast).odd.den by omega)
    (show (0 : ℤ) ≤ dM w + nM w by omega)
  nlinarith [h1, h2]

/-! ### Separation by the boxes of the parent tiles -/

/-- The box of a parent tile: `n - d + 1 ≤ x ≤ 2d`, `0 ≤ y ≤ 3n + d - 1` for the odd one, `n - d + 1 ≤ x ≤ d`,
`0 ≤ y ≤ 2n + d - 1` for the even one. -/
def loX (U1 U2 : Word) (k : Bool) : ℤ :=
  if k then (StandardClause.fracOdd U1).num - (StandardClause.fracOdd U1).den + 1
  else (StandardClause.fracEven U2).num - (StandardClause.fracEven U2).den + 1

def hiX (U1 U2 : Word) (k : Bool) : ℤ :=
  if k then 2 * (StandardClause.fracOdd U1).den else (StandardClause.fracEven U2).den

def hiY (U1 U2 : Word) (k : Bool) : ℤ :=
  if k then 3 * (StandardClause.fracOdd U1).num + (StandardClause.fracOdd U1).den - 1
  else 2 * (StandardClause.fracEven U2).num + (StandardClause.fracEven U2).den - 1

theorem box_K (U1 U2 : Word) (k : Bool) {a z : Site} (h : z - a ∈ tileK U1 U2 k) :
    loX U1 U2 k ≤ z.1 - a.1 ∧ z.1 - a.1 ≤ hiX U1 U2 k ∧ 0 ≤ z.2 - a.2 ∧ z.2 - a.2 ≤ hiY U1 U2 k := by
  cases k
  · simp only [tileK, Bool.false_eq_true, if_false] at h
    simpa [loX, hiX, hiY] using ClosedPathExcluded.box_shift_even U2 a z ((CellRegisters.mem_shiftS_iff _ a z).2 (Finset.mem_coe.2 h))
  · simp only [tileK, if_true] at h
    simpa [loX, hiX, hiY] using ClosedPathExcluded.box_shift_odd U1 a z ((CellRegisters.mem_shiftS_iff _ a z).2 (Finset.mem_coe.2 h))

theorem sep_x (U1 U2 : Word) (ka kb : Bool) {a b : Site} (hsep : hiX U1 U2 ka + a.1 < loX U1 U2 kb + b.1) {z : Site}
    (ha : z - a ∈ tileK U1 U2 ka) (hb : z - b ∈ tileK U1 U2 kb) : False := by
  obtain ⟨-, h1, -, -⟩ := box_K U1 U2 ka ha
  obtain ⟨h2, -, -, -⟩ := box_K U1 U2 kb hb
  linarith

theorem sep_y (U1 U2 : Word) (ka kb : Bool) {a b : Site} (hsep : hiY U1 U2 ka + a.2 < b.2) {z : Site}
    (ha : z - a ∈ tileK U1 U2 ka) (hb : z - b ∈ tileK U1 U2 kb) : False := by
  obtain ⟨-, -, -, h1⟩ := box_K U1 U2 ka ha
  obtain ⟨-, -, h2, -⟩ := box_K U1 U2 kb hb
  linarith

end FLatticePaper.Tiles.SwapContainCore
