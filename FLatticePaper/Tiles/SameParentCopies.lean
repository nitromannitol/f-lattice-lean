import FLatticePaper.Tiles.H3Pairs

/-! Copies of the same parent tile that are not a doubled pair, in the four decompositions of a non-base word (the standard
decompositions of both children and the decompositions of both alternate children into six standard copies), do not meet at
the corrected children: in the odd ones after a `3` and in the even ones after a `2`, for the copies that are not replaced by
L-corrections.

The argument is the separation of `H3Pairs`: on a parent tile the functionals `Λ₀ = d₀ y - n₀ x` and
`S₀ = (d₀ + n₀) x + (d₀ - n₀) y` at the mediant `n₀/d₀` of the two parents lie in the intervals of `H3Pairs.odd_bounds` and
`H3Pairs.even_bounds`, so two copies whose offsets differ by more than the length of the interval in one of the functionals are
disjoint. The difference of the offsets is linear in `Λ₀(v_{p,2})` and `Λ₀(v_{q,2})` once the determinant is used
(`vals`), and the last letter of the word bounds these two below in terms of the parents of the shorter word (`rel_one`,
`rel_two`, `rel_three`). -/

namespace FLatticePaper.Tiles.SameParentCopies

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.H3Bounds FLatticePaper.Tiles.H3Pairs

/-- The numerator `n₀` of the mediant of the parents of `w`. -/
abbrev nM (w : Word) : ℤ := (parentsAt w).odd.num + (parentsAt w).even.num

/-- The denominator `d₀` of the mediant of the parents of `w`. -/
abbrev dM (w : Word) : ℤ := (parentsAt w).odd.den + (parentsAt w).even.den

/-- The determinant of the parents of `w`. -/
abbrev eW (w : Word) : ℤ := if phase w = 1 then 1 else -1

/-! ### Separation of two copies of one tile -/

theorem copies_lam {T : Finset GInt} {n0 d0 lo hi : ℤ} (hlo : ∀ z ∈ T, lo ≤ lam n0 d0 z)
    (hhi : ∀ z ∈ T, lam n0 d0 z ≤ hi) {a b : GInt} (h : hi - lo < lam n0 d0 b - lam n0 d0 a) {z : GInt}
    (ha : z - a ∈ T) (hb : z - b ∈ T) : False := by
  have h1 := hlo _ hb
  have h2 := hhi _ ha
  rw [lam_sub] at h1 h2
  linarith

theorem copies_sig {T : Finset GInt} {n0 d0 lo hi : ℤ} (hlo : ∀ z ∈ T, lo ≤ sig n0 d0 z)
    (hhi : ∀ z ∈ T, sig n0 d0 z ≤ hi) {a b : GInt} (h : hi - lo < sig n0 d0 b - sig n0 d0 a) {z : GInt}
    (ha : z - a ∈ T) (hb : z - b ∈ T) : False := by
  have h1 := hlo _ hb
  have h2 := hhi _ ha
  rw [sig_sub] at h1 h2
  linarith

/-! ### The intervals on the parent tiles -/

theorem mediant_bounds (w : Word) (hw : ¬ IsBase w) : 2 ≤ nM w ∧ 2 ≤ dM w - nM w := by
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior w (H3Data.nonbase_one_two hw)
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior w (H3Data.nonbase_one_three hw)
  unfold nM dM
  omega

theorem eW_cases (w : Word) : eW w = 1 ∨ eW w = -1 := by
  unfold eW
  split_ifs <;> simp

/-- The intervals of `Λ₀` and `S₀` on the odd parent tile. -/
theorem stripP (w : Word) (hw : ¬ IsBase w) (U : Word) (hU : curO U = (parentsAt w).odd) :
    ∃ A A' : Bool,
      (∀ z ∈ oddTile U, mLP A (eW w) (nM w) (dM w) ≤ lam (nM w) (dM w) z) ∧
      (∀ z ∈ oddTile U, lam (nM w) (dM w) z ≤
        lam (nM w) (dM w) (texV1Odd (parentsAt w).odd - gI + (texV2 (parentsAt w).odd + gOne)) - mLP A (eW w) (nM w) (dM w)) ∧
      (∀ z ∈ oddTile U, sig (nM w) (dM w) (texV2 (parentsAt w).odd + gOne) - mSP A' (eW w) (nM w) (dM w) ≤ sig (nM w) (dM w) z) ∧
      (∀ z ∈ oddTile U, sig (nM w) (dM w) z ≤ sig (nM w) (dM w) (texV1Odd (parentsAt w).odd - gI) + mSP A' (eW w) (nM w) (dM w)) := by
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior w (H3Data.nonbase_one_two hw)
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior w (H3Data.nonbase_one_three hw)
  have hne : w ≠ [] := fun h => hw (Or.inl h)
  have hn0 : nM w = 1 * (parentsAt w).odd.num + (parentsAt w).even.num := by unfold nM; ring
  have hd0 : dM w = 1 * (parentsAt w).odd.den + (parentsAt w).even.den := by unfold dM; ring
  rcases H3Data.half_dichotomy w hne with hh | hh <;> rcases H3Data.third_dichotomy w hne with ht | ht
  · exact ⟨true, true, odd_bounds U _ _ hU 1 (eW w) _ _ true true hn0 hd0 le_rfl (by omega) hd1 (by omega) hd2
      (H3Data.eps_det w) (eW_cases w) (fun _ => hh.1) (fun h => absurd h (by decide)) (fun _ => ht.1)
      (fun h => absurd h (by decide))⟩
  · exact ⟨true, false, odd_bounds U _ _ hU 1 (eW w) _ _ true false hn0 hd0 le_rfl (by omega) hd1 (by omega) hd2
      (H3Data.eps_det w) (eW_cases w) (fun _ => hh.1) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun _ => ht.1)⟩
  · exact ⟨false, true, odd_bounds U _ _ hU 1 (eW w) _ _ false true hn0 hd0 le_rfl (by omega) hd1 (by omega) hd2
      (H3Data.eps_det w) (eW_cases w) (fun h => absurd h (by decide)) (fun _ => hh.1) (fun _ => ht.1)
      (fun h => absurd h (by decide))⟩
  · exact ⟨false, false, odd_bounds U _ _ hU 1 (eW w) _ _ false false hn0 hd0 le_rfl (by omega) hd1 (by omega) hd2
      (H3Data.eps_det w) (eW_cases w) (fun h => absurd h (by decide)) (fun _ => hh.1) (fun h => absurd h (by decide))
      (fun _ => ht.1)⟩

/-- The intervals of `Λ₀` and `S₀` on the even parent tile. -/
theorem stripQ (w : Word) (hw : ¬ IsBase w) (U : Word) (hU : curE U = (parentsAt w).even) :
    ∃ A A' : Bool,
      (∀ z ∈ evenTile U, mLQ A (eW w) 1 (nM w) (dM w) ≤ lam (nM w) (dM w) z) ∧
      (∀ z ∈ evenTile U, lam (nM w) (dM w) z ≤
        lam (nM w) (dM w) (texV1Even (parentsAt w).even - gI + (texV2 (parentsAt w).even + gOne)) -
          mLQ A (eW w) 1 (nM w) (dM w)) ∧
      (∀ z ∈ evenTile U, sig (nM w) (dM w) (texV2 (parentsAt w).even + gOne) - mSQ A' (eW w) 1 (nM w) (dM w) ≤
        sig (nM w) (dM w) z) ∧
      (∀ z ∈ evenTile U, sig (nM w) (dM w) z ≤
        sig (nM w) (dM w) (texV1Even (parentsAt w).even - gI) + mSQ A' (eW w) 1 (nM w) (dM w)) := by
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior w (H3Data.nonbase_one_two hw)
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior w (H3Data.nonbase_one_three hw)
  have hne : w ≠ [] := fun h => hw (Or.inl h)
  have hn0 : nM w = 1 * (parentsAt w).odd.num + (parentsAt w).even.num := by unfold nM; ring
  have hd0 : dM w = 1 * (parentsAt w).odd.den + (parentsAt w).even.den := by unfold dM; ring
  rcases H3Data.half_dichotomy w hne with hh | hh <;> rcases H3Data.third_dichotomy w hne with ht | ht
  · exact ⟨true, true, even_bounds U _ _ hU 1 (eW w) _ _ true true hn0 hd0 le_rfl (by omega) hd1 (by omega) hd2
      (H3Data.eps_det w) (eW_cases w) (fun _ => hh.2) (fun h => absurd h (by decide)) (fun _ => ht.2)
      (fun h => absurd h (by decide))⟩
  · exact ⟨true, false, even_bounds U _ _ hU 1 (eW w) _ _ true false hn0 hd0 le_rfl (by omega) hd1 (by omega) hd2
      (H3Data.eps_det w) (eW_cases w) (fun _ => hh.2) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun _ => ht.2)⟩
  · exact ⟨false, true, even_bounds U _ _ hU 1 (eW w) _ _ false true hn0 hd0 le_rfl (by omega) hd1 (by omega) hd2
      (H3Data.eps_det w) (eW_cases w) (fun h => absurd h (by decide)) (fun _ => hh.2) (fun _ => ht.2)
      (fun h => absurd h (by decide))⟩
  · exact ⟨false, false, even_bounds U _ _ hU 1 (eW w) _ _ false false hn0 hd0 le_rfl (by omega) hd1 (by omega) hd2
      (H3Data.eps_det w) (eW_cases w) (fun h => absurd h (by decide)) (fun _ => hh.2) (fun h => absurd h (by decide))
      (fun _ => ht.2)⟩

/-- Two copies of the odd parent tile are disjoint when their offsets differ in `Λ₀` by more than the interval. -/
theorem sepP_lam (w : Word) (hw : ¬ IsBase w) (U : Word) (hU : curO U = (parentsAt w).odd) {a b : GInt}
    (h : ∀ A : Bool, lam (nM w) (dM w) (texV1Odd (parentsAt w).odd - gI + (texV2 (parentsAt w).odd + gOne)) -
      2 * mLP A (eW w) (nM w) (dM w) < lam (nM w) (dM w) b - lam (nM w) (dM w) a) {z : GInt}
    (ha : z - a ∈ oddTile U) (hb : z - b ∈ oddTile U) : False := by
  obtain ⟨A, -, h1, h2, -, -⟩ := stripP w hw U hU
  exact copies_lam h1 h2 (by linarith [h A]) ha hb

/-- Two copies of the odd parent tile are disjoint when their offsets differ in `S₀` by more than the interval. -/
theorem sepP_sig (w : Word) (hw : ¬ IsBase w) (U : Word) (hU : curO U = (parentsAt w).odd) {a b : GInt}
    (h : ∀ A' : Bool, sig (nM w) (dM w) (texV1Odd (parentsAt w).odd - gI) - sig (nM w) (dM w) (texV2 (parentsAt w).odd + gOne) +
      2 * mSP A' (eW w) (nM w) (dM w) < sig (nM w) (dM w) b - sig (nM w) (dM w) a) {z : GInt}
    (ha : z - a ∈ oddTile U) (hb : z - b ∈ oddTile U) : False := by
  obtain ⟨-, A', -, -, h1, h2⟩ := stripP w hw U hU
  exact copies_sig h1 h2 (by linarith [h A']) ha hb

/-- Two copies of the even parent tile are disjoint when their offsets differ in `Λ₀` by more than the interval. -/
theorem sepQ_lam (w : Word) (hw : ¬ IsBase w) (U : Word) (hU : curE U = (parentsAt w).even) {a b : GInt}
    (h : ∀ A : Bool, lam (nM w) (dM w) (texV1Even (parentsAt w).even - gI + (texV2 (parentsAt w).even + gOne)) -
      2 * mLQ A (eW w) 1 (nM w) (dM w) < lam (nM w) (dM w) b - lam (nM w) (dM w) a) {z : GInt}
    (ha : z - a ∈ evenTile U) (hb : z - b ∈ evenTile U) : False := by
  obtain ⟨A, -, h1, h2, -, -⟩ := stripQ w hw U hU
  exact copies_lam h1 h2 (by linarith [h A]) ha hb

/-- Two copies of the even parent tile are disjoint when their offsets differ in `S₀` by more than the interval. -/
theorem sepQ_sig (w : Word) (hw : ¬ IsBase w) (U : Word) (hU : curE U = (parentsAt w).even) {a b : GInt}
    (h : ∀ A' : Bool, sig (nM w) (dM w) (texV1Even (parentsAt w).even - gI) -
      sig (nM w) (dM w) (texV2 (parentsAt w).even + gOne) + 2 * mSQ A' (eW w) 1 (nM w) (dM w) <
        sig (nM w) (dM w) b - sig (nM w) (dM w) a) {z : GInt}
    (ha : z - a ∈ evenTile U) (hb : z - b ∈ evenTile U) : False := by
  obtain ⟨-, A', -, -, h1, h2⟩ := stripQ w hw U hU
  exact copies_sig h1 h2 (by linarith [h A']) ha hb

/-! ### The values of the functionals on the parent vectors -/

theorem lam_texV2 (n0 d0 : ℤ) (f : Fraction) : lam n0 d0 (texV2 f) = (d0 - n0) * f.num + (d0 + n0) * f.den := by
  simp only [lam, texV2]
  ring

/-- `Λ₀` and `S₀` on the four vectors of the parents and on `1`, `i`: the determinant fixes all but `Λ₀(v_{p,2})` and
`Λ₀(v_{q,2})`, which are also `S₀(v_{p,1}) / 2` and `S₀(v_{q,1})`. -/
theorem vals (w : Word) :
    lam (nM w) (dM w) (texV1Odd (parentsAt w).odd) = 2 * eW w ∧ lam (nM w) (dM w) (texV1Even (parentsAt w).even) = -eW w ∧
      sig (nM w) (dM w) (texV2 (parentsAt w).odd) = 2 * eW w ∧ sig (nM w) (dM w) (texV2 (parentsAt w).even) = -2 * eW w ∧
      sig (nM w) (dM w) (texV1Odd (parentsAt w).odd) = 2 * lam (nM w) (dM w) (texV2 (parentsAt w).odd) ∧
      sig (nM w) (dM w) (texV1Even (parentsAt w).even) = lam (nM w) (dM w) (texV2 (parentsAt w).even) ∧
      lam (nM w) (dM w) gI = dM w ∧ lam (nM w) (dM w) gOne = -nM w ∧ sig (nM w) (dM w) gI = dM w - nM w ∧
      sig (nM w) (dM w) gOne = dM w + nM w := by
  have hdet := H3Data.eps_det w
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [lam, texV1Odd, nM, dM, eW]; linear_combination 2 * hdet
  · simp only [lam, texV1Even, nM, dM, eW]; linear_combination (-1 : ℤ) * hdet
  · simp only [sig, texV2, nM, dM, eW]; linear_combination 2 * hdet
  · simp only [sig, texV2, nM, dM, eW]; linear_combination (-2 : ℤ) * hdet
  · simp only [lam, sig, texV1Odd, texV2]; ring
  · simp only [lam, sig, texV1Even, texV2]; ring
  · simp [lam, gI]
  · simp [lam, gOne]
  · simp [sig, gI]
  · simp [sig, gOne]

/-! ### The last letter -/

theorem parents_last (w : Word) (d : Digit) (h : w.getLast? = some d) : parentsAt w = (parentsAt w.dropLast).step d := by
  obtain ⟨v, rfl⟩ : ∃ v, w = v ++ [d] := by
    induction w using List.reverseRecOn with
    | nil => simp at h
    | append_singleton v x _ =>
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] at h
      exact ⟨v, by rw [h]⟩
  simpa using parentsAt_append_singleton v d

/-- A fraction of the shorter word, in `Λ₀(v_2)`. -/
theorem prev_bound (w : Word) (hw : ¬ IsBase w) (f : Fraction) (hf : f.InUnitInterval) :
    dM w + nM w ≤ (dM w - nM w) * f.num + (dM w + nM w) * f.den := by
  obtain ⟨hc1, hc2⟩ := mediant_bounds w hw
  obtain ⟨hd, hn, -⟩ := hf
  have h1 := mul_nonneg (show (0 : ℤ) ≤ dM w - nM w by omega) hn
  have h2 := mul_nonneg (show (0 : ℤ) ≤ dM w + nM w by omega) (show (0 : ℤ) ≤ f.den - 1 by omega)
  nlinarith

/-- After a `1`: `q = p + p'` and `p = p' + q'`. -/
theorem rel_one (w : Word) (hw : ¬ IsBase w) (h : w.getLast? = some Digit.one) :
    dM w + nM w ≤ lam (nM w) (dM w) (texV2 (parentsAt w).even) - lam (nM w) (dM w) (texV2 (parentsAt w).odd) ∧
      dM w + nM w ≤ 2 * lam (nM w) (dM w) (texV2 (parentsAt w).odd) - lam (nM w) (dM w) (texV2 (parentsAt w).even) := by
  have hs := parents_last w _ h
  have h1 := prev_bound w hw _ (parentsAt_valid w.dropLast).odd_bounds
  have h2 := prev_bound w hw _ (parentsAt_valid w.dropLast).even_bounds
  have ho : (parentsAt w).odd = ⟨(parentsAt w.dropLast).odd.num + (parentsAt w.dropLast).even.num,
      (parentsAt w.dropLast).odd.den + (parentsAt w.dropLast).even.den⟩ := by
    rw [hs]; simp [Parents.step, Parents.current, Parents.combine]
  have he : (parentsAt w).even = ⟨2 * (parentsAt w.dropLast).odd.num + (parentsAt w.dropLast).even.num,
      2 * (parentsAt w.dropLast).odd.den + (parentsAt w.dropLast).even.den⟩ := by
    rw [hs]; simp [Parents.step, Parents.current, Parents.combine]
  rw [lam_texV2, lam_texV2, ho, he]
  constructor <;> nlinarith [h1, h2]

/-- After a `2`: `p = p' + q` and `q = q'`. -/
theorem rel_two (w : Word) (hw : ¬ IsBase w) (h : w.getLast? = some Digit.two) :
    dM w + nM w ≤ lam (nM w) (dM w) (texV2 (parentsAt w).even) ∧
      dM w + nM w ≤ lam (nM w) (dM w) (texV2 (parentsAt w).odd) - lam (nM w) (dM w) (texV2 (parentsAt w).even) := by
  have hs := parents_last w _ h
  have h1 := prev_bound w hw _ (parentsAt_valid w.dropLast).odd_bounds
  have h2 := prev_bound w hw _ (parentsAt_valid w.dropLast).even_bounds
  have ho : (parentsAt w).odd = ⟨(parentsAt w.dropLast).odd.num + (parentsAt w.dropLast).even.num,
      (parentsAt w.dropLast).odd.den + (parentsAt w.dropLast).even.den⟩ := by
    rw [hs]; simp [Parents.step, Parents.current, Parents.combine]
  have he : (parentsAt w).even = (parentsAt w.dropLast).even := by
    rw [hs]; simp [Parents.step]
  rw [lam_texV2, lam_texV2, ho, he]
  constructor <;> nlinarith [h1, h2]

/-- After a `3`: `p = p'` and `q = 2 p + q'`. -/
theorem rel_three (w : Word) (hw : ¬ IsBase w) (h : w.getLast? = some Digit.three) :
    dM w + nM w ≤ lam (nM w) (dM w) (texV2 (parentsAt w).odd) ∧
      dM w + nM w ≤ lam (nM w) (dM w) (texV2 (parentsAt w).even) - 2 * lam (nM w) (dM w) (texV2 (parentsAt w).odd) := by
  have hs := parents_last w _ h
  have h1 := prev_bound w hw _ (parentsAt_valid w.dropLast).odd_bounds
  have h2 := prev_bound w hw _ (parentsAt_valid w.dropLast).even_bounds
  have ho : (parentsAt w).odd = (parentsAt w.dropLast).odd := by
    rw [hs]; simp [Parents.step]
  have he : (parentsAt w).even = ⟨2 * (parentsAt w.dropLast).odd.num + (parentsAt w.dropLast).even.num,
      2 * (parentsAt w.dropLast).odd.den + (parentsAt w.dropLast).even.den⟩ := by
    rw [hs]; simp [Parents.step, Parents.current, Parents.combine]
  rw [lam_texV2, lam_texV2, ho, he]
  constructor <;> nlinarith [h1, h2]

/-! ### The pairs -/

theorem one_eq_neg_one_false : ((1 : ℤ) = -1) = False := by norm_num

theorem neg_one_eq_one_false : ((-1 : ℤ) = 1) = False := by norm_num

/-- Closes the separation inequality of a pair once the determinant is substituted: unfolds the bounds, expands the
functionals over the offsets and concludes by `linarith` from `vals`, the last letter and the mediant bounds. -/
macro "sep_close" : tactic => `(tactic| (simp only [mLP, mLQ, mSP, mSQ, lam_add, lam_sub, lam_zero, sig_add, sig_sub,
  sig_zero, Bool.false_eq_true, if_true, if_false, one_eq_neg_one_false, neg_one_eq_one_false]; linarith))

/-- Copies `0` and `1` of the standard odd child after a `3`, `W_1` odd. -/
theorem so01_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (0) ∈ oddTile U)
    (hb : z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even) ∈ oddTile U) : False := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close

/-- Copies `0` and `1` of the standard odd child after a `3`, `W_1` even. -/
theorem so01_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even) ∈ oddTile U)
    (hb : z - (texV2 (parentsAt w).even) ∈ oddTile U) : False := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close

/-- Copies `3` and `4` of the standard odd child after a `3`, `W_1` odd. -/
theorem so34_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (texV1Odd (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ evenTile U)
    (hb : z - (texV2 (parentsAt w).odd) ∈ evenTile U) : False := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_sig w hw U hU (fun A => ?_) hb ha
  cases A <;> simp only [hE] <;> sep_close

/-- Copies `2` and `5` of the standard odd child after a `3`, `W_1` even. -/
theorem so25_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (0) ∈ evenTile U)
    (hb : z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ evenTile U) : False := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_sig w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close

/-- Copies `0` and `3` of the standard even child after a `2`, `W_1` odd. -/
theorem se03_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (0) ∈ oddTile U)
    (hb : z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even + texV2 (parentsAt w).even) ∈ oddTile U) : False := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close

/-- Copies `0` and `3` of the standard even child after a `2`, `W_1` even. -/
theorem se03_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (texV1Even (parentsAt w).even) ∈ oddTile U)
    (hb : z - (texV2 (parentsAt w).odd + texV2 (parentsAt w).even) ∈ oddTile U) : False := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close

/-- Copies `4` and `5` of the standard even child after a `2`, `W_1` odd. -/
theorem se45_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (texV1Odd (parentsAt w).odd) ∈ evenTile U)
    (hb : z - (texV2 (parentsAt w).odd + texV2 (parentsAt w).odd) ∈ evenTile U) : False := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close

/-- Copies `4` and `5` of the standard even child after a `2`, `W_1` even. -/
theorem se45_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (0) ∈ evenTile U)
    (hb : z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV2 (parentsAt w).odd) ∈ evenTile U) : False := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close

/-- Copies `1` and `2` of the even alternate child after a `3`, `W_1` odd. -/
theorem ae12_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ evenTile U)
    (hb : z - (texV2 (parentsAt w).odd) ∈ evenTile U) : False := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_sig w hw U hU (fun A => ?_) hb ha
  cases A <;> simp only [hE] <;> sep_close

/-- Copies `1` and `2` of the even alternate child after a `3`, `W_1` even. -/
theorem ae12_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ evenTile U)
    (hb : z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd) ∈ evenTile U) : False := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_sig w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close

/-- Copies `4` and `5` of the even alternate child after a `3`, `W_1` odd. -/
theorem ae45_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (0) ∈ oddTile U)
    (hb : z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even) ∈ oddTile U) : False := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close

/-- Copies `4` and `5` of the even alternate child after a `3`, `W_1` even. -/
theorem ae45_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.three) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (texV1Even (parentsAt w).even) ∈ oddTile U)
    (hb : z - (texV2 (parentsAt w).odd - texV1Even (parentsAt w).even + texV2 (parentsAt w).even) ∈ oddTile U) : False := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_three w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close

/-- Copies `0` and `3` of the odd alternate child after a `2`, `W_1` odd. -/
theorem ao03_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w = 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (0) ∈ oddTile U)
    (hb : z - (texV2 (parentsAt w).odd + texV2 (parentsAt w).even) ∈ oddTile U) : False := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close

/-- Copies `0` and `3` of the odd alternate child after a `2`, `W_1` even. -/
theorem ao03_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w ≠ 1) (U : Word)
    (hU : curO U = (parentsAt w).odd) {z : GInt} (ha : z - (texV1Even (parentsAt w).even) ∈ oddTile U)
    (hb : z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even + texV2 (parentsAt w).even) ∈ oddTile U) : False := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepP_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close

/-- Copies `4` and `5` of the odd alternate child after a `2`, `W_1` odd. -/
theorem ao45_of (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w = 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (texV1Odd (parentsAt w).odd) ∈ evenTile U)
    (hb : z - (texV2 (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ evenTile U) : False := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = 1 := if_pos hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close

/-- Copies `4` and `5` of the odd alternate child after a `2`, `W_1` even. -/
theorem ao45_ef (w : Word) (hw : ¬ IsBase w) (hd : w.getLast? = some Digit.two) (hph : phase w ≠ 1) (U : Word)
    (hU : curE U = (parentsAt w).even) {z : GInt} (ha : z - (0) ∈ evenTile U)
    (hb : z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ evenTile U) : False := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := vals w
  obtain ⟨r1, r2⟩ := rel_two w hw hd
  obtain ⟨c1, c2⟩ := mediant_bounds w hw
  have hE : eW w = -1 := if_neg hph
  refine sepQ_lam w hw U hU (fun A => ?_) ha hb
  cases A <;> simp only [hE] <;> sep_close

end FLatticePaper.Tiles.SameParentCopies
