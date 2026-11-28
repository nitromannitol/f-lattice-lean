import FLatticePaper.Tiles.AltItem4Defs

/-! # Item (4) of `lemma:alternate_tile_properties`: the alternate parent piece of the even child

The alternate parent piece `H = T̂(p₁) + h` of `T̂(q₀)` (present for the types one and two) is the odd alternate tile of the
prefix `u` of `w = u x`, translated. As in the text:
* `H` is symmetric about the centre `D` of `T̂(q₀)`: `T̂(p₁)` is symmetric about its own centre `D'` (item (1)) and
  `2h + D' = D` (`parent_even_sym`);
* on `H`, `L_s ≥ L_s(h) - 2 d_s - 3` (the claim of the text on `T̂(p₁)`, `AltBounds.claim_all`, through
  `d_p L_s = d_s L_p + ε z₁`), while on `T̂(q₀)`, `L_s ≤ L_s(D) + 2 d_s` (the claim and the half-turn);
* so in the directions `v = k v₁ + v₂` (`L_s(v) = T_s`) the translate `H + v` misses `T̂(q₀)` (`parent_even_sep`), and by the
  half-turn `z ↦ D + v - z`, which exchanges `T̂` and `T̂ + v` and maps `H` to `H + v`, the piece `H` misses `T̂(q₀) + v`
  (`parent_even_sep'`). -/

namespace FLatticePaper.Tiles.AltItem4

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile oddChildB evenChildB)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile altRegs)
open FLatticePaper.Tiles.AltPieces
open FLatticePaper.Tiles.SiteInduction (InH)

theorem phase_snoc_two (w : Word) : (phase (w ++ [Digit.two]) == 1) = (phase w == 1) := by
  unfold phase
  simp

/-- The parent piece of `T̂(q₀)` at `w = u x`, `x ≠ 3`, is `T̂(p₁)` of `u` translated by the offset of the type. -/
theorem parent_even_eq (u : Word) (x : Digit) (hx : x ≠ Digit.three) :
    (altRegs AltRotStep.B (u ++ [x])).1 = altOddTile AltRotStep.B u ∧
      (parentsAt (u ++ [x])).odd = SiteInduction.curO u := by
  cases x with
  | one => exact ⟨(AltBounds.altRegs_one u).1, (HorizontalStep.par_one u).1⟩
  | two => exact ⟨AltBounds.altRegs_two u, (HorizontalStep.par_two u).1⟩
  | three => exact absurd rfl hx

/-- **The parent piece is symmetric about the centre of `T̂(q₀)`.** -/
theorem parent_even_sym (u : Word) (x : Digit) (hx : x ≠ Digit.three) (z : Site)
    (hz : z ∈ AltRotStep.altP1Part (phase (u ++ [x]) == 1) x (altRegs AltRotStep.B (u ++ [x])).1
      (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even) :
    centreEven (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even - z ∈
      AltRotStep.altP1Part (phase (u ++ [x]) == 1) x (altRegs AltRotStep.B (u ++ [x])).1
        (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even := by
  rw [(parent_even_eq u x hx).1] at hz ⊢
  have hS := altOdd_halfTurn u
  cases x with
  | three => exact absurd rfl hx
  | one =>
    rw [phase_snoc_one, CeilWords.parentsAt_snoc_one] at hz ⊢
    rcases Bool.eq_false_or_eq_true (phase u == 1) with h | h <;> rw [h] at hz ⊢ <;>
      simp only [AltRotStep.altP1Part, SurgicalAlt.altP1Coeff, Bool.not_true, Bool.not_false, if_true, if_false,
        Bool.false_eq_true, reduceCtorEq] at hz ⊢ <;>
      rw [mem_shift] at hz ⊢ <;> rw [hS] at hz <;> rw [h] at hz <;> convert hz using 1 <;>
      ext <;> simp [centreEven, centreOdd, SurgicalAlt.coeffOff, texV1Odd, texV1Even, texV2, Parents.current,
        Parents.combine] <;> ring
  | two =>
    rw [phase_snoc_two, CeilWords.parentsAt_snoc_two] at hz ⊢
    rcases Bool.eq_false_or_eq_true (phase u == 1) with h | h <;> rw [h] at hz ⊢ <;>
      simp only [AltRotStep.altP1Part, SurgicalAlt.altP1Coeff, if_true, if_false, Bool.false_eq_true,
        reduceCtorEq] at hz ⊢ <;>
      rw [mem_shift] at hz ⊢ <;> rw [hS] at hz <;> rw [h] at hz <;> convert hz using 1 <;>
      ext <;> simp [centreEven, centreOdd, SurgicalAlt.coeffOff, texV1Odd, texV1Even, texV2, Parents.current,
        Parents.combine] <;> ring

/-! ### The margins of the separation, as polynomial inequalities in the entries of the parents -/

theorem marg_even_F1 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) (_hd : d1 ≤ d2)
    (_he : n1 * d2 - n2 * d1 = -1) :
    0 < 2 * d1 ^ 2 + d1 * d2 + 4 * d1 * n1 - d1 * n2 - 6 * d1 + 3 * d2 * n1 - 3 * d2 - 2 * n1 ^ 2 - n1 * n2 + 2 * n1 + n2 - 3 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3]

theorem marg_even_T1 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) (_hd : d1 ≤ d2)
    (he : n1 * d2 - n2 * d1 = 1) :
    0 < 2 * d1 ^ 2 + d1 * d2 + 4 * d1 * n1 + d1 * n2 - 6 * d1 + d2 * n1 - 3 * d2 - 2 * n1 ^ 2 - n1 * n2 + 2 * n1 + n2 - 3 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3]

theorem marg_even_2 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) (hd2 : 3 ≤ d2) (_hd1 : 2 ≤ d1) :
    0 < 2 * d1 * d2 + 4 * d1 * n2 - 6 * d1 + d2 ^ 2 + 2 * d2 * n2 - 3 * d2 - 2 * n1 * n2 + 2 * n1 - n2 ^ 2 + n2 - 3 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3]

/-! ### The separation -/

/-- `d_f L_t = d_t L_f + ε z₁`: the claim on `T̂(f)` bounds `L_t` from below. -/
theorem transfer_lower (ds ns dp np y1 y2 m : ℤ) (hdp : 0 < dp) (hds : 0 ≤ ds)
    (he : ds * np - dp * ns = 1 ∨ ds * np - dp * ns = -1) (hL : -2 * dp ≤ dp * y2 - np * y1) (hX : |y1| ≤ m * dp) :
    -2 * ds - m ≤ ds * y2 - ns * y1 := by
  have key : dp * (ds * y2 - ns * y1) = ds * (dp * y2 - np * y1) + (ds * np - dp * ns) * y1 := by ring
  have hab := abs_le.1 hX
  have h1 : dp * (-2 * ds - m) ≤ dp * (ds * y2 - ns * y1) := by
    rw [key]
    rcases he with he | he <;> rw [he] <;> nlinarith [mul_le_mul_of_nonneg_left hL hds]
  exact le_of_mul_le_mul_left h1 hdp

/-- **`H + v` misses `T̂(q₀)`** for `v = k v₁ + v₂`. -/
theorem parent_even_sep (u : Word) (x : Digit) (hx : x ≠ Digit.three) (hw : ¬ IsBase (u ++ [x])) (k1 : ℤ) (z : Site)
    (h1 : z ∈ altEvenTile AltRotStep.B (u ++ [x]))
    (h2 : z - latV (u ++ [x]) true k1 1 ∈ AltRotStep.altP1Part (phase (u ++ [x]) == 1) x
      (altRegs AltRotStep.B (u ++ [x])).1 (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even) : False := by
  have hD := (altEven_halfTurn (u ++ [x]) z).1 h1
  have hU := ((AltBounds.claim_all (u ++ [x])).2 _ hD).1
  have hC := (AltBounds.claim_all u).1
  rw [← (parent_even_eq u x hx).2] at hC
  rw [(parent_even_eq u x hx).1] at h2
  have hd1 : x = Digit.one → (parentsAt (u ++ [x])).odd.den ≤ (parentsAt (u ++ [x])).even.den := by
    rintro rfl
    rw [(HorizontalStep.par_one u).1, (HorizontalStep.par_one u).2]
    have := (parentsAt_valid u).odd_bounds.1
    simp only [Parents.current, Parents.combine]; omega
  obtain ⟨hp, hq, -, -⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, hpo, hqe, hdet⟩ := parents_facts hw
  have hpos := SiteHullEven.curE_pos_lt (u ++ [x])
  have he : (SiteInduction.curE (u ++ [x])).den * (parentsAt (u ++ [x])).odd.num -
      (parentsAt (u ++ [x])).odd.den * (SiteInduction.curE (u ++ [x])).num = 1 ∨
      (SiteInduction.curE (u ++ [x])).den * (parentsAt (u ++ [x])).odd.num -
      (parentsAt (u ++ [x])).odd.den * (SiteInduction.curE (u ++ [x])).num = -1 := by
    have : (SiteInduction.curE (u ++ [x])).den * (parentsAt (u ++ [x])).odd.num -
        (parentsAt (u ++ [x])).odd.den * (SiteInduction.curE (u ++ [x])).num =
        (parentsAt (u ++ [x])).odd.num * (parentsAt (u ++ [x])).even.den -
          (parentsAt (u ++ [x])).even.num * (parentsAt (u ++ [x])).odd.den := by
      simp only [SiteInduction.curE, Parents.current, Parents.combine]; ring
    rw [this, hdet]; split_ifs <;> simp
  rcases AltBounds.phase_cases (u ++ [x]) with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;> rw [ho] at h2 hU <;>
    rw [hph] at hdet <;> norm_num at hdet <;>
    cases x <;> simp only [AltRotStep.altP1Part, SurgicalAlt.altP1Coeff, if_true, if_false, Bool.false_eq_true,
      reduceCtorEq] at h2 <;>
    (try exact absurd rfl hx) <;>
    rw [mem_shift] at h2 <;>
    obtain ⟨hL, hX⟩ := hC _ h2 <;>
    have hT := transfer_lower _ _ _ _ _ _ 3 (by omega) (by omega) he hL hX <;>
    simp only [centreEven, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current,
      Parents.combine, SurgicalAlt.coeffOff, texV1Odd, texV1Even, texV2, Prod.fst_sub, Prod.snd_sub, if_true, if_false,
      Bool.false_eq_true] at hU hT <;>
    generalize (parentsAt (u ++ _)).odd.num = n1 at * <;>
    generalize (parentsAt (u ++ _)).odd.den = d1 at * <;>
    generalize (parentsAt (u ++ _)).even.num = n2 at * <;>
    generalize (parentsAt (u ++ _)).even.den = d2 at *
  · have hm := marg_even_T1 n1 d1 n2 d2 hp.1 hp.2 hq.1 hq.2 (hd1 rfl) hdet
    nlinarith
  · have hm := marg_even_2 n1 d1 n2 d2 hp.1 hp.2 hq.1 hq.2 (by omega) (by omega)
    nlinarith
  · have hm := marg_even_F1 n1 d1 n2 d2 hp.1 hp.2 hq.1 hq.2 (hd1 rfl) hdet
    nlinarith
  · have hm := marg_even_2 n1 d1 n2 d2 hp.1 hp.2 hq.1 hq.2 (by omega) (by omega)
    nlinarith

/-- **`H` misses `T̂(q₀) + v`**, by the half-turn `z ↦ D + v - z`. -/
theorem parent_even_sep' (u : Word) (x : Digit) (hx : x ≠ Digit.three) (hw : ¬ IsBase (u ++ [x])) (k1 : ℤ) (z : Site)
    (h1 : z ∈ AltRotStep.altP1Part (phase (u ++ [x]) == 1) x (altRegs AltRotStep.B (u ++ [x])).1
      (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even)
    (h2 : z - latV (u ++ [x]) true k1 1 ∈ altEvenTile AltRotStep.B (u ++ [x])) : False := by
  set D := centreEven (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even
  set v := latV (u ++ [x]) true k1 1
  have hs := parent_even_sym u x hx z h1
  have ht := (altEven_halfTurn (u ++ [x]) (z - v)).1 h2
  refine parent_even_sep u x hx hw k1 (D + v - z) ?_ ?_
  · convert ht using 1; abel
  · convert hs using 1; abel

end FLatticePaper.Tiles.AltItem4
