import FLatticePaper.Tiles.AltItem4Tools
import FLatticePaper.Tiles.AltItem4PairsOddFalse
import FLatticePaper.Tiles.AltItem4PairsOddTrue
import FLatticePaper.Tiles.SiteBase
import FLatticePaper.Tiles.BaseInvariant

/-! # Item (4) of `lemma:alternate_tile_properties`, the odd alternate child, the direction `W = v₂`

For `w = u x` with `x ∈ {1, 3}`, the odd alternate tile `T̂(p₀)` carries the alternate parent piece `H = T̂(q₁) + h`, the
even alternate tile of `u` translated by `h` (`A + B - U` when `W₁` is odd, `B + U` when it is even). As in the text:
* `H` is symmetric about the centre `D` of `T̂(p₀)` (`parent_odd_sym`): `T̂(q₁)` is symmetric about its own centre and
  `2h` plus that centre is `D`;
* on `H`, `L_q ≥ L_q(h) - 2 d_q` (the claim of the text on `T̂(q₁)`), hence by the half-turn `L_q ≤ L_q(D) - L_q(h) + 2 d_q`;
  so `H` misses `H + W` and the translates by `W` of the copies `T(p₁)^{+,2}` and `T(p₁)^{-,1}` (`sepq_P`, `sepq_H`);
* `L_r ≤ L_r(D) + 2 d_r` on `T̂(p₀)` (the claim and the half-turn), while the translates by `W` of `T(p₁)^{-,2}` and
  `T(q₁)^-` lie above that bound (`sepr`);
* `T(p₁)^{+,1} + W = T(p₁)^{-,2}`, the complete overlap of the text;
* the contact `y ∈ T(q₁)^-`, `y - W ∈ H` (`contact`): then `y - W` lies in the standard copy `T(q₁) + h` of `H` (for a
  non-base `u` by `(B2)`, `AltItem4.even_far_points`, and `L_q`; for a base `u` on the explicit base tiles), and the two
  copies `T(q₁) + h` and `T(q₁)^-` are copies of `T(q₁)` in `T(p₀) + c` and `T(p₀) + c + W`, the enclosure alternative;
* the half-turn `z ↦ D + W - z` exchanges `T̂(p₀)` and `T̂(p₀) + W`, maps `H` to `H + W` and permutes the copies
  (`T(p₁)^{+,1} ↔ T(p₁)^{-,2}`, `T(p₁)^{+,2} ↔ T(p₁)^{-,1}`, `T(q₁)^+ ↔ T(q₁)^-`), which gives the remaining pairs. -/

namespace FLatticePaper.Tiles.AltItem4

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile oddChildB evenChildB)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile altRegs)
open FLatticePaper.Tiles.AltPieces
open FLatticePaper.Tiles.SiteInduction (InH)

/-- The offset `h` of the alternate parent piece of `T̂(p₀)`. -/
def hOdd (o : Bool) (p q : Fraction) : Site :=
  SurgicalAlt.coeffOff (texV1Odd p) (texV2 p) (texV1Even q) (texV2 q) (if o then (1, 1, -1, 0) else (0, 1, 1, 0))

theorem altQ1Part_eq (o : Bool) (x : Digit) (hx : x ≠ Digit.two) (aE : Tile) (p q : Fraction) :
    AltRotStep.altQ1Part o x aE p q = shift aE (hOdd o p q) := by
  cases o <;> simp [AltRotStep.altQ1Part, SurgicalAlt.altQ1Coeff, hx, hOdd]

theorem altQ1Part_two (o : Bool) (aE : Tile) (p q : Fraction) : AltRotStep.altQ1Part o Digit.two aE p q = ∅ := by
  simp [AltRotStep.altQ1Part, SurgicalAlt.altQ1Coeff]

/-- The parent piece of `T̂(p₀)` at `w = u x`, `x ≠ 2`, is `T̂(q₁)` of `u`, and `q₁` is the current even fraction of `u`. -/
theorem parent_odd_eq (u : Word) (x : Digit) (hx : x ≠ Digit.two) :
    (altRegs AltRotStep.B (u ++ [x])).2 = altEvenTile AltRotStep.B u ∧
      (parentsAt (u ++ [x])).even = SiteInduction.curE u ∧ (stateAt (u ++ [x])).tEven = evenTile u := by
  cases x with
  | one => exact ⟨(AltBounds.altRegs_one u).2, (HorizontalStep.par_one u).2, (HorizontalStep.reg_one u).2⟩
  | two => exact absurd rfl hx
  | three => exact ⟨AltBounds.altRegs_three u, (HorizontalStep.par_three u).2, (HorizontalStep.reg_three u).2⟩

theorem odd_dd (u : Word) (x : Digit) (hx : x ≠ Digit.two) :
    (parentsAt (u ++ [x])).odd.den < (parentsAt (u ++ [x])).even.den := by
  have h1 := (parentsAt_valid u).odd_bounds.1
  have h2 := (parentsAt_valid u).even_bounds.1
  cases x with
  | one =>
    rw [(HorizontalStep.par_one u).1, (HorizontalStep.par_one u).2]
    simp only [Parents.current, Parents.combine]; omega
  | two => exact absurd rfl hx
  | three =>
    rw [(HorizontalStep.par_three u).1, (HorizontalStep.par_three u).2]
    simp only [Parents.current, Parents.combine]; omega

/-- **The parent piece is symmetric about the centre of `T̂(p₀)`.** -/
theorem parent_odd_sym (u : Word) (x : Digit) (hx : x ≠ Digit.two) (z : Site) (hz : z ∈ shift (altEvenTile AltRotStep.B u) (hOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even)) :
    centreOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even - z ∈ shift (altEvenTile AltRotStep.B u) (hOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even) := by
  rw [mem_shift] at hz ⊢
  rw [altEven_halfTurn u] at hz
  cases x with
  | two => exact absurd rfl hx
  | one =>
    rw [phase_snoc_one, CeilWords.parentsAt_snoc_one] at hz ⊢
    rcases Bool.eq_false_or_eq_true (phase u == 1) with h | h <;> rw [h] at hz ⊢ <;> convert hz using 1 <;>
      ext <;> simp [hOdd, centreEven, centreOdd, SurgicalAlt.coeffOff, texV1Odd, texV1Even, texV2, Parents.current,
        Parents.combine] <;> ring
  | three =>
    rw [phase_snoc_three, CeilWords.parentsAt_snoc_three] at hz ⊢
    rcases Bool.eq_false_or_eq_true (phase u == 1) with h | h <;> rw [h] at hz ⊢ <;> convert hz using 1 <;>
      ext <;> simp [hOdd, centreEven, centreOdd, SurgicalAlt.coeffOff, texV1Odd, texV1Even, texV2, Parents.current,
        Parents.combine] <;> ring

/-- `L_q` on the parent piece, from the claim on `T̂(q₁)`. -/
theorem Lq_H (u : Word) (x : Digit) (hx : x ≠ Digit.two) (z : Site) (hz : z ∈ shift (altEvenTile AltRotStep.B u) (hOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even)) :
    (parentsAt (u ++ [x])).even.den * (hOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even).2 - (parentsAt (u ++ [x])).even.num * (hOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even).1 - 2 * (parentsAt (u ++ [x])).even.den ≤ (parentsAt (u ++ [x])).even.den * z.2 - (parentsAt (u ++ [x])).even.num * z.1 := by
  rw [mem_shift] at hz
  have h := ((AltBounds.claim_all u).2 _ hz).1
  rw [← (parent_odd_eq u x hx).2.1] at h
  simp only [Prod.fst_sub, Prod.snd_sub] at h
  linarith

/-! ### The margins, as polynomial inequalities in the entries of the parents -/

theorem margOdd_true_P2 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) (_hd : d1 < d2)
    (he : n1 * d2 - n2 * d1 = 1) : 0 < d1 * d2 + d1 * n2 + d2 * n1 - 3 * d2 - n1 * n2 + n2 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3]

theorem margOdd_true_M1 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) (hd : d1 < d2)
    (he : n1 * d2 - n2 * d1 = 1) : 0 < d2 ^ 2 + 2 * d2 * n2 - 3 * d2 - n2 ^ 2 + n2 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3, mul_pos (sub_pos.2 hd) h1, mul_pos (sub_pos.2 hd) h3, mul_pos (sub_pos.2 hd) (sub_pos.2 h2), mul_pos (sub_pos.2 hd) (sub_pos.2 h4)]

theorem margOdd_true_HH (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) (_hd : d1 < d2)
    (_he : n1 * d2 - n2 * d1 = 1) : 0 < d1 * d2 - d1 * n2 + 3 * d2 * n1 - 3 * d2 - n1 * n2 + n2 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3]

theorem margOdd_true_M2 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) (hd : d1 < d2)
    (he : n1 * d2 - n2 * d1 = 1) : 0 < d1 * d2 + 3 * d1 * n2 - 3 * d1 + d2 ^ 2 - d2 * n1 + 2 * d2 * n2 - 3 * d2 - n1 * n2 + n1 - n2 ^ 2 + n2 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3, mul_pos (sub_pos.2 hd) h1, mul_pos (sub_pos.2 hd) h3, mul_pos (sub_pos.2 hd) (sub_pos.2 h2), mul_pos (sub_pos.2 hd) (sub_pos.2 h4)]

theorem margOdd_true_Qm (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (_h4 : n2 < d2) (hd : d1 < d2)
    (he : n1 * d2 - n2 * d1 = 1) : 0 < d1 ^ 2 + d1 * d2 + 2 * d1 * n1 + 2 * d1 * n2 - 3 * d1 - 3 * d2 - n1 ^ 2 - n1 * n2 + n1 + n2 := by
  rcases (show d1 = 2 ∨ 3 ≤ d1 by omega) with rfl | h
  · obtain rfl : n1 = 1 := by omega
    linarith
  · nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ d2) (by omega : (0 : ℤ) ≤ d1 - 3),
      mul_nonneg (by omega : (0 : ℤ) ≤ d1) (by omega : (0 : ℤ) ≤ d1 - 3), mul_pos h1 (by omega : (0 : ℤ) < 2 * d1 - n1 + 1),
      mul_pos h3 (by omega : (0 : ℤ) < 2 * d1 - n1 + 1)]

theorem margOdd_false_P2 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) (_hd : d1 < d2)
    (he : n1 * d2 - n2 * d1 = -1) : 0 < d1 * d2 + 3 * d1 * n2 - d2 * n1 - 3 * d2 - n1 * n2 + n2 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3]

theorem margOdd_false_M1 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) (hd : d1 < d2)
    (he : n1 * d2 - n2 * d1 = -1) : 0 < 2 * d1 * n2 + d2 ^ 2 - 2 * d2 * n1 + 2 * d2 * n2 - 3 * d2 - n2 ^ 2 + n2 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3, mul_pos (sub_pos.2 hd) h1, mul_pos (sub_pos.2 hd) h3, mul_pos (sub_pos.2 hd) (sub_pos.2 h2), mul_pos (sub_pos.2 hd) (sub_pos.2 h4)]

theorem margOdd_false_HH (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) (_hd : d1 < d2)
    (he : n1 * d2 - n2 * d1 = -1) : 0 < d1 * d2 + 3 * d1 * n2 - d2 * n1 - 3 * d2 - n1 * n2 + n2 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3]

theorem margOdd_false_M2 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) (hd : d1 < d2)
    (he : n1 * d2 - n2 * d1 = -1) : 0 < d1 * d2 + 2 * d1 * n2 - 3 * d1 + d2 ^ 2 + 2 * d2 * n2 - 3 * d2 - n1 * n2 + n1 - n2 ^ 2 + n2 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3, mul_pos (sub_pos.2 hd) h1, mul_pos (sub_pos.2 hd) h3, mul_pos (sub_pos.2 hd) (sub_pos.2 h2), mul_pos (sub_pos.2 hd) (sub_pos.2 h4)]

theorem margOdd_false_Qm (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) (hd : d1 < d2)
    (_he : n1 * d2 - n2 * d1 = -1) : 0 < d1 ^ 2 + d1 * d2 + 2 * d1 * n1 - 3 * d1 + 2 * d2 * n1 - 3 * d2 - n1 ^ 2 - n1 * n2 + n1 + n2 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3, mul_pos (sub_pos.2 hd) h1, mul_pos (sub_pos.2 hd) h3, mul_pos (sub_pos.2 hd) (sub_pos.2 h2), mul_pos (sub_pos.2 hd) (sub_pos.2 h4)]

/-! ### The separations -/

/-- **`H` misses the translates by `W` of `T(p₁)^{+,2}` and `T(p₁)^{-,1}`** (`L_q`). -/
theorem sepq_P (u : Word) (x : Digit) (hx : x ≠ Digit.two) (hw : ¬ IsBase (u ++ [x])) (a z : Site)
    (ha : a = AltRotStep.shP (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even + AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .dsP1Plus ∨
      a = AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .dsP1Minus)
    (h1 : z ∈ shift (altEvenTile AltRotStep.B u) (hOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even)) (h2 : z - latV (u ++ [x]) false 0 1 ∈ shift (stateAt (u ++ [x])).tOdd a) : False := by
  have hU := Lq_H u x hx _ (parent_odd_sym u x hx z h1)
  have hdd := odd_dd u x hx
  have hL := Lq_pcopy hw hdd a _ h2
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, -, -⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  rcases ha with rfl | rfl <;>
    rcases AltBounds.phase_cases (u ++ [x]) with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;> rw [ho] at hU hL <;>
    rw [hph] at hdet <;> norm_num at hdet <;>
    simp only [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, hOdd, centreOdd, latV, latV1, fracOf, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg, if_true, if_false, Bool.false_eq_true] at hU hL <;>
    generalize (parentsAt (u ++ [x])).odd.num = n1 at * <;> generalize (parentsAt (u ++ [x])).odd.den = d1 at * <;>
    generalize (parentsAt (u ++ [x])).even.num = n2 at * <;> generalize (parentsAt (u ++ [x])).even.den = d2 at *
  · nlinarith [margOdd_true_P2 n1 d1 n2 d2 h1 h2 h3 h4 hdd hdet]
  · nlinarith [margOdd_false_P2 n1 d1 n2 d2 h1 h2 h3 h4 hdd hdet]
  · nlinarith [margOdd_true_M1 n1 d1 n2 d2 h1 h2 h3 h4 hdd hdet]
  · nlinarith [margOdd_false_M1 n1 d1 n2 d2 h1 h2 h3 h4 hdd hdet]

/-- **`H` misses `H + W`** (`L_q`). -/
theorem sepq_H (u : Word) (x : Digit) (hx : x ≠ Digit.two) (hw : ¬ IsBase (u ++ [x])) (z : Site)
    (h1 : z ∈ shift (altEvenTile AltRotStep.B u) (hOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even)) (h2 : z - latV (u ++ [x]) false 0 1 ∈ shift (altEvenTile AltRotStep.B u) (hOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even)) : False := by
  have hU := Lq_H u x hx _ (parent_odd_sym u x hx z h1)
  have hL := Lq_H u x hx _ h2
  have hdd := odd_dd u x hx
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, -, -⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  rcases AltBounds.phase_cases (u ++ [x]) with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;> rw [ho] at hU hL <;>
    rw [hph] at hdet <;> norm_num at hdet <;>
    simp only [SurgicalAlt.coeffOff, texV1Odd, texV1Even, texV2, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, hOdd, centreOdd, latV, latV1, fracOf, Prod.fst_sub, Prod.snd_sub, if_true, if_false, Bool.false_eq_true] at hU hL <;>
    generalize (parentsAt (u ++ [x])).odd.num = n1 at * <;> generalize (parentsAt (u ++ [x])).odd.den = d1 at * <;>
    generalize (parentsAt (u ++ [x])).even.num = n2 at * <;> generalize (parentsAt (u ++ [x])).even.den = d2 at *
  · nlinarith [margOdd_true_HH n1 d1 n2 d2 h1 h2 h3 h4 hdd hdet]
  · nlinarith [margOdd_false_HH n1 d1 n2 d2 h1 h2 h3 h4 hdd hdet]

/-- **`T̂(p₀)` misses the translates by `W` of `T(p₁)^{-,2}` and `T(q₁)^-`** (`L_r`). -/
theorem sepr (u : Word) (x : Digit) (hx : x ≠ Digit.two) (hw : ¬ IsBase (u ++ [x])) (T : Tile) (a z : Site)
    (ha : (T = (stateAt (u ++ [x])).tOdd ∧
        a = AltRotStep.shP (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even + AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .dsP1Minus) ∨
      (T = (stateAt (u ++ [x])).tEven ∧ a = AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .q1Minus))
    (h1 : z ∈ altOddTile AltRotStep.B (u ++ [x])) (h2 : z - latV (u ++ [x]) false 0 1 ∈ shift T a) : False := by
  have hD := (altOdd_halfTurn (u ++ [x]) z).1 h1
  have hU := ((AltBounds.claim_all (u ++ [x])).1 _ hD).1
  have hdd := odd_dd u x hx
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, -, -⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hL := Lr_pcopy hw _ _ h2
    rcases AltBounds.phase_cases (u ++ [x]) with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;> rw [ho] at hU hL <;>
      rw [hph] at hdet <;> norm_num at hdet <;>
      simp only [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, centreOdd, latV, latV1, fracOf, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg, if_true, if_false, Bool.false_eq_true] at hU hL <;>
      generalize (parentsAt (u ++ [x])).odd.num = n1 at * <;> generalize (parentsAt (u ++ [x])).odd.den = d1 at * <;>
    generalize (parentsAt (u ++ [x])).even.num = n2 at * <;> generalize (parentsAt (u ++ [x])).even.den = d2 at *
    · nlinarith [margOdd_true_M2 n1 d1 n2 d2 h1 h2 h3 h4 hdd hdet]
    · nlinarith [margOdd_false_M2 n1 d1 n2 d2 h1 h2 h3 h4 hdd hdet]
  · have hL := Lr_qcopy hw _ _ h2
    rcases AltBounds.phase_cases (u ++ [x]) with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;> rw [ho] at hU hL <;>
      rw [hph] at hdet <;> norm_num at hdet <;>
      simp only [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, centreOdd, latV, latV1, fracOf, Prod.fst_sub, Prod.snd_sub, if_true, if_false, Bool.false_eq_true] at hU hL <;>
      generalize (parentsAt (u ++ [x])).odd.num = n1 at * <;> generalize (parentsAt (u ++ [x])).odd.den = d1 at * <;>
    generalize (parentsAt (u ++ [x])).even.num = n2 at * <;> generalize (parentsAt (u ++ [x])).even.den = d2 at *
    · nlinarith [margOdd_true_Qm n1 d1 n2 d2 h1 h2 h3 h4 hdd hdet]
    · nlinarith [margOdd_false_Qm n1 d1 n2 d2 h1 h2 h3 h4 hdd hdet]

/-! ### The contact with the parent piece -/

theorem base_contact_three (k : ℕ) (x : Digit) (hx : x ≠ Digit.two)
    (hw : ¬ IsBase (List.replicate k Digit.three ++ [x])) (z : Site)
    (h1 : z ∈ (AltRotStep.B (List.replicate k Digit.three)).2)
    (h2 : z ∈ shift (evenTile (List.replicate k Digit.three)) (AltRotStep.offP0 (phase (List.replicate k Digit.three ++ [x]) == 1) (parentsAt (List.replicate k Digit.three ++ [x])).odd (parentsAt (List.replicate k Digit.three ++ [x])).even .q1Minus - latV (List.replicate k Digit.three ++ [x]) false 0 1 - hOdd (phase (List.replicate k Digit.three ++ [x]) == 1) (parentsAt (List.replicate k Digit.three ++ [x])).odd (parentsAt (List.replicate k Digit.three ++ [x])).even)) :
    z ∈ evenTile (List.replicate k Digit.three) := by
  cases x with
  | two => exact absurd rfl hx
  | three =>
    refine absurd (Or.inr (Or.inl (fun d hd => ?_))) hw
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hd
    rcases hd with ⟨-, h⟩ | h <;> exact h
  | one =>
    exfalso
    have hB : (AltRotStep.B (List.replicate k Digit.three)).2 = PaperAltBase.stairAltF (2 * (k : ℤ) + 3) := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · show (AltRotStep.B []).2 = _
        rw [AltRotStep.B_nil]; simp
      · rw [AltRotStep.B_three k hk]
    rw [hB] at h1
    rw [SiteBase.evenTile_rep_three] at h2
    simp [mem_shift, Standard.stairF, PaperAltBase.stairAltF, PaperAltBase.boxF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, CeilWords.parentsAt_snoc_one, SiteBase.parentsAt_rep_three, phase_snoc_one, AltRotStep.phase_replicate_three, AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, SiteInduction.curO, Parents.current, Parents.combine, hOdd, latV, latV1, fracOf, Prod.fst_sub, Prod.snd_sub, Bool.false_eq_true] at h1 h2
    omega

set_option maxHeartbeats 400000 in
theorem base_contact_two (k : ℕ) (hk : 1 ≤ k) (x : Digit) (hx : x ≠ Digit.two) (z : Site)
    (h1 : z ∈ (AltRotStep.B (List.replicate k Digit.two)).2)
    (h2 : z ∈ shift (evenTile (List.replicate k Digit.two)) (AltRotStep.offP0 (phase (List.replicate k Digit.two ++ [x]) == 1) (parentsAt (List.replicate k Digit.two ++ [x])).odd (parentsAt (List.replicate k Digit.two ++ [x])).even .q1Minus - latV (List.replicate k Digit.two ++ [x]) false 0 1 - hOdd (phase (List.replicate k Digit.two ++ [x]) == 1) (parentsAt (List.replicate k Digit.two ++ [x])).odd (parentsAt (List.replicate k Digit.two ++ [x])).even)) :
    z ∈ evenTile (List.replicate k Digit.two) := by
  rw [AltRotStep.B_two k hk] at h1
  rw [BaseInvariant.evenTile_two k hk] at h2 ⊢
  cases x with
  | two => exact absurd rfl hx
  | three =>
    have hd : AltRotStep.offP0 (phase (List.replicate k Digit.two ++ [Digit.three]) == 1) (parentsAt (List.replicate k Digit.two ++ [Digit.three])).odd (parentsAt (List.replicate k Digit.two ++ [Digit.three])).even .q1Minus - latV (List.replicate k Digit.two ++ [Digit.three]) false 0 1 - hOdd (phase (List.replicate k Digit.two ++ [Digit.three]) == 1) (parentsAt (List.replicate k Digit.two ++ [Digit.three])).odd (parentsAt (List.replicate k Digit.two ++ [Digit.three])).even = (2 * (k : ℤ) + 4, -2 * (k : ℤ) - 4) := by
      ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, SiteInduction.curO, Parents.current, Parents.combine, hOdd, latV, latV1, fracOf, Bool.false_eq_true, CeilWords.parentsAt_snoc_three, SiteBase.parentsAt_rep_two, phase_snoc_three,
        AltRotStep.phase_replicate_two] <;> ring
    rw [hd] at h2
    simp only [mem_shift, Prod.ext_iff, Standard.nladderN, Standard.nladderF, PaperAltBase.nearLadderAltF, PaperAltBase.boxF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.fst_sub, Prod.snd_sub] at h1 h2 ⊢
    obtain ⟨e1, e2⟩ : z.1 = 2 * (k : ℤ) + 3 ∧ z.2 = 2 * (k : ℤ) := by omega
    rw [e1, e2]
    omega
  | one =>
    exfalso
    have hd : AltRotStep.offP0 (phase (List.replicate k Digit.two ++ [Digit.one]) == 1) (parentsAt (List.replicate k Digit.two ++ [Digit.one])).odd (parentsAt (List.replicate k Digit.two ++ [Digit.one])).even .q1Minus - latV (List.replicate k Digit.two ++ [Digit.one]) false 0 1 - hOdd (phase (List.replicate k Digit.two ++ [Digit.one]) == 1) (parentsAt (List.replicate k Digit.two ++ [Digit.one])).odd (parentsAt (List.replicate k Digit.two ++ [Digit.one])).even = (-2 * (k : ℤ) - 2, -6 * (k : ℤ) - 6) := by
      ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, SiteInduction.curO, Parents.current, Parents.combine, hOdd, latV, latV1, fracOf, Bool.false_eq_true, CeilWords.parentsAt_snoc_one, SiteBase.parentsAt_rep_two, phase_snoc_one,
        AltRotStep.phase_replicate_two] <;> ring
    rw [hd] at h2
    simp only [mem_shift, Prod.ext_iff, Standard.nladderN, Standard.nladderF, PaperAltBase.nearLadderAltF, PaperAltBase.boxF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.fst_sub, Prod.snd_sub] at h1 h2
    omega

/-- The contact for a base prefix, on the explicit base tiles. -/
theorem base_contact (u : Word) (hu : IsBase u) (x : Digit) (hx : x ≠ Digit.two) (hw : ¬ IsBase (u ++ [x])) (z : Site)
    (h1 : z ∈ altEvenTile AltRotStep.B u) (h2 : z ∈ shift (evenTile u) (AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .q1Minus - latV (u ++ [x]) false 0 1 - hOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even)) : z ∈ evenTile u := by
  rw [AltRotStep.altEvenTile_of_base _ hu] at h1
  rcases SiteBase.isBase_cases hu with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact base_contact_three k x hx hw z h1 h2
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact base_contact_three 0 x hx hw z h1 h2
    · exact base_contact_two k hk x hx z h1 h2

/-- A point of `T(q₁)^-` whose translate by `-W` lies in `H`: that translate lies in the copy `T(q₁) + h` of the standard
tile inside `H`. -/
theorem contact_mem (u : Word) (x : Digit) (hx : x ≠ Digit.two) (hw : ¬ IsBase (u ++ [x])) (y : Site)
    (hJ : y ∈ shift (stateAt (u ++ [x])).tEven (AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .q1Minus))
    (hK : y - latV (u ++ [x]) false 0 1 ∈ shift (altEvenTile AltRotStep.B u) (hOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even)) :
    y - latV (u ++ [x]) false 0 1 ∈ shift (stateAt (u ++ [x])).tEven (hOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even) := by
  rw [mem_shift] at hK ⊢
  rw [(parent_odd_eq u x hx).2.2]
  have hJ' : y - latV (u ++ [x]) false 0 1 - hOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even ∈ shift (evenTile u) (AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .q1Minus - latV (u ++ [x]) false 0 1 - hOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even) := by
    rw [(parent_odd_eq u x hx).2.2] at hJ
    rw [mem_shift] at hJ ⊢
    convert hJ using 1; abel
  by_cases hu : IsBase u
  · exact base_contact u hu x hx hw _ hK hJ'
  rcases even_far_points hu _ hK with h | h
  · exact h
  exfalso
  have hq := (AltItem5.parent_hyps hw).2.1
  have hl := lam_upper _ hq _ ((mem_qCopy_iff hw _ _).1 hJ)
  have hQ : 5 ≤ (parentsAt (u ++ [x])).even.den + (parentsAt (u ++ [x])).even.num := by
    rw [(parent_odd_eq u x hx).2.1]
    obtain ⟨a1, a2, a3, a4, -⟩ := parents_facts hu
    simp only [SiteInduction.curE, Parents.current, Parents.combine]; omega
  rw [← (parent_odd_eq u x hx).2.1] at h
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  rcases AltBounds.phase_cases (u ++ [x]) with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;> rw [ho] at h hl <;>
    rw [hph] at hdet <;> norm_num at hdet <;>
    simp only [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, hOdd, latV, latV1, fracOf, Prod.fst_sub, Prod.snd_sub, if_true, if_false, Bool.false_eq_true] at h hl <;>
    generalize (parentsAt (u ++ [x])).odd.num = n1 at * <;> generalize (parentsAt (u ++ [x])).odd.den = d1 at * <;>
  generalize (parentsAt (u ++ [x])).even.num = n2 at * <;> generalize (parentsAt (u ++ [x])).even.den = d2 at * <;>
    nlinarith

/-- **The contact**: a point of `T(q₁)^-` whose translate by `-W` lies in `H` lies in a stacked zero-one string, through the
enclosure of `T(q₁) + h` and `T(q₁)^-` in `T(p₀) + c + W` and `T(p₀) + c`. -/
theorem contact (u : Word) (x : Digit) (hx : x ≠ Digit.two) (hw : ¬ IsBase (u ++ [x])) (y : Site)
    (hJ : y ∈ shift (stateAt (u ++ [x])).tEven (AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .q1Minus))
    (hK : y - latV (u ++ [x]) false 0 1 ∈ shift (altEvenTile AltRotStep.B u) (hOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even)) : StackedAt y := by
  have hin := contact_mem u x hx hw y hJ hK
  rcases AltBounds.phase_cases (u ++ [x]) with ⟨ho, -⟩ | ⟨ho, -⟩
  · refine ⟨u ++ [x], false, texV2 (parentsAt (u ++ [x])).odd - texV1Even (parentsAt (u ++ [x])).even, 0, 1, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), ?_, ?_⟩
    · simp only [SiteStrings.tileOf, Bool.false_eq_true, if_false]
      refine mem_of_copy (e := texV2 (parentsAt (u ++ [x])).odd) (fun z hz => ?_) hJ ?_
      · rw [oddTile_eq hw, ho]
        exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ z (by simp [MixedPieces.qOffsetsOdd]) hz
      · rw [ho]; ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2] <;> ring
    · simp only [SiteStrings.tileOf, Bool.false_eq_true, if_false]
      have hin' := (mem_shift_shift_iff _ _ _ _).2 hin
      refine mem_of_copy (e := texV1Odd (parentsAt (u ++ [x])).odd) (fun z hz => ?_) hin' ?_
      · rw [oddTile_eq hw, ho]
        exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ z (by simp [MixedPieces.qOffsetsOdd]) hz
      · rw [ho]; ext <;> simp [SurgicalAlt.coeffOff, texV1Odd, texV1Even, texV2, SiteInduction.curO, Parents.current, Parents.combine, hOdd, latV, latV1, fracOf, Bool.false_eq_true] <;> ring
  · refine ⟨u ++ [x], false, texV2 (parentsAt (u ++ [x])).odd + texV1Even (parentsAt (u ++ [x])).even, 0, 1, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), ?_, ?_⟩
    · simp only [SiteStrings.tileOf, Bool.false_eq_true, if_false]
      refine mem_of_copy (e := texV1Odd (parentsAt (u ++ [x])).odd + texV2 (parentsAt (u ++ [x])).odd) (fun z hz => ?_) hJ ?_
      · rw [oddTile_eq hw, ho]
        exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ z (by simp [MixedPieces.qOffsetsOdd]) hz
      · rw [ho]; ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, Bool.false_eq_true] <;> ring
    · simp only [SiteStrings.tileOf, Bool.false_eq_true, if_false]
      have hin' := (mem_shift_shift_iff _ _ _ _).2 hin
      refine mem_of_copy (e := 0) (fun z hz => ?_) hin' ?_
      · rw [oddTile_eq hw, ho]
        exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ z (by simp [MixedPieces.qOffsetsOdd]) hz
      · rw [ho]; ext <;> simp [SurgicalAlt.coeffOff, texV1Odd, texV1Even, texV2, SiteInduction.curO, Parents.current, Parents.combine, hOdd, latV, latV1, fracOf, Prod.fst_zero, Prod.snd_zero, Bool.false_eq_true]

end FLatticePaper.Tiles.AltItem4
