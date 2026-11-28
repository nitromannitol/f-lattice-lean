import FLatticePaper.Tiles.StdPseudoAnchoredSets
import FLatticePaper.Tiles.SiteVertCover
import FLatticePaper.Tiles.SiteHullEven
import FLatticePaper.Tiles.JointFamily
import FLatticePaper.Tiles.SurgicalPartial

/-! # The midpoint of the doubled partner on the vertical side of the even tile (Case 4, even-first orientation)

For a word `wd` put `w = wd ++ [three]`. Its odd register is `P = (parentsAt wd).odd` and its even register is
`F = curE wd = 2P + Q` with `Q = (parentsAt wd).even`. The half-turn of the even tile of `wd` fixes the point
`m = (texV2 P + texV2 F + (1, -1)) / 2`, and `m` lies on the vertical side `vMinus` of that tile.

Proof. The vertical reversed word of the even tile is a ceiling word of slope `c/d = F` (`SiteHullEven.cw_vert_even`), so the
lower vertical band lemma `SiteVertCover.vband_stringSites_M` applies at `m`. Its cursor parameter is
`s = (d + c) x + (d - c) y = c + (d a - c b)` with `a/b = P` and `D = d a - c b = det(P, Q) = ±1` (the Farey frame of `wd`), and
`d ≠ 2c` by the parity of `c + d`. The placed set of the reversed vertical string at the origin is the marked set
(`StdPseudoAnchoredSets.placed_vRevStringAt_iff`).

The hypotheses `hn` (non-base) and `hW` (phase) are not used: the statement holds for every word. -/

namespace FLatticePaper.Tiles.EvenMidVMinus

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.JointFamily FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.SiteVertCover
  FLatticePaper.Tiles.SiteHullEven FLatticePaper.Tiles.SiteHullOdd FLatticePaper.Tiles.CeilWords
  FLatticePaper.Tiles.SiteInduction

/-- **The arithmetic of the midpoint.** With `c/d` the even slope, `a/b` the odd parent, `e/f` the even parent (so `c = 2a + e`,
`d = 2b + f`) and the unit determinant `af − eb = ±1`, the point `(x, y)` with `2x = (a − b) + (c − d) + 1` and
`2y = (a + b) + (c + d) − 1` has `0 ≤ y − x ≤ 2d − 2`, its band parameter is `c + D` with `D = ±1`, and `d ≠ 2c`. -/
theorem mid_arith (a b c d e f x y : ℤ) (hb : 0 < b) (hf : 0 < f) (hc : c = 2 * a + e) (hd : d = 2 * b + f)
    (hdet : a * f - e * b = 1 ∨ a * f - e * b = -1) (hc0 : 0 < c) (hev : (c + d) % 2 = 0)
    (hx : 2 * x = (a - b) + (c - d) + 1) (hy : 2 * y = (a + b) + (c + d) - 1) :
    (0 ≤ y - x ∧ y - x ≤ 2 * d - 2) ∧ ∃ D : ℤ, (D = 1 ∨ D = -1) ∧ (d + c) * x + (d - c) * y = c + D ∧ d ≠ 2 * c := by
  have hD : d * a - c * b = a * f - e * b := by rw [hc, hd]; ring
  have hyx : y - x = b + d - 1 := by omega
  refine ⟨⟨by omega, by omega⟩, d * a - c * b, ?_, ?_, ?_⟩
  · rw [hD]; exact hdet
  · have h2 : 2 * ((d + c) * x + (d - c) * y) = 2 * (c + (d * a - c * b)) := by
      linear_combination (d + c) * hx + (d - c) * hy
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2
  · intro h
    have hD' : c * (2 * a - b) = d * a - c * b := by rw [h]; ring
    have hc1 : c = 1 := by
      rcases hdet with h1 | h1
      · have key : c * (2 * a - b) = 1 := by rw [hD', hD]; exact h1
        exact Int.eq_one_of_dvd_one hc0.le ⟨2 * a - b, key.symm⟩
      · have key : c * (2 * a - b) = -1 := by rw [hD', hD]; exact h1
        exact Int.eq_one_of_dvd_one hc0.le ⟨-(2 * a - b), by linear_combination key⟩
    subst hc1
    omega

/-- **The midpoint lies on the vertical side `vMinus` of the even tile of `wd`.** The point `m` with `2 m = texV2 P + texV2 F
+ (1, -1)` (where `P` and `F` are the odd and the even registers of `wd ++ [three]`) is a site of the vertical reversed string of
the even tile of `wd` at the origin. -/
theorem mid_vMinus (wd : Word) (_hn : ¬ IsBase (wd ++ [Digit.three]))
    (_hW : W1Odd (wd ++ [Digit.three]) = false) (m : ℤ × ℤ)
    (hm : (2 : ℤ) • m = texV2 (parentsAt (wd ++ [Digit.three])).odd + texV2 (parentsAt (wd ++ [Digit.three])).even + ((1 : ℤ), (-1 : ℤ))) :
    m ∈ placedSites (sideString (hWordOf wd true) (vWordOf wd true) 0 Side.vMinus) := by
  have hstep := parentsAt_append_singleton wd Digit.three
  have hO : (parentsAt (wd ++ [Digit.three])).odd = (parentsAt wd).odd := by rw [hstep]; rfl
  have hE : (parentsAt (wd ++ [Digit.three])).even = curE wd := by rw [hstep]; rfl
  rw [hO, hE] at hm
  have hValid := parentsAt_valid wd
  obtain ⟨hbd, -, -⟩ := hValid.odd_bounds
  obtain ⟨hfd, -, -⟩ := hValid.even_bounds
  have hdet : (parentsAt wd).odd.num * (parentsAt wd).even.den - (parentsAt wd).even.num * (parentsAt wd).odd.den = 1 ∨
      (parentsAt wd).odd.num * (parentsAt wd).even.den - (parentsAt wd).even.num * (parentsAt wd).odd.den = -1 := by
    have h := hValid.unit_det
    unfold Fraction.det at h
    exact h
  have hC := cw_vert_even wd
  have hpos := curE_pos_lt wd
  have hev : ((curE wd).num + (curE wd).den) % 2 = 0 := curE_even wd
  have hcn : (curE wd).num = 2 * (parentsAt wd).odd.num + (parentsAt wd).even.num := by
    show ((parentsAt wd).combine 2 1).num = _
    simp [Parents.combine]
  have hcd : (curE wd).den = 2 * (parentsAt wd).odd.den + (parentsAt wd).even.den := by
    show ((parentsAt wd).combine 2 1).den = _
    simp [Parents.combine]
  have hx2 := congrArg Prod.fst hm
  have hy2 := congrArg Prod.snd hm
  simp only [texV2, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hx2 hy2
  obtain ⟨hMb, D, hDd, hsv, hne⟩ := mid_arith (parentsAt wd).odd.num (parentsAt wd).odd.den (curE wd).num (curE wd).den
    (parentsAt wd).even.num (parentsAt wd).even.den m.1 m.2 hbd hfd hcn hcd hdet hpos.1 hev (by omega) (by omega)
  -- the ceiling word of the reversed vertical string
  obtain ⟨ℓ', hℓ⟩ := head_q_of_ceil _ _ _ hC hpos.1 hpos.2
  rw [hℓ] at hC
  have hV : CursorV (Letter.q :: ℓ') (curE wd).num (curE wd).den := by
    intro j hj
    have h := hC.2 j (by rw [← hC.1]; exact_mod_cast hj)
    have e : (j : ℤ) * (curE wd).num = (curE wd).num * j := mul_comm _ _
    exact ⟨by linarith [h.1, e], by linarith [h.2, e]⟩
  have hlen : ((Letter.q :: ℓ').length : ℤ) = (curE wd).den := hC.1
  have hmem : (m.1 + 1, m.2 + 1) ∈ stringSites true true (Letter.q :: ℓ') := by
    rcases (show (m.1 + m.2) % 2 = 0 ∨ (m.1 + m.2) % 2 = 1 by omega) with h0 | h1
    · -- even: the parameter `l = 0`, `a = min (2c) (d - c)`
      refine vband_stringSites_M (curE wd).num (curE wd).den m.1 m.2 0
        (((curE wd).den + (curE wd).num) * m.1 + ((curE wd).den - (curE wd).num) * m.2)
        (min (2 * (curE wd).num) ((curE wd).den - (curE wd).num)) 0 ℓ' hpos.1 hpos.2 hMb hV hlen rfl
        ⟨fun h => absurd h (by omega), fun _ => ⟨rfl, rfl⟩⟩ ?_ ?_
      · rw [hsv]; omega
      · rw [hsv]; omega
    · -- odd: `a = c`, `l = min (d - c) (3c - d)`, and `l ≤ c - 1` since `d ≠ 2c`
      have hmin : min ((curE wd).den - (curE wd).num) (3 * (curE wd).num - (curE wd).den) ≤ (curE wd).num - 1 := by
        rcases lt_or_gt_of_ne hne with h | h
        · exact le_trans (min_le_left _ _) (by omega)
        · exact le_trans (min_le_right _ _) (by omega)
      refine vband_stringSites_M (curE wd).num (curE wd).den m.1 m.2 0
        (((curE wd).den + (curE wd).num) * m.1 + ((curE wd).den - (curE wd).num) * m.2)
        (curE wd).num
        (min ((curE wd).den - (curE wd).num) (3 * (curE wd).num - (curE wd).den)) ℓ' hpos.1 hpos.2 hMb hV hlen rfl
        ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by omega)⟩ ?_ ?_
      · rw [hsv]; omega
      · rw [hsv]; omega
  -- the bridge to the placed sites of the reversed vertical string
  show m ∈ placedSites (vRevStringAt (vWordOf wd true).reverse 0)
  refine (StdPseudoAnchoredSets.placed_vRevStringAt_iff _ _).2 ?_
  refine List.mem_map.2 ⟨(m.1 + 1, m.2 + 1), ?_, ?_⟩
  · rw [hℓ]; exact hmem
  · ext <;> simp

end FLatticePaper.Tiles.EvenMidVMinus
