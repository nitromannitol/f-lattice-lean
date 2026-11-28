import FLatticePaper.Tiles.StdPseudoAnchoredSets
import FLatticePaper.Tiles.SiteVertCover
import FLatticePaper.Tiles.SiteHullEven
import FLatticePaper.Tiles.SiteInduction
import FLatticePaper.Tiles.JointFamily
import FLatticePaper.Tiles.SurgicalPartial
import FLatticePaper.Tiles.SiteScope

/-! # The odd-first point on the vertical side of the even tile

For `w = wd ++ [three]` with `W1Odd w = true`, the odd register of `w` is `P = (parentsAt wd).odd` and its even register is
`F = curE wd`. The point `z = texV2 F − texV2 P + (1, −1)` lies on the vertical side `vMinus` of the even tile of `wd`.

Proof. The reversed vertical string of the even tile is a ceiling word of slope `c/d = F` (`SiteHullEven.cw_vert_even`), so the lower
vertical band lemma `SiteVertCover.vband_stringSites_M` applies at `z` once `x + y` is even, `0 ≤ y − x ≤ 2d − 2`, and the band
parameter `(d + c) x + (d − c) y` lies in `[0, 2c]`. With `a/b = P`, `e/f = Q = (parentsAt wd).even` and `c = 2a + e`, `d = 2b + f`,
these are `x + y = 2c − 2a`, `y − x = 2d − 2b − 2`, and the parameter `2c − 2D` with `D = a f − e b = det(P, Q)`. In the odd-phase
case `D = 1` by `SiteScope.det_parentsAt`. The hypothesis `hn` (non-base) is not used. -/

namespace FLatticePaper.Tiles.OddPtVMinus

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.JointFamily FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.SiteVertCover
  FLatticePaper.Tiles.SiteHullEven FLatticePaper.Tiles.SiteHullOdd FLatticePaper.Tiles.CeilWords
  FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SiteScope

/-- **The even-band points lie on `vMinus`.** For a point `p` with `p.1 + p.2` even, `0 ≤ p.2 − p.1 ≤ 2d − 2` and the band parameter
`(d + c) p.1 + (d − c) p.2` in `[0, 2c]`, the point `p` lies on the vertical side `vMinus` of the even tile of `wd`
(with `c/d = curE wd`). -/
theorem mem_vMinus_of_even (wd : Word) (p : ℤ × ℤ)
    (hM : 0 ≤ p.2 - p.1 ∧ p.2 - p.1 ≤ 2 * (curE wd).den - 2)
    (hpar : (p.1 + p.2) % 2 = 0)
    (hsl : 0 ≤ ((curE wd).den + (curE wd).num) * p.1 + ((curE wd).den - (curE wd).num) * p.2)
    (hsu : ((curE wd).den + (curE wd).num) * p.1 + ((curE wd).den - (curE wd).num) * p.2 ≤ 2 * (curE wd).num) :
    p ∈ placedSites (sideString (hWordOf wd true) (vWordOf wd true) 0 Side.vMinus) := by
  have hC := cw_vert_even wd
  have hpos := curE_pos_lt wd
  obtain ⟨ℓ', hℓ⟩ := head_q_of_ceil _ _ _ hC hpos.1 hpos.2
  rw [hℓ] at hC
  have hV : CursorV (Letter.q :: ℓ') (curE wd).num (curE wd).den := by
    intro j hj
    have h := hC.2 j (by rw [← hC.1]; exact_mod_cast hj)
    have e : (j : ℤ) * (curE wd).num = (curE wd).num * j := mul_comm _ _
    exact ⟨by linarith [h.1, e], by linarith [h.2, e]⟩
  have hlen : ((Letter.q :: ℓ').length : ℤ) = (curE wd).den := hC.1
  have hmem : (p.1 + 1, p.2 + 1) ∈ stringSites true true (Letter.q :: ℓ') :=
    vband_stringSites_M (curE wd).num (curE wd).den p.1 p.2 0
      (((curE wd).den + (curE wd).num) * p.1 + ((curE wd).den - (curE wd).num) * p.2)
      (min (2 * (curE wd).num) ((curE wd).den - (curE wd).num)) 0 ℓ' hpos.1 hpos.2 hM hV hlen rfl
      ⟨fun h => absurd h (by omega), fun _ => ⟨rfl, rfl⟩⟩ hsl (by rw [sub_zero]; exact hsu)
  show p ∈ placedSites (vRevStringAt (vWordOf wd true).reverse 0)
  refine (StdPseudoAnchoredSets.placed_vRevStringAt_iff _ _).2 ?_
  refine List.mem_map.2 ⟨(p.1 + 1, p.2 + 1), ?_, ?_⟩
  · rw [hℓ]; exact hmem
  · ext <;> simp

/-- **The arithmetic of the odd-first point.** With `c = 2a + e`, `d = 2b + f` and the unit determinant `af − eb = 1`, the point
`(x, y)` with `x = (c − d) − (a − b) + 1` and `y = (c + d) − (a + b) − 1` has `0 ≤ y − x ≤ 2d − 2`, band parameter `2c − 2`, and
`x + y` even. -/
theorem pt_arith (a b c d e f x y : ℤ) (hb : 0 < b) (hf : 0 < f) (hc : c = 2 * a + e) (hd : d = 2 * b + f)
    (hdet : a * f - e * b = 1) (hx : x = (c - d) - (a - b) + 1) (hy : y = (c + d) - (a + b) - 1) :
    (0 ≤ y - x ∧ y - x ≤ 2 * d - 2) ∧ (d + c) * x + (d - c) * y = 2 * c - 2 ∧ (x + y) % 2 = 0 := by
  subst hx hy hc hd
  refine ⟨⟨by omega, by omega⟩, ?_, by omega⟩
  linear_combination (-2 : ℤ) * hdet

/-- **The odd-first point lies on the vertical side `vMinus` of the even tile of `wd`.** For `w = wd ++ [three]` with odd phase, the
point `texV2 (parentsAt w).even − texV2 (parentsAt w).odd + (1, −1)` is a site of the vertical side. -/
theorem pt_vMinus_odd (wd : Word) (_hn : ¬ IsBase (wd ++ [Digit.three]))
    (hW : W1Odd (wd ++ [Digit.three]) = true) :
    texV2 (parentsAt (wd ++ [Digit.three])).even - texV2 (parentsAt (wd ++ [Digit.three])).odd + ((1 : ℤ), (-1 : ℤ)) ∈
      placedSites (sideString (hWordOf wd true) (vWordOf wd true) 0 Side.vMinus) := by
  have hstep := parentsAt_append_singleton wd Digit.three
  have hO : (parentsAt (wd ++ [Digit.three])).odd = (parentsAt wd).odd := by rw [hstep]; rfl
  have hE : (parentsAt (wd ++ [Digit.three])).even = curE wd := by rw [hstep]; rfl
  rw [hO, hE]
  generalize hz : texV2 (curE wd) - texV2 (parentsAt wd).odd + ((1 : ℤ), (-1 : ℤ)) = z
  -- the odd phase of `wd`, from the phase of `wd ++ [three]`
  have hph : FLatticePaper.Farey.phase wd = 1 := by
    have h1 : FLatticePaper.Farey.phase (wd ++ [Digit.three]) = 1 := by
      have h := hW
      unfold W1Odd at h
      exact beq_iff_eq.mp h
    have h2 : FLatticePaper.Farey.phase (wd ++ [Digit.three]) = FLatticePaper.Farey.phase wd := by
      unfold FLatticePaper.Farey.phase
      simp [List.count_append]
    omega
  have hdet : (parentsAt wd).odd.num * (parentsAt wd).even.den - (parentsAt wd).even.num * (parentsAt wd).odd.den = 1 := by
    have h := det_parentsAt wd
    unfold Fraction.det at h
    rw [hph] at h
    simpa using h
  obtain ⟨hbd, -, -⟩ := (parentsAt_valid wd).odd_bounds
  obtain ⟨hfd, -, -⟩ := (parentsAt_valid wd).even_bounds
  have hcn : (curE wd).num = 2 * (parentsAt wd).odd.num + (parentsAt wd).even.num := by
    show ((parentsAt wd).combine 2 1).num = _
    simp [Parents.combine]
  have hcd : (curE wd).den = 2 * (parentsAt wd).odd.den + (parentsAt wd).even.den := by
    show ((parentsAt wd).combine 2 1).den = _
    simp [Parents.combine]
  have hc0 := (curE_pos_lt wd).1
  have hx : z.1 = (curE wd).num - (curE wd).den - ((parentsAt wd).odd.num - (parentsAt wd).odd.den) + 1 := by
    rw [← hz]
    simp only [texV2, Prod.fst_add, Prod.fst_sub]
  have hy : z.2 = (curE wd).num + (curE wd).den - ((parentsAt wd).odd.num + (parentsAt wd).odd.den) - 1 := by
    rw [← hz]
    simp only [texV2, Prod.snd_add, Prod.snd_sub]
    ring
  obtain ⟨hM, hs, hpar⟩ := pt_arith (parentsAt wd).odd.num (parentsAt wd).odd.den (curE wd).num (curE wd).den
    (parentsAt wd).even.num (parentsAt wd).even.den z.1 z.2 hbd hfd hcn hcd hdet hx hy
  exact mem_vMinus_of_even wd z hM hpar (by rw [hs]; omega) (by rw [hs]; omega)

end FLatticePaper.Tiles.OddPtVMinus
