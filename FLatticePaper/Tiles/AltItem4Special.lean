import FLatticePaper.Tiles.AltItem4Defs

/-! # Item (4) of `lemma:alternate_tile_properties`: six pairs separated by a linear functional of the text

Six pairs of standard copies `J` of `T̂` and `K + v` of `T̂ + v` in the directions that the text treats directly have no common
point for a reason that the boxes of the parents do not capture:
* the even child, `v = v_1 + v_2` (`W₁` even) and `v = -v_1 + v_2` (`W₁` odd), `J = T(q₁)^{+,1}`, `K = T(q₁)^{-,2}`: as in the
  text (`min_{J + Y + jX} L_s > max L_s` for `J` other than `Q^{+,1}, P^+`), `L_s` separates them; on `J` it is bounded above
  through the closed form of `s`, on `K + v` below through the closed form of `q₁` and `d_q L_s = d_s L_q - 2ε z₁`;
* the odd child, `v = v_2`, `J = T(p₁)^{+,2}`, `K = T(q₁)^+` and `J = T(q₁)^-`, `K = T(p₁)^{-,1}` in both orientations: as in the
  text (`P^{+,2} ∩ (Q^+ + W) = ∅` through `N_q`), the functional `N_q(z) = (d_q + n_q) z₁ + (d_q - n_q) z₂` separates them; on the
  copy of `q₁` it is bounded through the closed form of `q₁`, on the copy of `p₁` through `d_p N_q = d_q N_p - ε (z₁ - z₂)`. -/

namespace FLatticePaper.Tiles.AltItem4

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile oddChildB evenChildB)
open FLatticePaper.Tiles.AltPieces
open FLatticePaper.Tiles.SiteInduction (InH)

theorem lOf_ge (f : Fraction) (hf : 0 < f.num ∧ f.num < f.den) (b : Bool) : -f.den ≤ SiteInduction.lOf f b := by
  unfold SiteInduction.lOf
  split_ifs
  · omega
  · rw [le_min_iff]; omega

theorem aOf_ge (f : Fraction) (hf : 0 < f.num ∧ f.num < f.den) (b : Bool) : 1 ≤ SiteInduction.aOf f b := by
  unfold SiteInduction.aOf
  split_ifs
  · rw [le_min_iff]; omega
  · omega

/-- The functional `N_f` on a point of `H_f`. -/
theorem sCo_bounds (f : Fraction) (hf : 0 < f.num ∧ f.num < f.den) (y : Site) (hy : InH f y) :
    -f.den ≤ (f.den + f.num) * y.1 + (f.den - f.num) * y.2 ∧
      (f.den + f.num) * y.1 + (f.den - f.num) * y.2 ≤
        SiteInduction.muOf f * (f.den ^ 2 + 2 * f.den * f.num - f.num ^ 2) + 2 * f.num + f.den := by
  obtain ⟨-, -, h3, h4⟩ := hy
  have l1 := lOf_ge f hf (decide ((y.1 + y.2) % 2 = 0))
  simp only [SiteInduction.sCo, SiteInduction.tOf] at h3 h4
  constructor <;> linarith

/-- The functional `L_f` on a point of `H_f`, from above. -/
theorem lam_upper (f : Fraction) (hf : 0 < f.num ∧ f.num < f.den) (y : Site) (hy : InH f y) :
    f.den * y.2 - f.num * y.1 ≤ f.den ^ 2 + 2 * f.den * f.num - f.num ^ 2 - 1 := by
  obtain ⟨h1, -, -, -⟩ := hy
  have a1 := aOf_ge f hf (decide ((y.1 + y.2) % 2 = 0))
  simp only [SiteInduction.tCo, SiteInduction.tOf] at h1
  linarith

/-! ### The two even pairs -/

theorem Ls_core (n1 d1 n2 d2 y1 y2 : ℤ) (hd1 : 1 ≤ d1) (hq : 0 < n2 ∧ n2 < d2)
    (he : n1 * d2 - n2 * d1 = 1 ∨ n1 * d2 - n2 * d1 = -1) (hl : -(2 * d2 - 2) ≤ d2 * y2 - n2 * y1)
    (hx1 : n2 - d2 ≤ y1) (hx2 : y1 ≤ d2 + 1) :
    -(2 * (2 * d1 + d2)) ≤ (2 * d1 + d2) * y2 - (2 * n1 + n2) * y1 := by
  have key : d2 * ((2 * d1 + d2) * y2 - (2 * n1 + n2) * y1) =
      (2 * d1 + d2) * (d2 * y2 - n2 * y1) - 2 * (n1 * d2 - n2 * d1) * y1 := by ring
  have hm := mul_le_mul_of_nonneg_left hl (show (0 : ℤ) ≤ 2 * d1 + d2 by omega)
  have h1 : d2 * (-(2 * (2 * d1 + d2))) ≤ d2 * ((2 * d1 + d2) * y2 - (2 * n1 + n2) * y1) := by
    rw [key]
    rcases he with he | he <;> rw [he] <;> nlinarith
  exact le_of_mul_le_mul_left h1 (by omega)

/-- `L_s` on a copy of `T(q₁)` in the even child, from below: `L_s(z) ≥ L_s(a) - 2 d_s`. -/
theorem Ls_qcopy {w : Word} (hw : ¬ IsBase w) (a z : Site) (hz : z ∈ shift (stateAt w).tEven a) :
    (SiteInduction.curE w).den * a.2 - (SiteInduction.curE w).num * a.1 - 2 * (SiteInduction.curE w).den ≤
      (SiteInduction.curE w).den * z.2 - (SiteInduction.curE w).num * z.1 := by
  obtain ⟨hp, hq, -, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hy := (mem_qCopy_iff hw a z).1 hz
  have hl := H3Data.lam_bound_InH _ hq.1.le _ hy
  have hb := inH_box _ hq.1 hq.2 _ hy
  rw [hmq] at hb
  simp only [Prod.fst_sub, Prod.snd_sub] at hl hb
  have hmax : max (parentsAt w).even.den (2 * (parentsAt w).even.num) ≤ 2 * (parentsAt w).even.den - 2 :=
    max_le (by omega) (by omega)
  have he : (parentsAt w).odd.num * (parentsAt w).even.den - (parentsAt w).even.num * (parentsAt w).odd.den = 1 ∨
      (parentsAt w).odd.num * (parentsAt w).even.den - (parentsAt w).even.num * (parentsAt w).odd.den = -1 := by
    rw [hdet]; split_ifs <;> simp
  have hc := Ls_core _ _ _ _ (z.1 - a.1) (z.2 - a.2) (by omega) hq he (by linarith) (by linarith) (by linarith)
  simp only [SiteInduction.curE, Parents.current, Parents.combine, one_mul]
  nlinarith

theorem Nq_qcopy {w : Word} (hw : ¬ IsBase w) (b z : Site) (hz : z ∈ shift (stateAt w).tEven b) :
    -(parentsAt w).even.den ≤ ((parentsAt w).even.den + (parentsAt w).even.num) * (z.1 - b.1) + ((parentsAt w).even.den - (parentsAt w).even.num) * (z.2 - b.2) ∧
      ((parentsAt w).even.den + (parentsAt w).even.num) * (z.1 - b.1) + ((parentsAt w).even.den - (parentsAt w).even.num) * (z.2 - b.2) ≤
        ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2) + 2 * (parentsAt w).even.num + (parentsAt w).even.den := by
  obtain ⟨-, hq, -, hmq⟩ := AltItem5.parent_hyps hw
  have h := sCo_bounds _ hq _ ((mem_qCopy_iff hw b z).1 hz)
  rw [hmq, one_mul] at h
  simpa only [Prod.fst_sub, Prod.snd_sub] using h

theorem Nq_pcopy {w : Word} (hw : ¬ IsBase w) (a z : Site) (hz : z ∈ shift (stateAt w).tOdd a) :
    -((parentsAt w).even.den * (parentsAt w).odd.den) - 2 * (parentsAt w).odd.den - 2 ≤
        (parentsAt w).odd.den * (((parentsAt w).even.den + (parentsAt w).even.num) * (z.1 - a.1) + ((parentsAt w).even.den - (parentsAt w).even.num) * (z.2 - a.2)) ∧
      (parentsAt w).odd.den * (((parentsAt w).even.den + (parentsAt w).even.num) * (z.1 - a.1) + ((parentsAt w).even.den - (parentsAt w).even.num) * (z.2 - a.2)) ≤
        (parentsAt w).even.den * (2 * ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2) + 2 * (parentsAt w).odd.num + (parentsAt w).odd.den) +
          2 * (parentsAt w).odd.den + 2 := by
  obtain ⟨hp, hq, hmp, -⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hy := (mem_pCopy_iff hw a z).1 hz
  have h := sCo_bounds _ hp _ hy
  have hb := inH_box _ hp.1 hp.2 _ hy
  rw [hmp] at h hb
  simp only [Prod.fst_sub, Prod.snd_sub] at h hb
  have he : (parentsAt w).odd.num * (parentsAt w).even.den - (parentsAt w).even.num * (parentsAt w).odd.den = 1 ∨ (parentsAt w).odd.num * (parentsAt w).even.den - (parentsAt w).even.num * (parentsAt w).odd.den = -1 := by
    rw [hdet]; split_ifs <;> simp
  have key : (parentsAt w).odd.den * (((parentsAt w).even.den + (parentsAt w).even.num) * (z.1 - a.1) + ((parentsAt w).even.den - (parentsAt w).even.num) * (z.2 - a.2)) =
      (parentsAt w).even.den * (((parentsAt w).odd.den + (parentsAt w).odd.num) * (z.1 - a.1) + ((parentsAt w).odd.den - (parentsAt w).odd.num) * (z.2 - a.2)) -
        ((parentsAt w).odd.num * (parentsAt w).even.den - (parentsAt w).even.num * (parentsAt w).odd.den) * ((z.1 - a.1) - (z.2 - a.2)) := by ring
  have hq0 : (0 : ℤ) ≤ (parentsAt w).even.den := by omega
  rw [key]
  have m1 := mul_le_mul_of_nonneg_left h.1 hq0
  have m2 := mul_le_mul_of_nonneg_left h.2 hq0
  rcases he with he | he <;> rw [he] <;> constructor <;> nlinarith

/-- The even child, `W₁` even, `v = v_1 + v_2`: `T(q₁)^{+,1}` and `T(q₁)^{-,2} + v` are separated by `L_s`. -/
theorem sep_even_false_11_25 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus))
    (hK : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) 1)) : False := by
  obtain ⟨hp, hq, -, -⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 0 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    have : phase w ≠ 1 := fun h => by rw [h] at ho; simp at ho
    omega
  rw [hph] at hdet
  norm_num at hdet
  have hJs : x ∈ evenTile w := by
    rw [evenTile_eq hw, ho]
    have e : AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus = (0 : Site) := by ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2]
    rw [e] at hJ
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ x (by simp [MixedPieces.qOffsetsEven]) hJ
  have hup := lam_upper _ (SiteHullEven.curE_pos_lt w) x ((SubEvenCopy.mem_evenTile_iff w x).1 hJs)
  have hlow := Ls_qcopy hw _ x hK
  simp only [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, if_true, if_false,
    Bool.false_eq_true] at hup hlow
  nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1, mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2), mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]

/-- The even child, `W₁` odd, `v = -v_1 + v_2`: `T(q₁)^{+,1}` and `T(q₁)^{-,2} + v` are separated by `L_s`. -/
theorem sep_even_true_m11_25 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = true) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .dsQ1Plus))
    (hK : x ∈ shift (stateAt w).tEven (AltRotStep.shQ true (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) 1)) : False := by
  obtain ⟨hp, hq, -, -⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 1 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    simpa using ho
  rw [hph] at hdet
  norm_num at hdet
  have hJs : x ∈ evenTile w := by
    rw [evenTile_eq hw, ho]
    have e : AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .dsQ1Plus = texV1Odd (parentsAt w).odd := by ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2]
    rw [e] at hJ
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ x (by simp [MixedPieces.qOffsetsEven]) hJ
  have hup := lam_upper _ (SiteHullEven.curE_pos_lt w) x ((SubEvenCopy.mem_evenTile_iff w x).1 hJs)
  have hlow := Ls_qcopy hw _ x hK
  simp only [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, Prod.fst_add, Prod.snd_add, if_true,
    ] at hup hlow
  nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1, mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2), mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]

/-! ### The margins of the four odd pairs, as polynomial inequalities in the entries of the parents -/

theorem marg_aux (n2 d2 : ℤ) (h3 : 0 < n2) (hd2 : n2 + 2 ≤ d2) :
    4 ≤ d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2 - 2 * d2 - 2 * n2 - 2 := by
  nlinarith [mul_le_mul (show (2 : ℤ) ≤ d2 - n2 by omega) (show d2 + n2 ≤ d2 + n2 from le_rfl) (by omega) (by omega)]

theorem margF14 (_n1 d1 n2 d2 : ℤ) (hd1 : 2 ≤ d1) (h3 : 0 < n2) (hd2 : n2 + 2 ≤ d2) :
    0 < d1 * d2 ^ 2 + 2 * d1 * d2 * n2 - 2 * d1 * d2 - d1 * n2 ^ 2 - 2 * d1 * n2 - 2 * d1 - 2 := by
  have hM := marg_aux n2 d2 h3 hd2
  nlinarith [mul_le_mul_of_nonneg_left hM (show (0 : ℤ) ≤ d1 by omega)]

theorem margT52 (n1 d1 n2 d2 : ℤ) (hd1 : 2 ≤ d1) (h3 : 0 < n2) (hd2 : n2 + 2 ≤ d2) (he : n1 * d2 - n2 * d1 = 1) :
    0 < 2 * d1 ^ 2 * n2 + d1 * d2 ^ 2 - 2 * d1 * d2 * n1 + 2 * d1 * d2 * n2 - 2 * d1 * d2 - d1 * n2 ^ 2 -
      2 * d1 * n2 - 2 * d1 - 2 := by
  have hM := marg_aux n2 d2 h3 hd2
  have e1 : 2 * d1 ^ 2 * n2 - 2 * d1 * d2 * n1 = -2 * d1 := by
    have : 2 * d1 * (n1 * d2 - n2 * d1) = 2 * d1 := by rw [he]; ring
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hM (show (0 : ℤ) ≤ d1 by omega)]

theorem margF52 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (hd1 : 2 ≤ d1) (h3 : 0 < n2) (hd2 : n2 + 2 ≤ d2)
    (he : n1 * d2 - n2 * d1 = -1) :
    0 < d1 * d2 ^ 2 + 2 * d1 * d2 * n2 - 2 * d1 * d2 - 2 * d1 * n1 * n2 - d1 * n2 ^ 2 - 2 * d1 + 2 * d2 * n1 ^ 2 -
      2 * d2 * n1 - 2 := by
  have e1 : d1 * n2 = n1 * d2 + 1 := by linarith
  have e2 : 2 * d1 * d2 * n2 = 2 * n1 * d2 ^ 2 + 2 * d2 := by rw [show 2 * d1 * d2 * n2 = 2 * d2 * (d1 * n2) by ring, e1]; ring
  have e3 : 2 * d1 * n1 * n2 = 2 * n1 ^ 2 * d2 + 2 * n1 := by rw [show 2 * d1 * n1 * n2 = 2 * n1 * (d1 * n2) by ring, e1]; ring
  have e4 : d1 * n2 ^ 2 = n1 * n2 * d2 + n2 := by rw [show d1 * n2 ^ 2 = n2 * (d1 * n2) by ring, e1]; ring
  have h5 : 3 * d1 ≤ d1 * (d2 * (d2 - 2)) := by
    have : 3 ≤ d2 * (d2 - 2) := by nlinarith
    nlinarith
  have h6 : 3 * n1 * d2 ≤ n1 * d2 * (2 * d2 - n2 - 2) := by
    have : 3 ≤ 2 * d2 - n2 - 2 := by omega
    have : (0 : ℤ) ≤ n1 * d2 := mul_nonneg (by omega) (by omega)
    nlinarith
  nlinarith

theorem margT14 (n1 d1 n2 d2 : ℤ) (_h1 : 0 < n1) (h2 : n1 < d1) (hd1 : 2 ≤ d1) (h3 : 0 < n2) (hd2 : n2 + 2 ≤ d2)
    (he : n1 * d2 - n2 * d1 = 1) :
    0 < 2 * d1 ^ 2 * n2 + d1 * d2 ^ 2 - 2 * d1 * d2 * n1 + 2 * d1 * d2 * n2 - 2 * d1 * d2 - 2 * d1 * n1 * n2 -
      d1 * n2 ^ 2 - 2 * d1 + 2 * d2 * n1 ^ 2 - 2 * d2 * n1 - 2 := by
  have e1 : 2 * d1 ^ 2 * n2 - 2 * d1 * d2 * n1 = -2 * d1 := by
    have : 2 * d1 * (n1 * d2 - n2 * d1) = 2 * d1 := by rw [he]; ring
    linarith
  have e2 : -2 * d1 * n1 * n2 + 2 * d2 * n1 ^ 2 = 2 * n1 := by
    have : 2 * n1 * (n1 * d2 - n2 * d1) = 2 * n1 := by rw [he]; ring
    linarith
  have hT : 0 ≤ d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2 - 4 * d2 - 2 := by
    nlinarith [mul_le_mul (show (2 : ℤ) ≤ d2 - n2 by omega) (show d2 + n2 ≤ d2 + n2 from le_rfl) (by omega) (by omega)]
  have h7 : 2 * n1 * (d2 - 1) ≤ 2 * (d1 - 1) * (d2 - 1) := by
    apply mul_le_mul_of_nonneg_right _ (by omega); omega
  nlinarith [mul_le_mul_of_nonneg_left hT (show (0 : ℤ) ≤ d1 by omega)]

/-- The odd child, `W₁` even, `v = v_2`: the copies 1 and 4 + `v` are separated by `N_q`. -/
theorem sep_odd_false_01_14 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) (hK : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus + latV w false 0 1)) : False := by
  obtain ⟨hp, hq, -, -⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, hpo, hqe, hdet⟩ := parents_facts hw
  have hph : phase w = 0 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    have : phase w ≠ 1 := fun h => by rw [h] at ho; simp at ho
    omega
  rw [hph] at hdet
  norm_num at hdet
  have h1 := Nq_pcopy hw _ x hJ
  have h2 := Nq_qcopy hw _ x hK
  simp only [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, Prod.fst_add, Prod.snd_add,
    if_false, Bool.false_eq_true] at h1 h2
  generalize (parentsAt w).odd.num = n1 at *
  generalize (parentsAt w).odd.den = d1 at *
  generalize (parentsAt w).even.num = n2 at *
  generalize (parentsAt w).even.den = d2 at *
  have hd1 : 2 ≤ d1 := by omega
  have hd2 : n2 + 2 ≤ d2 := by omega
  have hm := margF14 n1 d1 n2 d2 hd1 hq.1 hd2
  have hq0 : (0 : ℤ) ≤ d1 := by omega
  nlinarith [mul_le_mul_of_nonneg_left h2.1 hq0, mul_le_mul_of_nonneg_left h2.2 hq0]

/-- The odd child, `W₁` even, `v = v_2`: the copies 5 and 2 + `v` are separated by `N_q`. -/
theorem sep_odd_false_01_52 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus)) (hK : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false 0 1)) : False := by
  obtain ⟨hp, hq, -, -⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, hpo, hqe, hdet⟩ := parents_facts hw
  have hph : phase w = 0 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    have : phase w ≠ 1 := fun h => by rw [h] at ho; simp at ho
    omega
  rw [hph] at hdet
  norm_num at hdet
  have h1 := Nq_qcopy hw _ x hJ
  have h2 := Nq_pcopy hw _ x hK
  simp only [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, Prod.fst_add, Prod.snd_add,
    if_false, Bool.false_eq_true] at h1 h2
  generalize (parentsAt w).odd.num = n1 at *
  generalize (parentsAt w).odd.den = d1 at *
  generalize (parentsAt w).even.num = n2 at *
  generalize (parentsAt w).even.den = d2 at *
  have hd1 : 2 ≤ d1 := by omega
  have hd2 : n2 + 2 ≤ d2 := by omega
  have hm := margF52 n1 d1 n2 d2 hp.1 hd1 hq.1 hd2 hdet
  have hq0 : (0 : ℤ) ≤ d1 := by omega
  nlinarith [mul_le_mul_of_nonneg_left h1.1 hq0, mul_le_mul_of_nonneg_left h1.2 hq0]

/-- The odd child, `W₁` odd, `v = v_2`: the copies 1 and 4 + `v` are separated by `N_q`. -/
theorem sep_odd_true_01_14 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = true) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.shP true (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .dsP1Plus)) (hK : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .q1Plus + latV w false 0 1)) : False := by
  obtain ⟨hp, hq, -, -⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, hpo, hqe, hdet⟩ := parents_facts hw
  have hph : phase w = 1 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    simpa using ho
  rw [hph] at hdet
  norm_num at hdet
  have h1 := Nq_pcopy hw _ x hJ
  have h2 := Nq_qcopy hw _ x hK
  simp only [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, if_true,
    if_false, Bool.false_eq_true] at h1 h2
  generalize (parentsAt w).odd.num = n1 at *
  generalize (parentsAt w).odd.den = d1 at *
  generalize (parentsAt w).even.num = n2 at *
  generalize (parentsAt w).even.den = d2 at *
  have hd1 : 2 ≤ d1 := by omega
  have hd2 : n2 + 2 ≤ d2 := by omega
  have hm := margT14 n1 d1 n2 d2 hp.1 hp.2 hd1 hq.1 hd2 hdet
  have hq0 : (0 : ℤ) ≤ d1 := by omega
  nlinarith [mul_le_mul_of_nonneg_left h2.1 hq0, mul_le_mul_of_nonneg_left h2.2 hq0]

/-- The odd child, `W₁` odd, `v = v_2`: the copies 5 and 2 + `v` are separated by `N_q`. -/
theorem sep_odd_true_01_52 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = true) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .q1Minus)) (hK : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false 0 1)) : False := by
  obtain ⟨hp, hq, -, -⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, hpo, hqe, hdet⟩ := parents_facts hw
  have hph : phase w = 1 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    simpa using ho
  rw [hph] at hdet
  norm_num at hdet
  have h1 := Nq_qcopy hw _ x hJ
  have h2 := Nq_pcopy hw _ x hK
  simp only [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, Prod.fst_add, Prod.snd_add, if_true,
    if_false, Bool.false_eq_true] at h1 h2
  generalize (parentsAt w).odd.num = n1 at *
  generalize (parentsAt w).odd.den = d1 at *
  generalize (parentsAt w).even.num = n2 at *
  generalize (parentsAt w).even.den = d2 at *
  have hd1 : 2 ≤ d1 := by omega
  have hd2 : n2 + 2 ≤ d2 := by omega
  have hm := margT52 n1 d1 n2 d2 hd1 hq.1 hd2 hdet
  have hq0 : (0 : ℤ) ≤ d1 := by omega
  nlinarith [mul_le_mul_of_nonneg_left h1.1 hq0, mul_le_mul_of_nonneg_left h1.2 hq0]

end FLatticePaper.Tiles.AltItem4
