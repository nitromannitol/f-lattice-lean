import FLatticePaper.Tiles.AltItem4H
import FLatticePaper.Tiles.EncUpper
import FLatticePaper.Tiles.AltItem4Special

/-! # Item (4) of `lemma:alternate_tile_properties`: tools for the odd child in the direction `v₂`

* `transfer_core` and the copy bounds: on a copy `T(f) + a` of a parent, `L_t ≥ L_t(a) - 2 d_t` for the children `t` and for
  `t = q₁` (with `d_{p₁} < d_{q₁}`), from `d_f L_t = d_t L_f + e z₁` (the identity the text uses throughout Step 2);
* the half-turn of a standard tile about `C_f = v_{f,1} + v_{f,2} + 1 - i` (`EncUpper.inH_refl` on the closed form), and the
  transport of `StackedAt` through a half-turn of the plane;
* `even_far_points` ((B2) in the text's proof of (4)): a point of the even alternate tile of a non-base word that is not in
  its standard even tile has `L_s ≥ d_s + n_s - 7`. -/

namespace FLatticePaper.Tiles.AltItem4

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile oddChildB evenChildB)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile altRegs)
open FLatticePaper.Tiles.AltPieces
open FLatticePaper.Tiles.SiteInduction (InH)

/-! ### The transfer -/

theorem transfer_core (dt nt df nf y1 y2 e : ℤ) (hdf : 0 < df) (hdt : 0 ≤ dt)
    (hL : -(2 * df - 2) ≤ df * y2 - nf * y1) (he : dt * nf - df * nt = e) (hey : -(2 * dt) ≤ e * y1) :
    -2 * dt ≤ dt * y2 - nt * y1 := by
  have key : df * (dt * y2 - nt * y1) = dt * (df * y2 - nf * y1) + e * y1 := by rw [← he]; ring
  have hm := mul_le_mul_of_nonneg_left hL hdt
  have h1 : df * (-2 * dt) ≤ df * (dt * y2 - nt * y1) := by rw [key]; nlinarith
  exact le_of_mul_le_mul_left h1 hdf

/-- The bounds of a point of `H_f` used by the transfer. -/
theorem inH_transfer_data (f : Fraction) (hf : 0 < f.num ∧ f.num < f.den) (y : Site) (hy : InH f y) :
    -(2 * f.den - 2) ≤ f.den * y.2 - f.num * y.1 ∧ f.num - f.den ≤ y.1 ∧
      y.1 ≤ SiteInduction.muOf f * f.den + 1 := by
  have hl := H3Data.lam_bound_InH f hf.1.le y hy
  have hb := inH_box f hf.1 hf.2 y hy
  have hmax : max f.den (2 * f.num) ≤ 2 * f.den - 2 := max_le (by omega) (by omega)
  exact ⟨by linarith, hb.1, hb.2.1⟩

/-- **The transfer on a copy of a parent**: for `z ∈ T(f) + a` and a fraction `t` with `d_t n_f - d_f n_t = e`,
`L_t(z) ≥ L_t(a) - 2 d_t` once `e z₁ ≥ -2 d_t` on the box of `f`. -/
theorem copy_lower (t f : Fraction) (ht : 0 ≤ t.den) (hf : 0 < f.num ∧ f.num < f.den) (e : ℤ)
    (he : t.den * f.num - f.den * t.num = e)
    (hey : ∀ y1 : ℤ, f.num - f.den ≤ y1 → y1 ≤ SiteInduction.muOf f * f.den + 1 → -(2 * t.den) ≤ e * y1)
    (a z : Site) (hz : InH f (z - a)) :
    t.den * a.2 - t.num * a.1 - 2 * t.den ≤ t.den * z.2 - t.num * z.1 := by
  obtain ⟨h1, h2, h3⟩ := inH_transfer_data f hf _ hz
  have hc := transfer_core t.den t.num f.den f.num (z - a).1 (z - a).2 e (by omega) ht h1 he (hey _ h2 h3)
  simp only [Prod.fst_sub, Prod.snd_sub] at hc
  nlinarith

theorem det_cases {w : Word} (hw : ¬ IsBase w) :
    (parentsAt w).odd.num * (parentsAt w).even.den - (parentsAt w).even.num * (parentsAt w).odd.den = 1 ∨
      (parentsAt w).odd.num * (parentsAt w).even.den - (parentsAt w).even.num * (parentsAt w).odd.den = -1 := by
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  rw [hdet]; split_ifs <;> simp

/-- `L_s` on a copy of `T(p₁)` in the even child. -/
theorem Ls_pcopy {w : Word} (hw : ¬ IsBase w) (a z : Site) (hz : z ∈ shift (stateAt w).tOdd a) :
    (SiteInduction.curE w).den * a.2 - (SiteInduction.curE w).num * a.1 - 2 * (SiteInduction.curE w).den ≤
      (SiteInduction.curE w).den * z.2 - (SiteInduction.curE w).num * z.1 := by
  obtain ⟨hp, hq, hmp, -⟩ := AltItem5.parent_hyps hw
  have hd := det_cases hw
  refine copy_lower _ _ (by simp only [SiteInduction.curE, Parents.current, Parents.combine]; omega) hp
    ((parentsAt w).odd.num * (parentsAt w).even.den - (parentsAt w).even.num * (parentsAt w).odd.den)
    (by simp only [SiteInduction.curE, Parents.current, Parents.combine]; ring) ?_ a z ((mem_pCopy_iff hw a z).1 hz)
  intro y1 h1 h2
  rw [hmp] at h2
  simp only [SiteInduction.curE, Parents.current, Parents.combine]
  rcases hd with hd | hd <;> rw [hd] <;> omega

/-- `L_r` on a copy of `T(p₁)` in the odd child. -/
theorem Lr_pcopy {w : Word} (hw : ¬ IsBase w) (a z : Site) (hz : z ∈ shift (stateAt w).tOdd a) :
    (SiteInduction.curO w).den * a.2 - (SiteInduction.curO w).num * a.1 - 2 * (SiteInduction.curO w).den ≤
      (SiteInduction.curO w).den * z.2 - (SiteInduction.curO w).num * z.1 := by
  obtain ⟨hp, hq, hmp, -⟩ := AltItem5.parent_hyps hw
  have hd := det_cases hw
  refine copy_lower _ _ (by simp only [SiteInduction.curO, Parents.current, Parents.combine]; omega) hp
    ((parentsAt w).odd.num * (parentsAt w).even.den - (parentsAt w).even.num * (parentsAt w).odd.den)
    (by simp only [SiteInduction.curO, Parents.current, Parents.combine]; ring) ?_ a z ((mem_pCopy_iff hw a z).1 hz)
  intro y1 h1 h2
  rw [hmp] at h2
  simp only [SiteInduction.curO, Parents.current, Parents.combine]
  rcases hd with hd | hd <;> rw [hd] <;> omega

/-- `L_r` on a copy of `T(q₁)` in the odd child. -/
theorem Lr_qcopy {w : Word} (hw : ¬ IsBase w) (a z : Site) (hz : z ∈ shift (stateAt w).tEven a) :
    (SiteInduction.curO w).den * a.2 - (SiteInduction.curO w).num * a.1 - 2 * (SiteInduction.curO w).den ≤
      (SiteInduction.curO w).den * z.2 - (SiteInduction.curO w).num * z.1 := by
  obtain ⟨hp, hq, -, hmq⟩ := AltItem5.parent_hyps hw
  have hd := det_cases hw
  refine copy_lower _ _ (by simp only [SiteInduction.curO, Parents.current, Parents.combine]; omega) hq
    (-((parentsAt w).odd.num * (parentsAt w).even.den - (parentsAt w).even.num * (parentsAt w).odd.den))
    (by simp only [SiteInduction.curO, Parents.current, Parents.combine]; ring) ?_ a z ((mem_qCopy_iff hw a z).1 hz)
  intro y1 h1 h2
  rw [hmq] at h2
  simp only [SiteInduction.curO, Parents.current, Parents.combine]
  rcases hd with hd | hd <;> rw [hd] <;> omega

/-- `L_q` on a copy of `T(p₁)`, when `d_{p₁} < d_{q₁}`. -/
theorem Lq_pcopy {w : Word} (hw : ¬ IsBase w) (hdd : (parentsAt w).odd.den < (parentsAt w).even.den) (a z : Site)
    (hz : z ∈ shift (stateAt w).tOdd a) :
    (parentsAt w).even.den * a.2 - (parentsAt w).even.num * a.1 - 2 * (parentsAt w).even.den ≤
      (parentsAt w).even.den * z.2 - (parentsAt w).even.num * z.1 := by
  obtain ⟨hp, hq, hmp, -⟩ := AltItem5.parent_hyps hw
  have hd := det_cases hw
  refine copy_lower _ _ (by omega) hp
    ((parentsAt w).odd.num * (parentsAt w).even.den - (parentsAt w).even.num * (parentsAt w).odd.den)
    (by ring) ?_ a z ((mem_pCopy_iff hw a z).1 hz)
  intro y1 h1 h2
  rw [hmp] at h2
  rcases hd with hd | hd <;> rw [hd] <;> omega

/-! ### The half-turn of the standard tiles and of the enclosure form -/

/-- The centre `C_f = v_{f,1} + v_{f,2} + 1 - i` of the standard tile of `f`. -/
def stdCentre (f : Fraction) : Site :=
  (SiteInduction.muOf f * f.den + f.num - f.den + 1, SiteInduction.muOf f * f.num + f.den + f.num - 1)

theorem refl_eq (f : Fraction) (z : Site) : EncUpper.refl f z = stdCentre f - z := by
  unfold EncUpper.refl stdCentre; ext <;> simp

theorem tileOf_halfTurn (u : Word) (par : Bool) (y : Site) (hy : y ∈ SiteStrings.tileOf u par) :
    stdCentre (fracOf u par) - y ∈ SiteStrings.tileOf u par := by
  cases par
  · simp only [SiteStrings.tileOf, fracOf, if_false, Bool.false_eq_true] at hy ⊢
    rw [SubOddCopy.mem_oddTile_iff] at hy ⊢
    rw [← refl_eq]; exact EncUpper.inH_refl _ _ hy
  · simp only [SiteStrings.tileOf, fracOf, if_true] at hy ⊢
    rw [SubEvenCopy.mem_evenTile_iff] at hy ⊢
    rw [← refl_eq]; exact EncUpper.inH_refl _ _ hy

/-- **The enclosure form is invariant under the half-turns of the plane.** -/
theorem stackedAt_halfTurn (c x : Site) (h : StackedAt x) : StackedAt (c - x) := by
  obtain ⟨u, par, a, i, j, hn, h1, h2⟩ := h
  refine ⟨u, par, c - a - stdCentre (fracOf u par) - latV u par i j, i, j, hn, ?_, ?_⟩
  · rw [mem_shift] at h2 ⊢
    have := tileOf_halfTurn u par _ h2
    convert this using 1; abel
  · rw [mem_shift] at h1 ⊢
    have := tileOf_halfTurn u par _ h1
    convert this using 1; abel

/-! ### (B2): the points of the even alternate tile outside its standard even tile -/

/-- The parent piece of the even alternate tile of `u x` (`x ≠ 3`): `L_s ≥ d_s + n_s - 7` on it. -/
theorem parent_even_far (u : Word) (x : Digit) (hx : x ≠ Digit.three) (hw : ¬ IsBase (u ++ [x])) (z : Site)
    (h2 : z ∈ AltRotStep.altP1Part (phase (u ++ [x]) == 1) x (altRegs AltRotStep.B (u ++ [x])).1
      (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even) :
    (SiteInduction.curE (u ++ [x])).den + (SiteInduction.curE (u ++ [x])).num - 7 ≤
      (SiteInduction.curE (u ++ [x])).den * z.2 - (SiteInduction.curE (u ++ [x])).num * z.1 := by
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
  rcases AltBounds.phase_cases (u ++ [x]) with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;> rw [ho] at h2 <;>
    rw [hph] at hdet <;> norm_num at hdet <;>
    cases x <;> simp only [AltRotStep.altP1Part, SurgicalAlt.altP1Coeff, if_true, if_false, Bool.false_eq_true,
      reduceCtorEq] at h2 <;>
    (try exact absurd rfl hx) <;>
    rw [mem_shift] at h2 <;>
    obtain ⟨hL, hX⟩ := hC _ h2 <;>
    have hT := transfer_lower _ _ _ _ _ _ 3 (by omega) (by omega) he hL hX <;>
    simp only [SurgicalAlt.coeffOff, texV1Odd, texV1Even, texV2, SiteInduction.curE, Parents.current, Parents.combine, Prod.fst_sub, Prod.snd_sub] at hT ⊢ <;>
    generalize (parentsAt (u ++ _)).odd.num = n1 at * <;>
    generalize (parentsAt (u ++ _)).odd.den = d1 at * <;>
    generalize (parentsAt (u ++ _)).even.num = n2 at * <;>
    generalize (parentsAt (u ++ _)).even.den = d2 at *
  · have hd := hd1 rfl
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1, mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2), mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1, mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2), mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · have hd := hd1 rfl
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1, mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2), mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1, mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2), mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]

/-- **(B2)**: a point of the even alternate tile of a non-base word lies in its standard even tile or has
`L_s ≥ d_s + n_s - 7`. -/
theorem even_far_points {w : Word} (hw : ¬ IsBase w) (z : Site) (hz : z ∈ altEvenTile AltRotStep.B w) :
    z ∈ evenTile w ∨
      (SiteInduction.curE w).den + (SiteInduction.curE w).num - 7 ≤
        (SiteInduction.curE w).den * z.2 - (SiteInduction.curE w).num * z.1 := by
  obtain ⟨u, y, rfl⟩ := exists_snoc_of_not_base hw
  obtain ⟨y', hy', he⟩ := altEvenTile_eq AltRotStep.B hw
  rw [AltRotStep.altTypeOf_snoc] at hy'
  obtain rfl := Option.some.inj hy'
  rw [he, Finset.mem_union] at hz
  rcases hz with hz | hz
  swap
  · by_cases hy3 : y = Digit.three
    · subst hy3
      exfalso
      rcases AltBounds.phase_cases (u ++ [Digit.three]) with ⟨ho, -⟩ | ⟨ho, -⟩ <;> rw [ho] at hz <;>
        simp [AltRotStep.altP1Part, SurgicalAlt.altP1Coeff] at hz
    · exact Or.inr (parent_even_far u y hy3 hw z hz)
  obtain ⟨hp, hq, -, -⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, hpo, hqe, hdet⟩ := parents_facts hw
  rw [mem_evenStd_iff] at hz
  rcases AltBounds.phase_cases (u ++ [y]) with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;> rw [ho] at hz <;>
    rw [hph] at hdet <;> norm_num at hdet <;>
    rcases hz with ⟨a, ha, hz⟩ | ⟨a, ha, hz⟩ <;>
    simp only [evenPOffs, evenQOffs, List.mem_cons, List.not_mem_nil, or_false] at ha
  all_goals first
    | (rcases ha with rfl | rfl
       · left
         rw [AltItem4.evenTile_eq hw, ho]
         exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ z (by simp [MixedPieces.pOffsetsEven, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, Bool.false_eq_true]) hz
       · right
         have h := Ls_pcopy hw _ z hz
         simp only [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, SiteInduction.curE, Parents.current, Parents.combine, if_true, if_false, Bool.false_eq_true] at h ⊢
         nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1, mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2), mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)])
    | (rcases ha with rfl | rfl | rfl | rfl
       · left
         rw [AltItem4.evenTile_eq hw, ho]
         exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ z (by simp [MixedPieces.qOffsetsEven, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, Bool.false_eq_true]) hz
       all_goals
         right
         have h := AltItem4.Ls_qcopy hw _ z hz
         simp only [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, SiteInduction.curE, Parents.current, Parents.combine, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, if_true, if_false, Bool.false_eq_true] at h ⊢
         nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1, mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2), mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)])

end FLatticePaper.Tiles.AltItem4
