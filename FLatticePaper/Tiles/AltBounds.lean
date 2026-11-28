import FLatticePaper.Tiles.AltItem5

/-! # Bounds on the alternate tiles (the claim in the proof of item (4) of `lemma:alternate_tile_properties`)

Surgical edition 3243bef, `lemma:alternate_tile_properties`, Step 2: for `c(T̂(t)) = 0`,
`min_{T̂(t)} L_t ≥ -2 d_t` and `max_{T̂(t)} |z₁| ≤ m_t d_t`, with `L_t(z) = d_t z₂ - n_t z₁`, `m_t = 2` for an even and `m_t = 3`
for an odd fraction `t`.

The proof here follows the induction of the text, with one change in the bounds of the standard subtiles: each standard copy
of the alternate child lies in a translate `T(t) + c` of the standard tile of the child's own fraction `t`, as one of the copies
of its standard decomposition (`c ∈ {0, ±U, B ± U, A + B, B - A, B, B + V}` by the case, with
`(A, B, U, V) = (v_{p₁,1}, v_{p₁,2}, v_{q₁,1}, v_{q₁,2})`), so `L_t` on it is bounded through the closed form of `t`
(`H3Data.lam_bound_InH`), and `z₁` through the box of the parent (`AltPieces.inH_box`). The text encloses the same subtiles in
translates of the standard odd child. The alternate parent piece uses the inductive hypothesis through
`d_f L_t = d_t L_f + ε z₁`, `|ε| = 1`, as in the text. -/

namespace FLatticePaper.Tiles.AltBounds

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile oddChildB evenChildB)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.SurgicalAlt (altTypeOf)
open FLatticePaper.Tiles.AltPieces
open FLatticePaper.Tiles.SiteInduction (InH)

/-! ### Membership in the standard children through their copies -/

theorem mem_oddChildB_P (o : Bool) (T1 T2 : Tile) (p q : Fraction) (a z : Site)
    (ha : a ∈ MixedPieces.pOffsetsOdd o p q) (hz : z ∈ shift T1 a) : z ∈ oddChildB o T1 T2 p q := by
  cases o <;> simp only [MixedPieces.pOffsetsOdd, Bool.false_eq_true, ite_false, ite_true, List.mem_cons,
    List.not_mem_nil, or_false] at ha <;> rcases ha with rfl | rfl <;>
    simp only [oddChildB, Finset.mem_union] <;>
    first
    | (rw [AltRotStep.shift_zero] at hz; tauto)
    | tauto

theorem mem_oddChildB_Q (o : Bool) (T1 T2 : Tile) (p q : Fraction) (b z : Site)
    (hb : b ∈ MixedPieces.qOffsetsOdd o p q) (hz : z ∈ shift T2 b) : z ∈ oddChildB o T1 T2 p q := by
  cases o <;> simp only [MixedPieces.qOffsetsOdd, Bool.false_eq_true, ite_false, ite_true, List.mem_cons,
    List.not_mem_nil, or_false] at hb <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [oddChildB, Finset.mem_union] <;>
    first
    | (rw [AltRotStep.shift_zero] at hz; tauto)
    | tauto

theorem mem_evenChildB_P (o : Bool) (T1 T2 : Tile) (p q : Fraction) (a z : Site)
    (ha : a ∈ MixedPieces.pOffsetsEven o p q) (hz : z ∈ shift T1 a) : z ∈ evenChildB o T1 T2 p q := by
  cases o <;> simp only [MixedPieces.pOffsetsEven, Bool.false_eq_true, ite_false, ite_true, List.mem_cons,
    List.not_mem_nil, or_false] at ha <;> rcases ha with rfl | rfl | rfl | rfl <;>
    simp only [evenChildB, Finset.mem_union] <;>
    first
    | (rw [AltRotStep.shift_zero] at hz; tauto)
    | tauto

theorem mem_evenChildB_Q (o : Bool) (T1 T2 : Tile) (p q : Fraction) (b z : Site)
    (hb : b ∈ MixedPieces.qOffsetsEven o p q) (hz : z ∈ shift T2 b) : z ∈ evenChildB o T1 T2 p q := by
  cases o <;> simp only [MixedPieces.qOffsetsEven, Bool.false_eq_true, ite_false, ite_true, List.mem_cons,
    List.not_mem_nil, or_false] at hb <;> rcases hb with rfl | rfl <;>
    simp only [evenChildB, Finset.mem_union] <;>
    first
    | (rw [AltRotStep.shift_zero] at hz; tauto)
    | tauto

/-! ### The claim -/

/-- The claim of the text for a tile `T` placed with `c = 0`, fraction `f` and constant `m`. -/
def Claim (T : Tile) (f : Fraction) (m : ℤ) : Prop :=
  ∀ z ∈ T, -2 * f.den ≤ f.den * z.2 - f.num * z.1 ∧ |z.1| ≤ m * f.den

/-- **The claim on a standard copy** `T(f) + a` that lies in the translate `T(t) + c` of the standard tile of `t`: `L_t` from the
closed form of `t` and `L_t(c) ≥ -2`, `z₁` from the box of `f`. -/
theorem copy_bound (t f : Fraction) (ht : 0 < t.num ∧ t.num < t.den) (hf : 0 < f.num ∧ f.num < f.den) (m : ℤ)
    (a c z : Site) (hz1 : InH f (z - a)) (hz2 : InH t (z - c)) (hc : -2 ≤ t.den * c.2 - t.num * c.1)
    (hx1 : -(m * t.den) ≤ f.num - f.den + a.1) (hx2 : SiteInduction.muOf f * f.den + 1 + a.1 ≤ m * t.den) :
    -2 * t.den ≤ t.den * z.2 - t.num * z.1 ∧ |z.1| ≤ m * t.den := by
  have hl := H3Data.lam_bound_InH t ht.1.le (z - c) hz2
  have hb := inH_box f hf.1 hf.2 (z - a) hz1
  simp only [Prod.fst_sub, Prod.snd_sub] at hl hb
  have hmax : max t.den (2 * t.num) ≤ 2 * t.den - 2 := max_le (by omega) (by omega)
  refine ⟨?_, abs_le.2 ⟨by linarith [hb.1], by linarith [hb.2.1]⟩⟩
  nlinarith

/-- **The claim on the alternate parent piece** `T̂(f) + h` of the child `t`, from the claim for `T̂(f)`: with
`d_f n_t - n_f d_t = ±1` (the parents are Farey neighbours of the child), `L_t ≥ -2 d_t - m_f + L_t(h) ≥ -2 d_t` once
`L_t(h) ≥ m_f`. -/
theorem parent_bound (t f : Fraction) (ht : 0 < t.den) (hf : 0 < f.den) (mf mt : ℤ)
    (hdet : t.den * f.num - f.den * t.num = 1 ∨ t.den * f.num - f.den * t.num = -1) (S : Tile) (hS : Claim S f mf)
    (h z : Site) (hz : z - h ∈ S) (hh : mf ≤ t.den * h.2 - t.num * h.1) (hx1 : mf * f.den + h.1 ≤ mt * t.den)
    (hx2 : mf * f.den - h.1 ≤ mt * t.den) :
    -2 * t.den ≤ t.den * z.2 - t.num * z.1 ∧ |z.1| ≤ mt * t.den := by
  obtain ⟨hL, hX⟩ := hS (z - h) hz
  simp only [Prod.fst_sub, Prod.snd_sub] at hL hX
  have hab := abs_le.1 hX
  have key : f.den * (t.den * (z.2 - h.2) - t.num * (z.1 - h.1)) =
      t.den * (f.den * (z.2 - h.2) - f.num * (z.1 - h.1)) + (t.den * f.num - f.den * t.num) * (z.1 - h.1) := by ring
  have h1 : f.den * (-2 * t.den - mf) ≤ f.den * (t.den * (z.2 - h.2) - t.num * (z.1 - h.1)) := by
    rw [key]
    rcases hdet with hd | hd <;> rw [hd] <;> nlinarith [mul_le_mul_of_nonneg_left hL ht.le]
  have h2 := le_of_mul_le_mul_left h1 hf
  have e : t.den * (z.2 - h.2) - t.num * (z.1 - h.1) = (t.den * z.2 - t.num * z.1) - (t.den * h.2 - t.num * h.1) := by
    ring
  rw [e] at h2
  refine ⟨by linarith, abs_le.2 ⟨by linarith, by linarith⟩⟩

/-! ### The standard copies of the alternate children, one by one -/

theorem std_even_false_0 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (z : Site)
    (hz : z ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) :
    -2 * (SiteInduction.curE w).den ≤ (SiteInduction.curE w).den * z.2 - (SiteInduction.curE w).num * z.1 ∧ |z.1| ≤ 2 * (SiteInduction.curE w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 0 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    have : phase w ≠ 1 := fun h => by rw [h] at ho; simp at ho
    omega
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - ((0 : Site)) ∈ evenTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).2, ho]
    refine mem_evenChildB_P _ _ _ _ _ (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus - ((0 : Site))) (z - ((0 : Site))) ?_ ?_
    · have e : AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus - ((0 : Site)) = (MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]) := by
        ext <;> simp [MixedPieces.pOffsetsEven,
          AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, Bool.false_eq_true]
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubEvenCopy.mem_evenTile_iff w _).1 hmem
  have hz1 := (mem_pCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curE w) (parentsAt w).odd (SiteHullEven.curE_pos_lt w) hp 2 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, Prod.fst_zero, Prod.snd_zero]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true]
    omega
  · rw [hmp]
    simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true]
    omega

theorem std_even_false_1 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (z : Site)
    (hz : z ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) :
    -2 * (SiteInduction.curE w).den ≤ (SiteInduction.curE w).den * z.2 - (SiteInduction.curE w).num * z.1 ∧ |z.1| ≤ 2 * (SiteInduction.curE w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 0 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    have : phase w ≠ 1 := fun h => by rw [h] at ho; simp at ho
    omega
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - (-texV1Even (parentsAt w).even) ∈ evenTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).2, ho]
    refine mem_evenChildB_P _ _ _ _ _ (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus - (-texV1Even (parentsAt w).even)) (z - (-texV1Even (parentsAt w).even)) ?_ ?_
    · have e : AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus - (-texV1Even (parentsAt w).even) = (MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]) := by
        ext <;> simp [MixedPieces.pOffsetsEven,
          AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, Bool.false_eq_true] <;> ring
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubEvenCopy.mem_evenTile_iff w _).1 hmem
  have hz1 := (mem_pCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curE w) (parentsAt w).odd (SiteHullEven.curE_pos_lt w) hp 2 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, texV1Even, Prod.fst_neg, Prod.snd_neg]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true]
    omega
  · rw [hmp]
    simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true]
    omega

theorem std_even_false_2 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (z : Site)
    (hz : z ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    -2 * (SiteInduction.curE w).den ≤ (SiteInduction.curE w).den * z.2 - (SiteInduction.curE w).num * z.1 ∧ |z.1| ≤ 2 * (SiteInduction.curE w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 0 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    have : phase w ≠ 1 := fun h => by rw [h] at ho; simp at ho
    omega
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - ((0 : Site)) ∈ evenTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).2, ho]
    refine mem_evenChildB_Q _ _ _ _ _ (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus - ((0 : Site))) (z - ((0 : Site))) ?_ ?_
    · have e : AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus - ((0 : Site)) = (MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]) := by
        ext <;> simp [MixedPieces.qOffsetsEven,
          AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, Bool.false_eq_true, Prod.fst_zero, Prod.snd_zero]
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubEvenCopy.mem_evenTile_iff w _).1 hmem
  have hz1 := (mem_qCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curE w) (parentsAt w).even (SiteHullEven.curE_pos_lt w) hq 2 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, Prod.fst_zero, Prod.snd_zero]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true]
    omega
  · rw [hmq]
    simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true]
    omega

theorem std_even_false_3 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (z : Site)
    (hz : z ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    -2 * (SiteInduction.curE w).den ≤ (SiteInduction.curE w).den * z.2 - (SiteInduction.curE w).num * z.1 ∧ |z.1| ≤ 2 * (SiteInduction.curE w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 0 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    have : phase w ≠ 1 := fun h => by rw [h] at ho; simp at ho
    omega
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - (texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ evenTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).2, ho]
    refine mem_evenChildB_Q _ _ _ _ _ (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus - (texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) (z - (texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) ?_ ?_
    · have e : AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus - (texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) = (MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]) := by
        ext <;> simp [MixedPieces.qOffsetsEven,
          AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, Bool.false_eq_true, Prod.fst_zero, Prod.snd_zero] <;> ring
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubEvenCopy.mem_evenTile_iff w _).1 hmem
  have hz1 := (mem_qCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curE w) (parentsAt w).even (SiteHullEven.curE_pos_lt w) hq 2 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, texV1Even, texV2, Prod.fst_sub, Prod.snd_sub]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true, Prod.fst_add, Prod.fst_neg]
    omega
  · rw [hmq]
    simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true, Prod.fst_add, Prod.fst_neg]
    omega

theorem std_even_false_4 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (z : Site)
    (hz : z ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    -2 * (SiteInduction.curE w).den ≤ (SiteInduction.curE w).den * z.2 - (SiteInduction.curE w).num * z.1 ∧ |z.1| ≤ 2 * (SiteInduction.curE w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 0 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    have : phase w ≠ 1 := fun h => by rw [h] at ho; simp at ho
    omega
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd) ∈ evenTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).2, ho]
    refine mem_evenChildB_Q _ _ _ _ _ (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd)) (z - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd)) ?_ ?_
    · have e : AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus - (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd) = (MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]) := by
        ext <;> simp [MixedPieces.qOffsetsEven,
          AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, Bool.false_eq_true, Prod.fst_zero, Prod.snd_zero]
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubEvenCopy.mem_evenTile_iff w _).1 hmem
  have hz1 := (mem_qCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curE w) (parentsAt w).even (SiteHullEven.curE_pos_lt w) hq 2 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, texV1Odd, texV2, Prod.fst_add, Prod.snd_add]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true]
    omega
  · rw [hmq]
    simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true]
    omega

theorem std_even_false_5 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (z : Site)
    (hz : z ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    -2 * (SiteInduction.curE w).den ≤ (SiteInduction.curE w).den * z.2 - (SiteInduction.curE w).num * z.1 ∧ |z.1| ≤ 2 * (SiteInduction.curE w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 0 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    have : phase w ≠ 1 := fun h => by rw [h] at ho; simp at ho
    omega
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - (-texV1Even (parentsAt w).even) ∈ evenTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).2, ho]
    refine mem_evenChildB_Q _ _ _ _ _ (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus - (-texV1Even (parentsAt w).even)) (z - (-texV1Even (parentsAt w).even)) ?_ ?_
    · have e : AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus - (-texV1Even (parentsAt w).even) = (MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]) := by
        ext <;> simp [MixedPieces.qOffsetsEven,
          AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, Bool.false_eq_true] <;> ring
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubEvenCopy.mem_evenTile_iff w _).1 hmem
  have hz1 := (mem_qCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curE w) (parentsAt w).even (SiteHullEven.curE_pos_lt w) hq 2 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, texV1Even, Prod.fst_neg, Prod.snd_neg]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true, Prod.fst_add, Prod.fst_neg]
    omega
  · rw [hmq]
    simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true, Prod.fst_add, Prod.fst_neg]
    omega

theorem std_even_true_0 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = true) (z : Site)
    (hz : z ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .p1Plus)) :
    -2 * (SiteInduction.curE w).den ≤ (SiteInduction.curE w).den * z.2 - (SiteInduction.curE w).num * z.1 ∧ |z.1| ≤ 2 * (SiteInduction.curE w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 1 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    simpa using ho
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - ((0 : Site)) ∈ evenTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).2, ho]
    refine mem_evenChildB_P _ _ _ _ _ (AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .p1Plus - ((0 : Site))) (z - ((0 : Site))) ?_ ?_
    · have e : AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .p1Plus - ((0 : Site)) = (MixedPieces.pOffsetsEven true (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]) := by
        ext <;> simp [MixedPieces.pOffsetsEven,
          AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, Prod.fst_zero, Prod.snd_zero]
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubEvenCopy.mem_evenTile_iff w _).1 hmem
  have hz1 := (mem_pCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curE w) (parentsAt w).odd (SiteHullEven.curE_pos_lt w) hp 2 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, Prod.fst_zero, Prod.snd_zero]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, ite_true]
    omega
  · rw [hmp]
    simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, ite_true]
    omega

theorem std_even_true_1 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = true) (z : Site)
    (hz : z ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .p1Minus)) :
    -2 * (SiteInduction.curE w).den ≤ (SiteInduction.curE w).den * z.2 - (SiteInduction.curE w).num * z.1 ∧ |z.1| ≤ 2 * (SiteInduction.curE w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 1 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    simpa using ho
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - (texV1Even (parentsAt w).even) ∈ evenTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).2, ho]
    refine mem_evenChildB_P _ _ _ _ _ (AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .p1Minus - (texV1Even (parentsAt w).even)) (z - (texV1Even (parentsAt w).even)) ?_ ?_
    · have e : AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .p1Minus - (texV1Even (parentsAt w).even) = (MixedPieces.pOffsetsEven true (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]) := by
        ext <;> simp [MixedPieces.pOffsetsEven,
          AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2] <;> ring
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubEvenCopy.mem_evenTile_iff w _).1 hmem
  have hz1 := (mem_pCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curE w) (parentsAt w).odd (SiteHullEven.curE_pos_lt w) hp 2 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, texV1Even]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, ite_true]
    omega
  · rw [hmp]
    simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, ite_true]
    omega

theorem std_even_true_2 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = true) (z : Site)
    (hz : z ∈ shift (stateAt w).tEven (AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    -2 * (SiteInduction.curE w).den ≤ (SiteInduction.curE w).den * z.2 - (SiteInduction.curE w).num * z.1 ∧ |z.1| ≤ 2 * (SiteInduction.curE w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 1 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    simpa using ho
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - ((0 : Site)) ∈ evenTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).2, ho]
    refine mem_evenChildB_Q _ _ _ _ _ (AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .dsQ1Plus - ((0 : Site))) (z - ((0 : Site))) ?_ ?_
    · have e : AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .dsQ1Plus - ((0 : Site)) = (MixedPieces.qOffsetsEven true (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]) := by
        ext <;> simp [MixedPieces.qOffsetsEven,
          AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2]
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubEvenCopy.mem_evenTile_iff w _).1 hmem
  have hz1 := (mem_qCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curE w) (parentsAt w).even (SiteHullEven.curE_pos_lt w) hq 2 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, Prod.fst_zero, Prod.snd_zero]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, ite_true]
    omega
  · rw [hmq]
    simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, ite_true]
    omega

theorem std_even_true_3 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = true) (z : Site)
    (hz : z ∈ shift (stateAt w).tEven (AltRotStep.shQ true (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    -2 * (SiteInduction.curE w).den ≤ (SiteInduction.curE w).den * z.2 - (SiteInduction.curE w).num * z.1 ∧ |z.1| ≤ 2 * (SiteInduction.curE w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 1 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    simpa using ho
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ evenTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).2, ho]
    refine mem_evenChildB_Q _ _ _ _ _ (AltRotStep.shQ true (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .dsQ1Plus - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) ?_ ?_
    · have e : AltRotStep.shQ true (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .dsQ1Plus - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) = (MixedPieces.qOffsetsEven true (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]) := by
        ext <;> simp [MixedPieces.qOffsetsEven,
          AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2] <;> ring
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubEvenCopy.mem_evenTile_iff w _).1 hmem
  have hz1 := (mem_qCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curE w) (parentsAt w).even (SiteHullEven.curE_pos_lt w) hq 2 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, texV1Even, texV2, Prod.fst_add, Prod.snd_add]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, ite_true, Prod.fst_add]
    omega
  · rw [hmq]
    simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, ite_true, Prod.fst_add]
    omega

theorem std_even_true_4 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = true) (z : Site)
    (hz : z ∈ shift (stateAt w).tEven (AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    -2 * (SiteInduction.curE w).den ≤ (SiteInduction.curE w).den * z.2 - (SiteInduction.curE w).num * z.1 ∧ |z.1| ≤ 2 * (SiteInduction.curE w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 1 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    simpa using ho
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - (texV2 (parentsAt w).odd - texV1Odd (parentsAt w).odd) ∈ evenTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).2, ho]
    refine mem_evenChildB_Q _ _ _ _ _ (AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .dsQ1Minus - (texV2 (parentsAt w).odd - texV1Odd (parentsAt w).odd)) (z - (texV2 (parentsAt w).odd - texV1Odd (parentsAt w).odd)) ?_ ?_
    · have e : AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .dsQ1Minus - (texV2 (parentsAt w).odd - texV1Odd (parentsAt w).odd) = (MixedPieces.qOffsetsEven true (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]) := by
        ext <;> simp [MixedPieces.qOffsetsEven,
          AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2]
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubEvenCopy.mem_evenTile_iff w _).1 hmem
  have hz1 := (mem_qCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curE w) (parentsAt w).even (SiteHullEven.curE_pos_lt w) hq 2 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, texV1Odd, texV2, Prod.fst_sub, Prod.snd_sub]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, ite_true]
    omega
  · rw [hmq]
    simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, ite_true]
    omega

theorem std_even_true_5 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = true) (z : Site)
    (hz : z ∈ shift (stateAt w).tEven (AltRotStep.shQ true (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    -2 * (SiteInduction.curE w).den ≤ (SiteInduction.curE w).den * z.2 - (SiteInduction.curE w).num * z.1 ∧ |z.1| ≤ 2 * (SiteInduction.curE w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 1 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    simpa using ho
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - (texV1Even (parentsAt w).even) ∈ evenTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).2, ho]
    refine mem_evenChildB_Q _ _ _ _ _ (AltRotStep.shQ true (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .dsQ1Minus - (texV1Even (parentsAt w).even)) (z - (texV1Even (parentsAt w).even)) ?_ ?_
    · have e : AltRotStep.shQ true (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 true (parentsAt w).odd (parentsAt w).even .dsQ1Minus - (texV1Even (parentsAt w).even) = (MixedPieces.qOffsetsEven true (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]) := by
        ext <;> simp [MixedPieces.qOffsetsEven,
          AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2] <;> ring
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubEvenCopy.mem_evenTile_iff w _).1 hmem
  have hz1 := (mem_qCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curE w) (parentsAt w).even (SiteHullEven.curE_pos_lt w) hq 2 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, texV1Even]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, ite_true, Prod.fst_add]
    omega
  · rw [hmq]
    simp only [SiteInduction.curE, Parents.current, Parents.combine, AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, ite_true, Prod.fst_add]
    omega

theorem std_odd_false_0 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (z : Site)
    (hz : z ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) :
    -2 * (SiteInduction.curO w).den ≤ (SiteInduction.curO w).den * z.2 - (SiteInduction.curO w).num * z.1 ∧ |z.1| ≤ 3 * (SiteInduction.curO w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 0 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    have : phase w ≠ 1 := fun h => by rw [h] at ho; simp at ho
    omega
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - (-texV1Even (parentsAt w).even) ∈ oddTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).1, ho]
    refine mem_oddChildB_P _ _ _ _ _ (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus - (-texV1Even (parentsAt w).even)) (z - (-texV1Even (parentsAt w).even)) ?_ ?_
    · have e : AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus - (-texV1Even (parentsAt w).even) = (MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]) := by
        ext <;> simp [MixedPieces.pOffsetsOdd,
          AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, Bool.false_eq_true]
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubOddCopy.mem_oddTile_iff w _).1 hmem
  have hz1 := (mem_pCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curO w) (parentsAt w).odd (SiteHullOdd.curO_pos_lt w) hp 3 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, texV1Even, Prod.fst_neg, Prod.snd_neg]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true]
    omega
  · rw [hmp]
    simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true]
    omega

theorem std_odd_false_1 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (z : Site)
    (hz : z ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) :
    -2 * (SiteInduction.curO w).den ≤ (SiteInduction.curO w).den * z.2 - (SiteInduction.curO w).num * z.1 ∧ |z.1| ≤ 3 * (SiteInduction.curO w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 0 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    have : phase w ≠ 1 := fun h => by rw [h] at ho; simp at ho
    omega
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - (texV2 (parentsAt w).odd) ∈ oddTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).1, ho]
    refine mem_oddChildB_P _ _ _ _ _ (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus - (texV2 (parentsAt w).odd)) (z - (texV2 (parentsAt w).odd)) ?_ ?_
    · have e : AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus - (texV2 (parentsAt w).odd) = (MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]) := by
        ext <;> simp [MixedPieces.pOffsetsOdd,
          AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, Bool.false_eq_true] <;> ring
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubOddCopy.mem_oddTile_iff w _).1 hmem
  have hz1 := (mem_pCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curO w) (parentsAt w).odd (SiteHullOdd.curO_pos_lt w) hp 3 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, texV2]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true, Prod.fst_add]
    omega
  · rw [hmp]
    simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true, Prod.fst_add]
    omega

theorem std_odd_false_2 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (z : Site)
    (hz : z ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) :
    -2 * (SiteInduction.curO w).den ≤ (SiteInduction.curO w).den * z.2 - (SiteInduction.curO w).num * z.1 ∧ |z.1| ≤ 3 * (SiteInduction.curO w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 0 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    have : phase w ≠ 1 := fun h => by rw [h] at ho; simp at ho
    omega
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - ((0 : Site)) ∈ oddTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).1, ho]
    refine mem_oddChildB_P _ _ _ _ _ (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus - ((0 : Site))) (z - ((0 : Site))) ?_ ?_
    · have e : AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus - ((0 : Site)) = (MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]) := by
        ext <;> simp [MixedPieces.pOffsetsOdd,
          AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, Bool.false_eq_true]
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubOddCopy.mem_oddTile_iff w _).1 hmem
  have hz1 := (mem_pCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curO w) (parentsAt w).odd (SiteHullOdd.curO_pos_lt w) hp 3 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, Prod.fst_zero, Prod.snd_zero]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true]
    omega
  · rw [hmp]
    simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true]
    omega

theorem std_odd_false_3 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (z : Site)
    (hz : z ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) :
    -2 * (SiteInduction.curO w).den ≤ (SiteInduction.curO w).den * z.2 - (SiteInduction.curO w).num * z.1 ∧ |z.1| ≤ 3 * (SiteInduction.curO w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 0 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    have : phase w ≠ 1 := fun h => by rw [h] at ho; simp at ho
    omega
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - (texV1Even (parentsAt w).even + texV2 (parentsAt w).odd) ∈ oddTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).1, ho]
    refine mem_oddChildB_P _ _ _ _ _ (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus - (texV1Even (parentsAt w).even + texV2 (parentsAt w).odd)) (z - (texV1Even (parentsAt w).even + texV2 (parentsAt w).odd)) ?_ ?_
    · have e : AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus - (texV1Even (parentsAt w).even + texV2 (parentsAt w).odd) = (MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]) := by
        ext <;> simp [MixedPieces.pOffsetsOdd,
          AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, Bool.false_eq_true]
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubOddCopy.mem_oddTile_iff w _).1 hmem
  have hz1 := (mem_pCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curO w) (parentsAt w).odd (SiteHullOdd.curO_pos_lt w) hp 3 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, texV1Even, texV2, Prod.fst_add, Prod.snd_add]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true, Prod.fst_add]
    omega
  · rw [hmp]
    simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true, Prod.fst_add]
    omega

theorem std_odd_false_4 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (z : Site)
    (hz : z ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus)) :
    -2 * (SiteInduction.curO w).den ≤ (SiteInduction.curO w).den * z.2 - (SiteInduction.curO w).num * z.1 ∧ |z.1| ≤ 3 * (SiteInduction.curO w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 0 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    have : phase w ≠ 1 := fun h => by rw [h] at ho; simp at ho
    omega
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - ((0 : Site)) ∈ oddTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).1, ho]
    refine mem_oddChildB_Q _ _ _ _ _ (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus - ((0 : Site))) (z - ((0 : Site))) ?_ ?_
    · have e : AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus - ((0 : Site)) = (MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]) := by
        ext <;> simp [MixedPieces.qOffsetsOdd,
          AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, Bool.false_eq_true, Prod.fst_zero, Prod.snd_zero]
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubOddCopy.mem_oddTile_iff w _).1 hmem
  have hz1 := (mem_qCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curO w) (parentsAt w).even (SiteHullOdd.curO_pos_lt w) hq 3 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, Prod.fst_zero, Prod.snd_zero]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true]
    omega
  · rw [hmq]
    simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true]
    omega

theorem std_odd_false_5 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (z : Site)
    (hz : z ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus)) :
    -2 * (SiteInduction.curO w).den ≤ (SiteInduction.curO w).den * z.2 - (SiteInduction.curO w).num * z.1 ∧ |z.1| ≤ 3 * (SiteInduction.curO w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 0 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    have : phase w ≠ 1 := fun h => by rw [h] at ho; simp at ho
    omega
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - (texV2 (parentsAt w).odd) ∈ oddTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).1, ho]
    refine mem_oddChildB_Q _ _ _ _ _ (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus - (texV2 (parentsAt w).odd)) (z - (texV2 (parentsAt w).odd)) ?_ ?_
    · have e : AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus - (texV2 (parentsAt w).odd) = (MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]) := by
        ext <;> simp [MixedPieces.qOffsetsOdd,
          AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, Bool.false_eq_true] <;> ring
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubOddCopy.mem_oddTile_iff w _).1 hmem
  have hz1 := (mem_qCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curO w) (parentsAt w).even (SiteHullOdd.curO_pos_lt w) hq 3 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, texV2]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true]
    omega
  · rw [hmq]
    simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true]
    omega

theorem std_odd_true_0 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = true) (z : Site)
    (hz : z ∈ shift (stateAt w).tOdd (AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .dsP1Plus)) :
    -2 * (SiteInduction.curO w).den ≤ (SiteInduction.curO w).den * z.2 - (SiteInduction.curO w).num * z.1 ∧ |z.1| ≤ 3 * (SiteInduction.curO w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 1 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    simpa using ho
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - ((0 : Site)) ∈ oddTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).1, ho]
    refine mem_oddChildB_P _ _ _ _ _ (AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .dsP1Plus - ((0 : Site))) (z - ((0 : Site))) ?_ ?_
    · have e : AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .dsP1Plus - ((0 : Site)) = (MixedPieces.pOffsetsOdd true (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]) := by
        ext <;> simp [MixedPieces.pOffsetsOdd,
          AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, Prod.fst_zero, Prod.snd_zero]
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubOddCopy.mem_oddTile_iff w _).1 hmem
  have hz1 := (mem_pCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curO w) (parentsAt w).odd (SiteHullOdd.curO_pos_lt w) hp 3 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, Prod.fst_zero, Prod.snd_zero]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, ite_true]
    omega
  · rw [hmp]
    simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, ite_true]
    omega

theorem std_odd_true_1 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = true) (z : Site)
    (hz : z ∈ shift (stateAt w).tOdd (AltRotStep.shP true (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .dsP1Plus)) :
    -2 * (SiteInduction.curO w).den ≤ (SiteInduction.curO w).den * z.2 - (SiteInduction.curO w).num * z.1 ∧ |z.1| ≤ 3 * (SiteInduction.curO w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 1 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    simpa using ho
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - (texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ oddTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).1, ho]
    refine mem_oddChildB_P _ _ _ _ _ (AltRotStep.shP true (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .dsP1Plus - (texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) (z - (texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) ?_ ?_
    · have e : AltRotStep.shP true (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .dsP1Plus - (texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) = (MixedPieces.pOffsetsOdd true (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]) := by
        ext <;> simp [MixedPieces.pOffsetsOdd,
          AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, Prod.fst_zero, Prod.snd_zero] <;> ring
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubOddCopy.mem_oddTile_iff w _).1 hmem
  have hz1 := (mem_pCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curO w) (parentsAt w).odd (SiteHullOdd.curO_pos_lt w) hp 3 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, texV1Even, texV2, Prod.fst_sub, Prod.snd_sub]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, ite_true, Prod.fst_add, Prod.fst_neg]
    omega
  · rw [hmp]
    simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, ite_true, Prod.fst_add, Prod.fst_neg]
    omega

theorem std_odd_true_2 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = true) (z : Site)
    (hz : z ∈ shift (stateAt w).tOdd (AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .dsP1Minus)) :
    -2 * (SiteInduction.curO w).den ≤ (SiteInduction.curO w).den * z.2 - (SiteInduction.curO w).num * z.1 ∧ |z.1| ≤ 3 * (SiteInduction.curO w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 1 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    simpa using ho
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - (-texV1Even (parentsAt w).even) ∈ oddTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).1, ho]
    refine mem_oddChildB_P _ _ _ _ _ (AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .dsP1Minus - (-texV1Even (parentsAt w).even)) (z - (-texV1Even (parentsAt w).even)) ?_ ?_
    · have e : AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .dsP1Minus - (-texV1Even (parentsAt w).even) = (MixedPieces.pOffsetsOdd true (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]) := by
        ext <;> simp [MixedPieces.pOffsetsOdd,
          AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2] <;> ring
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubOddCopy.mem_oddTile_iff w _).1 hmem
  have hz1 := (mem_pCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curO w) (parentsAt w).odd (SiteHullOdd.curO_pos_lt w) hp 3 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, texV1Even, Prod.fst_neg, Prod.snd_neg]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, ite_true]
    omega
  · rw [hmp]
    simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, ite_true]
    omega

theorem std_odd_true_3 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = true) (z : Site)
    (hz : z ∈ shift (stateAt w).tOdd (AltRotStep.shP true (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .dsP1Minus)) :
    -2 * (SiteInduction.curO w).den ≤ (SiteInduction.curO w).den * z.2 - (SiteInduction.curO w).num * z.1 ∧ |z.1| ≤ 3 * (SiteInduction.curO w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 1 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    simpa using ho
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - (texV2 (parentsAt w).odd + texV2 (parentsAt w).even) ∈ oddTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).1, ho]
    refine mem_oddChildB_P _ _ _ _ _ (AltRotStep.shP true (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .dsP1Minus - (texV2 (parentsAt w).odd + texV2 (parentsAt w).even)) (z - (texV2 (parentsAt w).odd + texV2 (parentsAt w).even)) ?_ ?_
    · have e : AltRotStep.shP true (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .dsP1Minus - (texV2 (parentsAt w).odd + texV2 (parentsAt w).even) = (MixedPieces.pOffsetsOdd true (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]) := by
        ext <;> simp [MixedPieces.pOffsetsOdd,
          AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, Prod.fst_zero, Prod.snd_zero] <;> ring
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubOddCopy.mem_oddTile_iff w _).1 hmem
  have hz1 := (mem_pCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curO w) (parentsAt w).odd (SiteHullOdd.curO_pos_lt w) hp 3 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, texV2, Prod.fst_add, Prod.snd_add]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, ite_true, Prod.fst_add, Prod.fst_neg]
    omega
  · rw [hmp]
    simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, ite_true, Prod.fst_add, Prod.fst_neg]
    omega

theorem std_odd_true_4 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = true) (z : Site)
    (hz : z ∈ shift (stateAt w).tEven (AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .q1Plus)) :
    -2 * (SiteInduction.curO w).den ≤ (SiteInduction.curO w).den * z.2 - (SiteInduction.curO w).num * z.1 ∧ |z.1| ≤ 3 * (SiteInduction.curO w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 1 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    simpa using ho
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - ((0 : Site)) ∈ oddTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).1, ho]
    refine mem_oddChildB_Q _ _ _ _ _ (AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .q1Plus - ((0 : Site))) (z - ((0 : Site))) ?_ ?_
    · have e : AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .q1Plus - ((0 : Site)) = (MixedPieces.qOffsetsOdd true (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]) := by
        ext <;> simp [MixedPieces.qOffsetsOdd,
          AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2]
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubOddCopy.mem_oddTile_iff w _).1 hmem
  have hz1 := (mem_qCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curO w) (parentsAt w).even (SiteHullOdd.curO_pos_lt w) hq 3 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, Prod.fst_zero, Prod.snd_zero]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, ite_true]
    omega
  · rw [hmq]
    simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, ite_true]
    omega

theorem std_odd_true_5 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = true) (z : Site)
    (hz : z ∈ shift (stateAt w).tEven (AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .q1Minus)) :
    -2 * (SiteInduction.curO w).den ≤ (SiteInduction.curO w).den * z.2 - (SiteInduction.curO w).num * z.1 ∧ |z.1| ≤ 3 * (SiteInduction.curO w).den := by
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hph : phase w = 1 := by
    have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
    simpa using ho
  rw [hph] at hdet
  norm_num at hdet
  have hmem : z - (texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) ∈ oddTile w := by
    rw [(HorizontalStep.tiles_nonbase w hw).1, ho]
    refine mem_oddChildB_Q _ _ _ _ _ (AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .q1Minus - (texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) (z - (texV2 (parentsAt w).odd - texV1Even (parentsAt w).even)) ?_ ?_
    · have e : AltRotStep.offP0 true (parentsAt w).odd (parentsAt w).even .q1Minus - (texV2 (parentsAt w).odd - texV1Even (parentsAt w).even) = (MixedPieces.qOffsetsOdd true (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]) := by
        ext <;> simp [MixedPieces.qOffsetsOdd,
          AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2] <;> ring
      rw [e]; exact List.getElem_mem _
    · rw [mem_shift] at hz ⊢
      convert hz using 1
      abel
  have hz2 := (SubOddCopy.mem_oddTile_iff w _).1 hmem
  have hz1 := (mem_qCopy_iff hw _ z).1 hz
  refine copy_bound (SiteInduction.curO w) (parentsAt w).even (SiteHullOdd.curO_pos_lt w) hq 3 _ _ z hz1 hz2 ?_ ?_ ?_
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, texV1Even, texV2, Prod.fst_sub, Prod.snd_sub]
    nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1,
      mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2),
      mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]
  · simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, ite_true]
    omega
  · rw [hmq]
    simp only [SiteInduction.curO, Parents.current, Parents.combine, AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, ite_true]
    omega

/-! ### The base alternate tiles -/

open FLatticePaper.Tiles.PaperAltBase in
theorem claim_stair (d : ℤ) (hd : 3 ≤ d) : Claim (stairAltF d) ⟨1, d⟩ 2 := by
  intro z hz
  simp only [stairAltF, boxF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hz
  obtain ⟨-, h⟩ := hz
  show -2 * d ≤ d * z.2 - 1 * z.1 ∧ |z.1| ≤ 2 * d
  rcases h with h | h | h | h | h | h <;>
    refine ⟨?_, abs_le.2 ⟨by omega, by omega⟩⟩ <;> nlinarith

open FLatticePaper.Tiles.PaperAltBase in
theorem claim_ladder (d : ℤ) (hd : 4 ≤ d) : Claim (shift (ladderAltF d) (1, 1)) ⟨1, d⟩ 3 := by
  intro z hz
  rw [mem_shift] at hz
  simp only [ladderAltF, boxF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.fst_sub, Prod.snd_sub] at hz
  obtain ⟨-, h, -⟩ := hz
  show -2 * d ≤ d * z.2 - 1 * z.1 ∧ |z.1| ≤ 3 * d
  rcases h with (h | h) | h | h
  · have h1 : z.1 = 0 ∧ z.2 = 0 := by
      have := congrArg Prod.fst h; have := congrArg Prod.snd h; simp only [Prod.fst_sub, Prod.snd_sub] at *; omega
    refine ⟨?_, abs_le.2 ⟨by omega, by omega⟩⟩
    rw [h1.1, h1.2]; nlinarith
  · have h1 : z.1 = d + 1 ∧ z.2 = d + 3 := by
      have := congrArg Prod.fst h; have := congrArg Prod.snd h; simp only [Prod.fst_sub, Prod.snd_sub] at *; omega
    refine ⟨?_, abs_le.2 ⟨by omega, by omega⟩⟩
    rw [h1.1, h1.2]; nlinarith
  · refine ⟨?_, abs_le.2 ⟨by omega, by omega⟩⟩; nlinarith
  · refine ⟨?_, abs_le.2 ⟨by omega, by omega⟩⟩; nlinarith

open FLatticePaper.Tiles.PaperAltBase in
theorem claim_nearStair (k : ℤ) (hk : 0 ≤ k) :
    Claim (shift (nearStairAltF (2 * k + 3)) (0, -1)) ⟨k + 1, k + 2⟩ 3 := by
  intro z hz
  rw [mem_shift] at hz
  simp only [nearStairAltF, boxF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.fst_sub, Prod.snd_sub]
    at hz
  obtain ⟨-, h⟩ := hz
  show -2 * (k + 2) ≤ (k + 2) * z.2 - (k + 1) * z.1 ∧ |z.1| ≤ 3 * (k + 2)
  rcases h with h | h | h | h | h | h <;>
    refine ⟨?_, abs_le.2 ⟨by omega, by omega⟩⟩ <;> nlinarith

open FLatticePaper.Tiles.PaperAltBase in
theorem claim_nearLadder (k : ℤ) (hk : 1 ≤ k) :
    Claim (shift (nearLadderAltF (2 * k + 2)) (0, -1)) ⟨2 * k + 1, 2 * k + 3⟩ 2 := by
  intro z hz
  rw [mem_shift] at hz
  simp only [nearLadderAltF, boxF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.fst_sub, Prod.snd_sub]
    at hz
  obtain ⟨-, h, -⟩ := hz
  show -2 * (2 * k + 3) ≤ (2 * k + 3) * z.2 - (2 * k + 1) * z.1 ∧ |z.1| ≤ 2 * (2 * k + 3)
  rcases h with (h | h) | h | h
  · have h1 : z.1 = -2 ∧ z.2 = 4 * k + 3 := by
      have := congrArg Prod.fst h; have := congrArg Prod.snd h; simp only [Prod.fst_sub, Prod.snd_sub] at *; omega
    refine ⟨?_, abs_le.2 ⟨by omega, by omega⟩⟩
    rw [h1.1, h1.2]; nlinarith
  · have h1 : z.1 = 2 * k + 3 ∧ z.2 = 2 * k := by
      have := congrArg Prod.fst h; have := congrArg Prod.snd h; simp only [Prod.fst_sub, Prod.snd_sub] at *; omega
    refine ⟨?_, abs_le.2 ⟨by omega, by omega⟩⟩
    rw [h1.1, h1.2]; nlinarith
  · refine ⟨?_, abs_le.2 ⟨by omega, by omega⟩⟩; nlinarith
  · refine ⟨?_, abs_le.2 ⟨by omega, by omega⟩⟩; nlinarith

/-! ### The claim on the base words -/

theorem curO_three (k : ℕ) : SiteInduction.curO (List.replicate k Digit.three) = ⟨1, 2 * (k : ℤ) + 2⟩ := by
  simp only [SiteInduction.curO, parentsAt_replicate_three, Parents.current, Parents.combine]
  congr 1; ring

theorem curE_three (k : ℕ) : SiteInduction.curE (List.replicate k Digit.three) = ⟨1, 2 * (k : ℤ) + 3⟩ := by
  simp only [SiteInduction.curE, parentsAt_replicate_three, Parents.current, Parents.combine]
  congr 1; ring

theorem curO_two (k : ℕ) : SiteInduction.curO (List.replicate k Digit.two) = ⟨(k : ℤ) + 1, (k : ℤ) + 2⟩ := by
  simp only [SiteInduction.curO, parentsAt_replicate_two, Parents.current, Parents.combine]
  congr 1 <;> ring

theorem curE_two (k : ℕ) : SiteInduction.curE (List.replicate k Digit.two) = ⟨2 * (k : ℤ) + 1, 2 * (k : ℤ) + 3⟩ := by
  simp only [SiteInduction.curE, parentsAt_replicate_two, Parents.current, Parents.combine]
  congr 1

/-- The claim on the base alternate tiles (`prop:base_cases`, the paper base). -/
theorem claim_base (w : Word) (hb : IsBase w) :
    Claim (altOddTile AltRotStep.B w) (SiteInduction.curO w) 3 ∧
      Claim (altEvenTile AltRotStep.B w) (SiteInduction.curE w) 2 := by
  rw [AltRotStep.altOddTile_of_base _ hb, AltRotStep.altEvenTile_of_base _ hb]
  by_cases h0 : w = []
  · subst h0
    rw [AltRotStep.B_nil]
    have e1 : SiteInduction.curO [] = ⟨0 + 1, 0 + 2⟩ := by decide
    have e2 : SiteInduction.curE [] = ⟨1, 3⟩ := by decide
    rw [e1, e2]
    exact ⟨by simpa using claim_nearStair 0 le_rfl, claim_stair 3 le_rfl⟩
  rcases hb with h | h | h
  · exact absurd h h0
  · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.three := ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, h⟩⟩
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at h0
      · exact hk
    rw [AltRotStep.B_three k hk, curO_three, curE_three]
    exact ⟨claim_ladder _ (by omega), claim_stair _ (by omega)⟩
  · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.two := ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, h⟩⟩
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at h0
      · exact hk
    rw [AltRotStep.B_two k hk, curO_two, curE_two]
    exact ⟨claim_nearStair _ (by omega), by
      have := claim_nearLadder (k : ℤ) (by exact_mod_cast hk)
      convert this using 3⟩

/-! ### The alternate parent piece -/

theorem phase_cases (w : Word) : (phase w == 1) = true ∧ phase w = 1 ∨ (phase w == 1) = false ∧ phase w = 0 := by
  have h2 : phase w < 2 := Nat.mod_lt _ (by norm_num)
  rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h | h
  · right; have : phase w = 0 := by omega
    exact ⟨by simp [this], this⟩
  · left; exact ⟨by simp [h], h⟩

/-- The claim on the alternate parent piece `T̂(p₁) + h` of `T̂(q₀)`. -/
theorem parent_even {w : Word} (hw : ¬ IsBase w) (x : Digit) (S : Tile) (hS : Claim S (parentsAt w).odd 3)
    (hx1 : x = Digit.one → (parentsAt w).odd.den ≤ (parentsAt w).even.den) (z : Site)
    (hz : z ∈ AltRotStep.altP1Part (phase w == 1) x S (parentsAt w).odd (parentsAt w).even) :
    -2 * (SiteInduction.curE w).den ≤ (SiteInduction.curE w).den * z.2 - (SiteInduction.curE w).num * z.1 ∧ |z.1| ≤ 2 * (SiteInduction.curE w).den := by
  obtain ⟨hp, hq, -, -⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hpos := SiteHullEven.curE_pos_lt w
  have hden : 0 < (parentsAt w).odd.den := by omega
  have hdet' : (SiteInduction.curE w).den * (parentsAt w).odd.num - (parentsAt w).odd.den * (SiteInduction.curE w).num =
      ((parentsAt w).odd.num * (parentsAt w).even.den - (parentsAt w).even.num * (parentsAt w).odd.den) := by
    simp only [SiteInduction.curE, Parents.current, Parents.combine]; ring
  have hd1 : (SiteInduction.curE w).den * (parentsAt w).odd.num - (parentsAt w).odd.den * (SiteInduction.curE w).num = 1 ∨
      (SiteInduction.curE w).den * (parentsAt w).odd.num - (parentsAt w).odd.den * (SiteInduction.curE w).num = -1 := by
    rw [hdet', hdet]; split_ifs <;> simp
  rcases phase_cases w with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;> rw [hph] at hdet <;> norm_num at hdet <;> rw [ho] at hz <;>
    cases x <;> simp only [AltRotStep.altP1Part, SurgicalAlt.altP1Coeff, if_true, if_false, Bool.false_eq_true,
      reduceCtorEq] at hz
  all_goals try exact absurd hz (by simp)
  all_goals
    try have hx := hx1 rfl
    rw [mem_shift] at hz
    refine parent_bound (SiteInduction.curE w) (parentsAt w).odd (by omega) hden 3 2 hd1 S hS _ z hz ?_ ?_ ?_ <;>
      simp only [SiteInduction.curE, Parents.current, Parents.combine, SurgicalAlt.coeffOff, texV1Odd, texV1Even, texV2] <;>
      first
      | omega
      | nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1, mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2), mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]

/-- The claim on the alternate parent piece `T̂(q₁) + h` of `T̂(p₀)`. -/
theorem parent_odd {w : Word} (hw : ¬ IsBase w) (x : Digit) (S : Tile) (hS : Claim S (parentsAt w).even 2) (z : Site)
    (hz : z ∈ AltRotStep.altQ1Part (phase w == 1) x S (parentsAt w).odd (parentsAt w).even) :
    -2 * (SiteInduction.curO w).den ≤ (SiteInduction.curO w).den * z.2 - (SiteInduction.curO w).num * z.1 ∧ |z.1| ≤ 3 * (SiteInduction.curO w).den := by
  obtain ⟨hp, hq, -, -⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  have hpos := SiteHullOdd.curO_pos_lt w
  have hden : 0 < (parentsAt w).even.den := by omega
  have hdet' : (SiteInduction.curO w).den * (parentsAt w).even.num - (parentsAt w).even.den * (SiteInduction.curO w).num =
      -((parentsAt w).odd.num * (parentsAt w).even.den - (parentsAt w).even.num * (parentsAt w).odd.den) := by
    simp only [SiteInduction.curO, Parents.current, Parents.combine]; ring
  have hd1 : (SiteInduction.curO w).den * (parentsAt w).even.num - (parentsAt w).even.den * (SiteInduction.curO w).num = 1 ∨
      (SiteInduction.curO w).den * (parentsAt w).even.num - (parentsAt w).even.den * (SiteInduction.curO w).num = -1 := by
    rw [hdet', hdet]; split_ifs <;> simp
  rcases phase_cases w with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;> rw [hph] at hdet <;> norm_num at hdet <;> rw [ho] at hz <;>
    cases x <;> simp only [AltRotStep.altQ1Part, SurgicalAlt.altQ1Coeff, if_true, if_false, Bool.false_eq_true,
      reduceCtorEq] at hz
  all_goals try exact absurd hz (by simp)
  all_goals
    rw [mem_shift] at hz
    refine parent_bound (SiteInduction.curO w) (parentsAt w).even (by omega) hden 2 3 hd1 S hS _ z hz ?_ ?_ ?_ <;>
      simp only [SiteInduction.curO, Parents.current, Parents.combine, SurgicalAlt.coeffOff, texV1Odd, texV1Even, texV2] <;>
      first
      | omega
      | nlinarith [mul_pos hp.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hq.2), mul_pos (sub_pos.2 hp.2) hq.1, mul_pos hp.1 (sub_pos.2 hq.2), mul_pos hp.1 hp.1, mul_pos hq.1 hq.1, mul_pos (sub_pos.2 hp.2) (sub_pos.2 hp.2), mul_pos (sub_pos.2 hq.2) (sub_pos.2 hq.2)]

/-! ### The claim for every word -/

theorem altRegs_one (u : Word) : (SurgicalAltTiles.altRegs AltRotStep.B (u ++ [Digit.one])).1 = altOddTile AltRotStep.B u ∧
    (SurgicalAltTiles.altRegs AltRotStep.B (u ++ [Digit.one])).2 = altEvenTile AltRotStep.B u := by
  rw [AltRotStep.altRegs_snoc]; exact ⟨rfl, rfl⟩

theorem altRegs_two (u : Word) :
    (SurgicalAltTiles.altRegs AltRotStep.B (u ++ [Digit.two])).1 = altOddTile AltRotStep.B u := by
  rw [AltRotStep.altRegs_snoc]; rfl

theorem altRegs_three (u : Word) :
    (SurgicalAltTiles.altRegs AltRotStep.B (u ++ [Digit.three])).2 = altEvenTile AltRotStep.B u := by
  rw [AltRotStep.altRegs_snoc]; rfl

/-- The claim on `T̂(q₀)` of a non-base word, given the claim on its alternate parent. -/
theorem claim_even_step {w : Word} (hw : ¬ IsBase w)
    (hreg : ∀ x, altTypeOf w = some x → x ≠ Digit.three →
      Claim (SurgicalAltTiles.altRegs AltRotStep.B w).1 (parentsAt w).odd 3)
    (hd : altTypeOf w = some Digit.one → (parentsAt w).odd.den ≤ (parentsAt w).even.den) :
    Claim (altEvenTile AltRotStep.B w) (SiteInduction.curE w) 2 := by
  obtain ⟨x, hx, he⟩ := altEvenTile_eq AltRotStep.B hw
  intro z hz
  rw [he, Finset.mem_union] at hz
  rcases hz with hz | hz
  · rw [mem_evenStd_iff] at hz
    rcases phase_cases w with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;> rw [ho] at hz
    · rcases hz with ⟨a, ha, hz⟩ | ⟨b, hb, hz⟩
      · simp only [evenPOffs, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact std_even_true_0 hw ho z hz
        · exact std_even_true_1 hw ho z hz
      · simp only [evenQOffs, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl
        · exact std_even_true_2 hw ho z hz
        · exact std_even_true_3 hw ho z hz
        · exact std_even_true_4 hw ho z hz
        · exact std_even_true_5 hw ho z hz
    · rcases hz with ⟨a, ha, hz⟩ | ⟨b, hb, hz⟩
      · simp only [evenPOffs, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact std_even_false_0 hw ho z hz
        · exact std_even_false_1 hw ho z hz
      · simp only [evenQOffs, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl
        · exact std_even_false_2 hw ho z hz
        · exact std_even_false_3 hw ho z hz
        · exact std_even_false_4 hw ho z hz
        · exact std_even_false_5 hw ho z hz
  · by_cases h3 : x = Digit.three
    · subst h3
      rcases phase_cases w with ⟨ho, -⟩ | ⟨ho, -⟩ <;> rw [ho] at hz <;>
        simp [AltRotStep.altP1Part, SurgicalAlt.altP1Coeff] at hz
    · exact parent_even hw x _ (hreg x hx h3) (fun h1 => hd (h1 ▸ hx)) z hz

/-- The claim on `T̂(p₀)` of a non-base word, given the claim on its alternate parent. -/
theorem claim_odd_step {w : Word} (hw : ¬ IsBase w)
    (hreg : ∀ x, altTypeOf w = some x → x ≠ Digit.two →
      Claim (SurgicalAltTiles.altRegs AltRotStep.B w).2 (parentsAt w).even 2) :
    Claim (altOddTile AltRotStep.B w) (SiteInduction.curO w) 3 := by
  obtain ⟨x, hx, he⟩ := altOddTile_eq AltRotStep.B hw
  intro z hz
  rw [he, Finset.mem_union] at hz
  rcases hz with hz | hz
  · rw [mem_oddStd_iff] at hz
    rcases phase_cases w with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;> rw [ho] at hz
    · rcases hz with ⟨a, ha, hz⟩ | ⟨b, hb, hz⟩
      · simp only [oddPOffs, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl
        · exact std_odd_true_0 hw ho z hz
        · exact std_odd_true_1 hw ho z hz
        · exact std_odd_true_2 hw ho z hz
        · exact std_odd_true_3 hw ho z hz
      · simp only [oddQOffs, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact std_odd_true_4 hw ho z hz
        · exact std_odd_true_5 hw ho z hz
    · rcases hz with ⟨a, ha, hz⟩ | ⟨b, hb, hz⟩
      · simp only [oddPOffs, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl
        · exact std_odd_false_0 hw ho z hz
        · exact std_odd_false_1 hw ho z hz
        · exact std_odd_false_2 hw ho z hz
        · exact std_odd_false_3 hw ho z hz
      · simp only [oddQOffs, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact std_odd_false_4 hw ho z hz
        · exact std_odd_false_5 hw ho z hz
  · by_cases h2 : x = Digit.two
    · subst h2
      rcases phase_cases w with ⟨ho, -⟩ | ⟨ho, -⟩ <;> rw [ho] at hz <;>
        simp [AltRotStep.altQ1Part, SurgicalAlt.altQ1Coeff] at hz
    · exact parent_odd hw x _ (hreg x hx h2) z hz

/-- **The claim of the text for every alternate tile** (the paper base): `L_t ≥ -2 d_t` and `|z₁| ≤ m_t d_t` on `T̂(t)`,
`m_t = 3` for the odd child and `2` for the even child. -/
theorem claim_all (w : Word) :
    Claim (altOddTile AltRotStep.B w) (SiteInduction.curO w) 3 ∧
      Claim (altEvenTile AltRotStep.B w) (SiteInduction.curE w) 2 := by
  induction w using List.reverseRecOn with
  | nil => exact claim_base [] (Or.inl rfl)
  | append_singleton u x ih =>
    by_cases hb : IsBase (u ++ [x])
    · exact claim_base _ hb
    · have ht : altTypeOf (u ++ [x]) = some x := AltRotStep.altTypeOf_snoc u x
      refine ⟨claim_odd_step hb ?_, claim_even_step hb ?_ ?_⟩
      · intro y hy hy2
        rw [ht] at hy
        obtain rfl := Option.some.inj hy
        cases x with
        | one => rw [(altRegs_one u).2, (HorizontalStep.par_one u).2]; exact ih.2
        | two => exact absurd rfl hy2
        | three => rw [altRegs_three, (HorizontalStep.par_three u).2]; exact ih.2
      · intro y hy hy3
        rw [ht] at hy
        obtain rfl := Option.some.inj hy
        cases x with
        | one => rw [(altRegs_one u).1, (HorizontalStep.par_one u).1]; exact ih.1
        | two => rw [altRegs_two, (HorizontalStep.par_two u).1]; exact ih.1
        | three => exact absurd rfl hy3
      · intro h1
        rw [ht] at h1
        obtain rfl := Option.some.inj h1
        rw [(HorizontalStep.par_one u).1, (HorizontalStep.par_one u).2]
        have hv := (parentsAt_valid u).odd_bounds
        simp only [Parents.current, Parents.combine]
        obtain ⟨h1', -, -⟩ := hv
        omega

end FLatticePaper.Tiles.AltBounds
