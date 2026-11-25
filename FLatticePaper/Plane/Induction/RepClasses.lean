import FLatticePaper.Plane.Induction.FreeVClass
import FLatticePaper.Plane.Induction.Sec3Shift
import FLatticePaper.Plane.Induction.SheetStars
import FLatticePaper.Plane.Induction.BaseMembership
import FLatticePaper.Plane.Induction.CollarTop
import FLatticePaper.Plane.Induction.VArcLongitudinal
import FLatticePaper.Plane.Induction.FreePolicy
import FLatticePaper.Plane.Induction.Q3VStar
import FLatticePaper.Plane.Induction.SheetOffsets
import FLatticePaper.Plane.Induction.MatchedPolicy

/-! The representatives of the native points in the conjugate field, in parent coordinates (`N = odd.num`, `D = odd.den`).

The conjugate child has `num = D − N`, `den = D + N`, so its kernel is `U_c = (D+N, D−N)` and its transverse is `V_c = (−2N, 2D)`,
and its centre is `(D − N + 1, 3D − N − 1)`. The shift `Y = X − sheetShift` is `U_p = (2D, 2N)` at ε = +1 and `0` at ε = −1. -/

namespace FLatticePaper.RepClasses

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.Sec3Shift FLatticePaper.W1MSheet

/-- The kernel of the conjugate deck. -/
theorem conj_kernel {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    (frameAt (conjWord word)).child.modifiedDeck.kernel =
      ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num,
        (frameAt word).parents.odd.den - (frameAt word).parents.odd.num) := by
  obtain ⟨hcn, hcd⟩ := FLatticePaper.Induction.frameAt_conj_num_den h
  rw [ChildFrame.kernel_coords, hcn, hcd]

/-- The transverse of the conjugate deck. -/
theorem conj_transverse {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    (frameAt (conjWord word)).child.modifiedDeck.transverse =
      (-2 * (frameAt word).parents.odd.num, 2 * (frameAt word).parents.odd.den) := by
  obtain ⟨hcn, hcd⟩ := FLatticePaper.Induction.frameAt_conj_num_den h
  show ((frameAt (conjWord word)).child.num - (frameAt (conjWord word)).child.den,
      (frameAt (conjWord word)).child.num + (frameAt (conjWord word)).child.den) = _
  rw [hcn, hcd]
  ext <;> simp <;> ring

/-- The centre of the conjugate frame. -/
theorem conj_centre {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    (frameAt (conjWord word)).centre =
      ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num + 1,
        2 * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) +
          ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) - 1) := by
  obtain ⟨hcn, hcd⟩ := FLatticePaper.Induction.frameAt_conj_num_den h
  rw [ChildFrame.centre_coords, hcn, hcd]

/-- The shift `Y = X − sheetShift`: `U_p` at ε = +1 and `0` at ε = −1. -/
theorem Y_eq {word : Word} :
    sec3X word - (frameAt word).sheetShift =
      (if (frameAt word).eps = 1 then (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num)
        else (0, 0)) := by
  rcases ChildFrame.eps_unit (frameAt word) with he | he
  · have hs : (frameAt word).sheetShift = 0 := by
      unfold ChildFrame.sheetShift
      rw [SheetOffsets.phaseW_pos he]
      simp
    simp [sec3X, he, hs, Upar]
  · have hs : (frameAt word).sheetShift = (frameAt word).parents.even.unmodifiedDeck.kernel := by
      unfold ChildFrame.sheetShift
      rw [SheetOffsets.phaseW_neg he]
      simp
    simp [sec3X, he, hs]
    rfl

/-- The parent-coordinate expansion of a point `w = b + k·V_p`. -/
theorem coords_of_vp {word : Word} {w b : Site} {k : ℤ}
    (hw : w = b + k • TipVertex.tipVertex (frameAt word)) :
    w.1 = b.1 + k * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den) ∧
      w.2 = b.2 + k * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) := by
  subst hw
  constructor <;> simp [TipVertex.tipVertex]

/-- The generic class: `z = U_c + Z(b)` is a free H site of the conjugate, `zTurn(w+Y) − z` is in its span, and the image step
is the prescribed H step of `z`. -/
theorem rep_generic {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {w b : Site} {k : ℤ}
    (hb : b ∈ (frameAt word).freeV) (hb0 : 0 ≤ b.2)
    (hbL : b.2 < (frameAt word).parents.odd.den + (frameAt word).parents.odd.num)
    (hw : w = b + k • TipVertex.tipVertex (frameAt word))
    (hnt : ¬ ((frameAt word).eps = 1 ∧ b.2 = (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1)) :
    ((frameAt (conjWord word)).child.modifiedDeck.kernel +
        zTurn b ∈ (frameAt (conjWord word)).freeH) ∧
    (zTurn (w + (sec3X word - (frameAt word).sheetShift)) -
        ((frameAt (conjWord word)).child.modifiedDeck.kernel + zTurn b) ∈
          (frameAt (conjWord word)).child.modifiedDeck.span) ∧
    (zTurn (w + (frameAt word).prescribedV 1 w + (sec3X word - (frameAt word).sheetShift)) -
        zTurn (w + (sec3X word - (frameAt word).sheetShift)) =
      (frameAt (conjWord word)).prescribedH (frameAt word).eps
        ((frameAt (conjWord word)).child.modifiedDeck.kernel + zTurn b)) := by
  obtain ⟨hw1, hw2⟩ := coords_of_vp hw
  have hK := conj_kernel h
  have hT := conj_transverse h
  have hC := conj_centre h
  obtain ⟨hpN, hpD, hpd2, -, -, -, -, -, -⟩ := PriceInputs.pdata h
  have hLpos : 0 < (frameAt word).parents.odd.den + (frameAt word).parents.odd.num := by omega
  have hph : (frameAt word).eps = -1 ∨ b.2 ≤ (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 2 := by
    rcases ChildFrame.eps_unit (frameAt word) with he | he
    · right
      have := hnt
      omega
    · left; exact he
  have hmem : (frameAt (conjWord word)).child.modifiedDeck.kernel + zTurn b ∈ (frameAt (conjWord word)).freeH := by
    have hb' := BaseMembership.base_mem_freeH h hb hb0 (by omega) hph
    have hr := CollarTop.freeH_reflect (frameAt (conjWord word)) hb'
    have e : (frameAt (conjWord word)).child.modifiedDeck.kernel + zTurn b =
        (frameAt (conjWord word)).centre -
          ((1 + b.2, -b.1) + (frameAt (conjWord word)).child.modifiedDeck.transverse) := by
      rw [hK, hC, hT]
      ext <;> simp [zTurn] <;> ring
    rw [e]
    exact hr
  have hspan : zTurn (w + (sec3X word - (frameAt word).sheetShift)) -
        ((frameAt (conjWord word)).child.modifiedDeck.kernel + zTurn b) ∈
          (frameAt (conjWord word)).child.modifiedDeck.span := by
    rcases ChildFrame.eps_unit (frameAt word) with he | he
    · have hY := Y_eq (word := word)
      rw [if_pos he] at hY
      refine ⟨-(k+1), 1, ?_⟩
      rw [hY, Farey.PeriodDeck.combine, hK, hT]
      ext <;> simp [zTurn, hw1, hw2] <;> ring
    · have hY := Y_eq (word := word)
      rw [if_neg (by rw [he]; norm_num)] at hY
      refine ⟨-(k+1), 0, ?_⟩
      rw [hY, Farey.PeriodDeck.combine, hK, hT]
      ext <;> simp [zTurn, hw1, hw2] <;> ring
  refine ⟨hmem, hspan, ?_⟩
  have hgen : ∀ p : Site, zTurn (w + p + (sec3X word - (frameAt word).sheetShift)) -
      zTurn (w + (sec3X word - (frameAt word).sheetShift)) = (-p.2, p.1) := by
    intro p
    ext <;> simp [zTurn]
  rw [hgen]
  have hwpar : w.1 + w.2 = (b.1 + b.2) + 2 * (k * (frameAt word).parents.odd.num) := by
    rw [hw1, hw2]; ring
  generalize k * (frameAt word).parents.odd.num = t at hwpar
  have hK' := hK
  by_cases hwe : EvenSite w
  · have hz0o : ¬ EvenSite ((frameAt (conjWord word)).child.modifiedDeck.kernel + zTurn b) := by
      rw [hK]
      unfold EvenSite at hwe ⊢
      simp only [zTurn, Prod.fst_add, Prod.snd_add]
      omega
    rw [SheetStars.prescribedV_even_one (frameAt word) hwe]
    unfold ChildFrame.prescribedH
    split_ifs with h1 h2
    · rw [hK] at h1
      have c1 := congrArg Prod.fst h1
      have c2 := congrArg Prod.snd h1
      simp [zTurn, hFirst] at c1 c2
      have hb2 : b.2 = (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1 := by omega
      have he : (frameAt word).eps = -1 := by
        rcases ChildFrame.eps_unit (frameAt word) with he | he
        · exact absurd ⟨he, hb2⟩ hnt
        · exact he
      rw [he]
      simp
    · simp
    · simp
  · have hz0e : EvenSite ((frameAt (conjWord word)).child.modifiedDeck.kernel + zTurn b) := by
      rw [hK]
      unfold EvenSite at hwe ⊢
      simp only [zTurn, Prod.fst_add, Prod.snd_add]
      omega
    rw [SheetStars.prescribedV_odd_one (frameAt word) hwe]
    unfold ChildFrame.prescribedH
    split_ifs with h1 h2
    · rw [h1] at hz0e
      unfold EvenSite hFirst at hz0e
      norm_num at hz0e
    · rw [h2] at hz0e
      obtain ⟨hcn, hcd⟩ := FLatticePaper.Induction.frameAt_conj_num_den h
      unfold EvenSite ChildFrame.hLast at hz0e
      rw [hcn, hcd] at hz0e
      simp only at hz0e
      omega
    · simp

/-- The H_0 class `w = (1,0) + k·V_p` (odd): the representative `(0,0)` is a free V site of the conjugate, `zTurn(w+Y) − (0,0)` is in the
span, and the image step is the prescribed V step of `(0,0)`. -/
theorem rep_H0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {w : Site} {k : ℤ}
    (hw : w = (1, 0) + k • TipVertex.tipVertex (frameAt word)) :
    ((0 : ℤ), (0 : ℤ)) ∈ (frameAt (conjWord word)).freeV ∧
    zTurn (w + (sec3X word - (frameAt word).sheetShift)) - ((0 : ℤ), (0 : ℤ)) ∈
      (frameAt (conjWord word)).child.modifiedDeck.span ∧
    zTurn (w + (frameAt word).prescribedV 1 w + (sec3X word - (frameAt word).sheetShift)) -
        zTurn (w + (sec3X word - (frameAt word).sheetShift)) =
      (frameAt (conjWord word)).prescribedV (frameAt word).eps ((0 : ℤ), (0 : ℤ)) := by
  have hK := conj_kernel h
  have hT := conj_transverse h
  have hmem := origin_mem_freeV (frameAt (conjWord word))
  have hw' : w.1 = 1 + k * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den) ∧
      w.2 = k * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) := by
    subst hw
    constructor <;> simp [TipVertex.tipVertex]
  obtain ⟨hw1, hw2⟩ := hw'
  have hwo : ¬ EvenSite w := by
    have hpar : w.1 + w.2 = 1 + 2 * (k * (frameAt word).parents.odd.num) := by rw [hw1, hw2]; ring
    generalize k * (frameAt word).parents.odd.num = t at hpar
    unfold EvenSite
    omega
  refine ⟨hmem, ?_, ?_⟩
  · rcases ChildFrame.eps_unit (frameAt word) with he | he
    · have hY := Y_eq (word := word)
      rw [if_pos he] at hY
      refine ⟨-k, 1, ?_⟩
      rw [hY, Farey.PeriodDeck.combine, hK, hT]
      refine Prod.ext ?_ ?_
      · simp only [zTurn, hw1, hw2, Prod.fst_add, Prod.snd_add, Prod.fst_sub]
        ring
      · simp only [zTurn, hw1, hw2, Prod.fst_add, Prod.snd_add, Prod.snd_sub]
        ring
    · have hY := Y_eq (word := word)
      rw [if_neg (by rw [he]; norm_num)] at hY
      refine ⟨-k, 0, ?_⟩
      rw [hY, Farey.PeriodDeck.combine, hK, hT]
      refine Prod.ext ?_ ?_
      · simp only [zTurn, hw1, hw2, Prod.fst_add, Prod.snd_add, Prod.fst_sub]
        ring
      · simp only [zTurn, hw1, hw2, Prod.fst_add, Prod.snd_add, Prod.snd_sub]
        ring
  · rw [SheetStars.prescribedV_odd_one (frameAt word) hwo]
    have hgen : zTurn (w + (0, -1) + (sec3X word - (frameAt word).sheetShift)) -
        zTurn (w + (sec3X word - (frameAt word).sheetShift)) = (1, 0) := by
      ext <;> simp [zTurn]
    rw [hgen]
    have hvF : (frameAt (conjWord word)).prescribedV (frameAt word).eps ((0 : ℤ), (0 : ℤ)) = (1, 0) := by
      rw [show ((0 : ℤ), (0 : ℤ)) = vFirst from rfl]
      exact ChildFrame.prescribedV_vFirst (frameAt (conjWord word)) _
    rw [hvF]

/-- The phase-one top class: for the top base `b` of ordinate `L' − 1` (ε = +1), `b = (N−D, L'−1)`, and the representative
`v_Last,c` of the conjugate is a free V site with `zTurn(w+Y) − v_Last,c = −(k+1)·U_c` and the step `(1,0)`. -/
theorem rep_top {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {b w : Site} {k : ℤ}
    (hε : (frameAt word).eps = 1) (hb : b ∈ (frameAt word).freeV)
    (hbj : b.2 = (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1)
    (hbne : b ≠ (frameAt word).vLast)
    (hw : w = b + k • TipVertex.tipVertex (frameAt word)) :
    (frameAt (conjWord word)).vLast ∈ (frameAt (conjWord word)).freeV ∧
    zTurn (w + (sec3X word - (frameAt word).sheetShift)) - (frameAt (conjWord word)).vLast ∈
      (frameAt (conjWord word)).child.modifiedDeck.span ∧
    zTurn (w + (frameAt word).prescribedV 1 w + (sec3X word - (frameAt word).sheetShift)) -
        zTurn (w + (sec3X word - (frameAt word).sheetShift)) =
      (frameAt (conjWord word)).prescribedV (frameAt word).eps (frameAt (conjWord word)).vLast := by
  have hK := conj_kernel h
  have hT := conj_transverse h
  obtain ⟨hcn, hcd⟩ := FLatticePaper.Induction.frameAt_conj_num_den h
  obtain ⟨hN1, hND, hD2, -, -, -, -, -, -⟩ := PriceInputs.pdata h
  have hLpos : 0 < (frameAt word).parents.odd.den + (frameAt word).parents.odd.num := by omega
  have hN : 0 < (frameAt word).parents.odd.num := by omega
  have hcut := CutOnePerProper.cutOnePerOrdinate_of_proper h
  have hpg := LiftPsi.phase1_top (frameAt word) hN hcut hε hb hbne hbj
  unfold NativeGrade.pg at hpg
  rw [hbj] at hpg
  have hb1 : b.1 = (frameAt word).parents.odd.num - (frameAt word).parents.odd.den := by
    have h0 : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) *
        (b.1 - ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den)) = 0 := by
      linear_combination hpg
    rcases mul_eq_zero.mp h0 with h1 | h1
    · omega
    · linarith
  obtain ⟨hw1, hw2⟩ := coords_of_vp hw
  have hw1' : w.1 = ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den) * (k + 1) := by
    rw [hw1, hb1]; ring
  have hw2' : w.2 = ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * k +
      ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1) := by
    rw [hw2, hbj]; ring
  have hvL : (frameAt (conjWord word)).vLast =
      (-2 * (frameAt word).parents.odd.num + 1, 2 * (frameAt word).parents.odd.den - 1) := by
    unfold ChildFrame.vLast
    rw [hcn, hcd]
    ext <;> simp <;> ring
  refine ⟨FreeVOrdinate.vLast_mem_freeV (frameAt (conjWord word)), ?_, ?_⟩
  · have hY := Y_eq (word := word)
    rw [if_pos hε] at hY
    refine ⟨-(k+1), 0, ?_⟩
    rw [hY, Farey.PeriodDeck.combine, hK, hT, hvL]
    refine Prod.ext ?_ ?_
    · simp only [zTurn, hw1', hw2', Prod.fst_add, Prod.snd_add, Prod.fst_sub]
      ring
    · simp only [zTurn, hw1', hw2', Prod.fst_add, Prod.snd_add, Prod.snd_sub]
      ring
  · have hwo : ¬ EvenSite w := by
      have hpar : w.1 + w.2 = 2 * ((frameAt word).parents.odd.num * (k + 1)) - 1 := by
        rw [hw1', hw2']; ring
      unfold EvenSite
      generalize (frameAt word).parents.odd.num * (k + 1) = t at hpar
      omega
    rw [SheetStars.prescribedV_odd_one (frameAt word) hwo]
    have hgen : zTurn (w + (0, -1) + (sec3X word - (frameAt word).sheetShift)) -
        zTurn (w + (sec3X word - (frameAt word).sheetShift)) = (1, 0) := by
      ext <;> simp [zTurn]
    rw [hgen]
    have hne : (frameAt (conjWord word)).vLast ≠ vFirst := by
      rw [hvL]
      intro e
      have e2 := congrArg Prod.snd e
      simp [vFirst] at e2
      omega
    have hvP : (frameAt (conjWord word)).prescribedV (frameAt word).eps (frameAt (conjWord word)).vLast = (1, 0) := by
      unfold ChildFrame.prescribedV
      rw [if_neg hne, if_pos rfl, hε]
    rw [hvP]

/-- **The representatives.** For a free V white `w ≠ V_end`, the native image `zTurn(w + X − lv)` and its image step are represented by
a free H site (generic class) or a free V site (H_0 class and phase-one top class) of the conjugate, with the step the prescribed step
of that site. -/
theorem rep_exists {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {w : Site}
    (hw : w ∈ (frameAt word).freeV) (hne : w ≠ (frameAt word).vLast) :
    (∃ z ∈ (frameAt (conjWord word)).freeH,
        zTurn (w + (sec3X word - (frameAt word).sheetShift)) - z ∈ (frameAt (conjWord word)).child.modifiedDeck.span ∧
        zTurn (w + (frameAt word).prescribedV 1 w + (sec3X word - (frameAt word).sheetShift)) -
            zTurn (w + (sec3X word - (frameAt word).sheetShift)) = (frameAt (conjWord word)).prescribedH (frameAt word).eps z) ∨
    (∃ z ∈ (frameAt (conjWord word)).freeV,
        zTurn (w + (sec3X word - (frameAt word).sheetShift)) - z ∈ (frameAt (conjWord word)).child.modifiedDeck.span ∧
        zTurn (w + (frameAt word).prescribedV 1 w + (sec3X word - (frameAt word).sheetShift)) -
            zTurn (w + (sec3X word - (frameAt word).sheetShift)) = (frameAt (conjWord word)).prescribedV (frameAt word).eps z) := by
  obtain ⟨hN1, hND, hD2, hn0, hd0, hn, hd, -, -⟩ := PriceInputs.pdata h
  rcases FreeVClass.freeV_class h hw hne with ⟨b, hb, hb0, hbL, -, -, hwb⟩ | ⟨-, hwH0⟩
  · by_cases hT : (frameAt word).eps = 1 ∧ b.2 = (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1
    · have hbne : b ≠ (frameAt word).vLast := by
        intro e
        have := NativeGrade.ne_vLast_of_ordinate (frameAt word) (z := b) (by omega)
        exact this e
      obtain ⟨-, hsp, hst⟩ := rep_top h hT.1 hb hT.2 hbne hwb
      exact Or.inr ⟨(frameAt (conjWord word)).vLast, (rep_top h hT.1 hb hT.2 hbne hwb).1, hsp, hst⟩
    · obtain ⟨hmem, hsp, hst⟩ := rep_generic h hb hb0 hbL hwb hT
      exact Or.inl ⟨_, hmem, hsp, hst⟩
  · obtain ⟨hmem, hsp, hst⟩ := rep_H0 h hwH0
    exact Or.inr ⟨((0 : ℤ), (0 : ℤ)), hmem, hsp, hst⟩

end FLatticePaper.RepClasses
