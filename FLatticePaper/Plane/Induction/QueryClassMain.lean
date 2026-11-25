import FLatticePaper.Plane.Induction.QueryClassFrame
import FLatticePaper.Plane.Induction.NativeGrade
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.FreeTraceBox
import FLatticePaper.Plane.Induction.ParentGradeKernel
import FLatticePaper.Plane.Induction.QueryGrade
import FLatticePaper.Plane.Induction.CollarTop
import FLatticePaper.Plane.Induction.ArcPsi

/-! Task w3, step 1(b): the transport classification of every free H query (the named 1(b) of `PsiArc`).

For `w` in the free H cut of the word, the query is `z = Z (w − sheetShift)`. Either `z = vAt base z.2`, the free V cut of the
conjugate (its representative is `Z x − m V'`), or `z = (1,0) + m V'` with ordinate `m L'` (the H-form, `t_p(x) = r`).
The hypotheses are the conjugate's one-point-per-ordinate cut (`hcutC`) and the base labelling `base`. -/

namespace FLatticePaper.QueryClassMain

open Farey FLatticePaper FLatticePaper.Induction

/-- **The transport classification.** -/
theorem transport_class {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hcutC : FreeEnum.CutOnePerOrdinate (frameAt (conjWord word)))
    {w : Site} (hw : w ∈ (frameAt word).freeH)
    (hW1 : (frameAt word).eps = 1 → w.1 ≠ (frameAt word).child.den)
    {base : ℤ → Site}
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r) :
    (FreeEnum.vAt (frameAt (conjWord word)) base (QueryGrade.zq (w - (frameAt word).sheetShift)).2 =
        QueryGrade.zq (w - (frameAt word).sheetShift) ∧
      ((QueryGrade.zq (w - (frameAt word).sheetShift)).2 % FreeEnum.period (frameAt (conjWord word)) ≠ 0 ∨
        ((frameAt word).eps = 1 ∧ (QueryGrade.zq (w - (frameAt word).sheetShift)).2 = 0))) ∨
    (∃ m : ℤ, QueryGrade.zq (w - (frameAt word).sheetShift) =
        ((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word)) ∧
      (QueryGrade.zq (w - (frameAt word).sheetShift)).2 = m * FreeEnum.period (frameAt (conjWord word))) := by
  -- parent facts
  set N := (frameAt word).parents.odd.num with hNdef
  set D := (frameAt word).parents.odd.den with hDdef
  have hN1 : 1 ≤ (frameAt word).parents.odd.num := frameAt_odd_num_pos h
  obtain ⟨hD, hN0, hNle, hodd⟩ := NativeGrade.odd_parent_facts (frameAt word)
  have hND : (frameAt word).parents.odd.num < (frameAt word).parents.odd.den := by omega
  have hcop := ParentGradeKernel.isCoprime_ND _ _ _ _ _ (NativeGrade.eps_eq_child (frameAt word))
    (frameAt word).eps_unit
  have hNne : (frameAt word).parents.odd.num ≠ 0 := by omega
  have hpd := QueryClassFrame.period_conj h
  have hvd := QueryClassFrame.vdeck_conj h
  obtain ⟨hn0, hnd, hd2, hd3, -⟩ := (frameAt word).child_facts
  have hLpos : 0 < (frameAt word).child.den + (frameAt word).child.num := by omega
  -- the query
  set x := w - (frameAt word).sheetShift with hxdef
  have hxw : EvenSite x ↔ EvenSite w := QueryClassFrame.evenSite_sub_shift (frameAt word) w
  have hpx := TpFrame.tp_query_bounds (frameAt word) hw
  rw [hpd] at ⊢
  rw [hvd]
  obtain ⟨mq, hmq⟩ : ∃ m : ℤ, m = (x.1 - 1) / (2 * D) := ⟨_, rfl⟩
  obtain ⟨iq, hiq⟩ : ∃ i : ℤ, i = (x.1 - 1) % (2 * D) := ⟨_, rfl⟩
  have hdec : x.1 - 1 = 2 * D * mq + iq := by
    rw [hmq, hiq, Int.emod_def]
    ring
  have hi0 : 0 ≤ iq := by
    rw [hiq]
    exact Int.emod_nonneg _ (by omega)
  have hi1 : iq < 2 * D := by
    rw [hiq]
    exact Int.emod_lt_of_pos _ (by omega)
  have hvA : FreeEnum.vAt (frameAt (conjWord word)) base (QueryGrade.zq x).2 =
      ((base iq).1 + mq * (-(2 * N)), (base iq).2 + mq * (2 * D)) := by
    unfold FreeEnum.vAt
    rw [hvd, hpd]
    have e1 : (QueryGrade.zq x).2 % (2 * D) = iq := by
      rw [hiq]
      rfl
    have e2 : (QueryGrade.zq x).2 / (2 * D) = mq := by
      rw [hmq]
      rfl
    rw [e1, e2]
  have hzq : QueryGrade.zq x = (-x.2, x.1 - 1) := rfl
  have hmodq : (QueryGrade.zq x).2 % (2 * D) = iq := by
    rw [hiq]
    rfl
  by_cases hE : EvenSite w
  · -- even query: t_p(x) ∈ [1, r]
    have hxe : EvenSite x := hxw.mpr hE
    have htpE : 1 ≤ (frameAt word).parentTGrade x ∧ (frameAt word).parentTGrade x ≤ D + N := by
      rcases (frameAt word).eps_unit with he | he
      · exact (hpx.2 he).1 hE
      · exact (hpx.1 he).1 hE
    by_cases htr : (frameAt word).parentTGrade x = D + N
    · -- H-form: t_p(x) = r
      right
      obtain ⟨m', hm1, hm2⟩ := QueryCPFrame.hform_of_tp N D x hcop hNne hodd
        (by unfold EvenSite at hxe; exact hxe) htr
      refine ⟨m', ?_, ?_⟩
      · rw [hzq]
        ext
        · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
          linarith
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          linarith
      · rw [hzq]
        linarith
    · -- V-form: the representative is a free V point of the conjugate
      left
      have htp1r : (frameAt word).parentTGrade x ≤ D + N - 1 := by
        have : (frameAt word).parentTGrade x < D + N := lt_of_le_of_ne htpE.2 htr
        omega
      have hrep := QueryCPFrame.rep_mem_of_even h x mq iq hdec hi0 hi1 hxe hN1 hND htpE.1 htpE.2
      have hex := QueryCPFrame.exit_of_rep h x mq iq hdec (Or.inr ⟨hxe, htp1r⟩)
      have hvS := (QueryClassFrame.vSpectrum_rep h x mq iq hdec hN1).2
        ⟨htpE.1, htp1r⟩
      have hfree := mem_freeV_of (frameAt (conjWord word))
        ((-x.2 + 2 * N * mq, iq) : ℤ × ℤ) hrep hex hvS
      have hi1p : iq < FreeEnum.period (frameAt (conjWord word)) := by rw [hpd]; exact hi1
      have hbeq := QueryClassFrame.rep_eq_base hcutC hbase hfree hi0 hi1p rfl
      refine ⟨?_, ?_⟩
      · rw [hvA, ← hbeq, hzq]
        ext
        · simp only
          ring
        · simp only
          linarith
      · by_cases hz0 : iq = 0
        · exfalso
          have hori := origin_mem_freeV (frameAt (conjWord word))
          have hbo := QueryClassFrame.rep_eq_base hcutC hbase hori (le_refl 0) (by rw [hpd]; omega) (rfl : (0 : ℤ) = 0)
          have hrep0 : ((-x.2 + 2 * N * mq, iq) : ℤ × ℤ) = ((0 : ℤ), (0 : ℤ)) := by
            rw [hbeq, hz0, ← hbo]
          have hpar := QueryClassFrame.rep_not_even_of_even (word := word) x mq iq hdec hxe
          have hEv : EvenSite ((0 : ℤ), (0 : ℤ)) := by
            unfold EvenSite
            norm_num
          exact hpar (by rw [hrep0]; exact hEv)
        · exact Or.inl (by rw [hmodq]; exact hz0)
  · -- odd query: t_p(x) ∈ [N, D]
    have hxo : ¬ EvenSite x := fun hx => hE (hxw.mp hx)
    have htpOD : N ≤ (frameAt word).parentTGrade x ∧ (frameAt word).parentTGrade x ≤ D := by
      rcases (frameAt word).eps_unit with he | he
      · have hb := (hpx.2 he).2 hE
        have hphW : (frameAt word).phaseW = 1 := by
          unfold ChildFrame.phaseW
          rw [he]
          norm_num
        have htpxw : (frameAt word).parentTGrade x = (frameAt word).parentTGrade w := by
          rw [hxdef, QueryClassFrame.tp_sub_shift, hphW, he]
          ring
        have hwD : (frameAt word).parentTGrade w ≤ D := by
          obtain ⟨⟨hn1, hd1⟩, ⟨hu0, hu1⟩⟩ := TpFrame.freeH_odd_tu (frameAt word) hw hE
          have hkey := (frameAt word).key_identity_tp w
          rw [he] at hkey
          have hdet : (frameAt word).eps = N * (frameAt word).child.den - D * (frameAt word).child.num :=
            NativeGrade.eps_eq_child (frameAt word)
          rw [he] at hdet
          have hrd : (D + N) * (frameAt word).child.den =
              D * ((frameAt word).child.den + (frameAt word).child.num) + 1 := by
            linear_combination (-1 : ℤ) * hdet
          have hkey' : ((frameAt word).child.den + (frameAt word).child.num) * (frameAt word).parentTGrade w =
              (D + N) * ((frameAt word).child.num * w.1 - (frameAt word).child.den * w.2) + (w.1 + w.2) := by
            unfold ChildFrame.tGrade at hkey
            linarith
          exact QueryClass.tp_le_D_of_w1_ne D N (frameAt word).child.num (frameAt word).child.den w.1 w.2
            ((frameAt word).parentTGrade w) hD hN0 hLpos hrd hkey' (by unfold ChildFrame.tGrade at hd1; linarith)
            (by linarith) (by linarith [hb.2, htpxw]) (hW1 he)
        exact ⟨by linarith [hb.1, htpxw], by linarith [hwD, htpxw]⟩
      · have hb := (hpx.1 he).2 hE
        exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
    have hrep := QueryCPFrame.rep_mem_of_odd h x mq iq hdec hi0 hi1 hxo hN1 hND htpOD.1 htpOD.2
    have hex := QueryCPFrame.exit_of_rep h x mq iq hdec (Or.inl ⟨hxo, htpOD.2⟩)
    have htpOD' : N ≤ N * x.1 - D * x.2 ∧ N * x.1 - D * x.2 ≤ D := htpOD
    have hvS := (QueryClassFrame.vSpectrum_rep h x mq iq hdec hN1).2 ⟨by linarith [htpOD'.1], by linarith [htpOD'.2]⟩
    have hfree := mem_freeV_of (frameAt (conjWord word)) ((-x.2 + 2 * N * mq, iq) : ℤ × ℤ) hrep hex hvS
    have hi1p : iq < FreeEnum.period (frameAt (conjWord word)) := by rw [hpd]; exact hi1
    have hbeq := QueryClassFrame.rep_eq_base hcutC hbase hfree hi0 hi1p rfl
    left
    refine ⟨?_, ?_⟩
    · rw [hvA, ← hbeq, hzq]
      ext
      · simp only
        ring
      · simp only
        linarith
    · by_cases hz0 : iq = 0
      · rcases (frameAt word).eps_unit with he | he
        · -- phase one: the origin-type query forces m = 0
          right
          have hxeq : x = w := by
            rw [hxdef, QueryClassFrame.sheetShift_coords]
            have hphW : (frameAt word).phaseW = 1 := by
              unfold ChildFrame.phaseW
              rw [he]
              norm_num
            rw [hphW]
            ext <;> simp
          have hori := origin_mem_freeV (frameAt (conjWord word))
          have hbo := QueryClassFrame.rep_eq_base hcutC hbase hori (le_refl 0) (by rw [hpd]; omega) rfl
          have hrep0 : ((-x.2 + 2 * N * mq, iq) : ℤ × ℤ) = ((0 : ℤ), (0 : ℤ)) := by
            rw [hbeq, hz0, ← hbo]
          have hr1 : -x.2 + 2 * N * mq = 0 := congrArg Prod.fst hrep0
          have hx2 : x.2 = 2 * N * mq := by linarith
          have hx1 : x.1 = 2 * D * mq + 1 := by linarith
          obtain ⟨hwn1, -, -, -⟩ := FreeTraceBox.freeH_box (frameAt word) hw
          obtain ⟨⟨hn1', hd1'⟩, ⟨hu0', hu1'⟩⟩ := TpFrame.freeH_odd_tu (frameAt word) hw hE
          have hmq0 : 0 ≤ mq := by
            have hw1 : 1 ≤ x.1 := by rw [hxeq]; exact hwn1
            have h2 : 0 ≤ 2 * D * mq := by linarith
            by_contra hneg
            rw [not_le] at hneg
            have : 2 * D * mq < 0 := by nlinarith
            linarith
          have hε1 : N * (frameAt word).child.den - D * (frameAt word).child.num = 1 := by
            have hdet : (frameAt word).eps = N * (frameAt word).child.den - D * (frameAt word).child.num :=
              NativeGrade.eps_eq_child (frameAt word)
            rw [he] at hdet
            linarith
          have ht : (frameAt word).child.num ≤ (frameAt word).child.num * (2 * D * mq + 1) -
              (frameAt word).child.den * (2 * N * mq) := by
            have ht0 := hn1'
            unfold ChildFrame.tGrade at ht0
            have hw1' : w.1 = 2 * D * mq + 1 := by rw [← hxeq]; exact hx1
            have hw2' : w.2 = 2 * N * mq := by rw [← hxeq]; exact hx2
            rw [hw1', hw2'] at ht0
            exact ht0
          have hm0 := QueryClass.origin_m_zero D N (frameAt word).child.num (frameAt word).child.den mq hmq0 hε1 ht
          have hk0 : (QueryGrade.zq x).2 = 0 := by
            rw [hzq, hdec, hz0, hm0]
            ring
          exact ⟨he, hk0⟩
        · -- phase zero: the origin-type query has t_p = N, excluded by the odd range N + 1 ≤ t_p
          exfalso
          have hb := (hpx.1 he).2 hE
          have hr1 : -x.2 + 2 * N * mq = 0 := by
            have hori := origin_mem_freeV (frameAt (conjWord word))
            have hbo := QueryClassFrame.rep_eq_base hcutC hbase hori (le_refl 0) (by rw [hpd]; omega) rfl
            have hrep0 : ((-x.2 + 2 * N * mq, iq) : ℤ × ℤ) = ((0 : ℤ), (0 : ℤ)) := by
              rw [hbeq, hz0, ← hbo]
            exact congrArg Prod.fst hrep0
          have hx1 : x.1 = 2 * D * mq + 1 := by
            linarith
          have hx2 : x.2 = 2 * N * mq := by linarith
          have htpN : (frameAt word).parentTGrade x = N := by
            unfold ChildFrame.parentTGrade
            rw [hx1, hx2]
            ring
          linarith [hb.1]
      · exact Or.inl (by rw [hmodq]; exact hz0)

/-- **The reflection of a free H point is a free H point:** `reflH w = U + I − w` (`ArcPsi.reflH`). -/
theorem reflH_mem_freeH {word : Word} {w : Site} (hw : w ∈ (frameAt word).freeH) :
    ArcPsi.reflH word w ∈ (frameAt word).freeH := by
  have hr := CollarTop.freeH_reflect (frameAt word) hw
  have e : (frameAt word).centre - (w + (frameAt word).child.modifiedDeck.transverse) = ArcPsi.reflH word w := by
    unfold ArcPsi.reflH
    rw [CollarTop.centre_eq, ChildFrame.child_modifiedDeck_transverse]
    ext <;> simp <;> ring
  rw [← e]
  exact hr

end FLatticePaper.QueryClassMain
