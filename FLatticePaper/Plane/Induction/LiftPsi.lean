import FLatticePaper.Plane.Induction.PriceAtI
import FLatticePaper.Plane.Induction.LiftTranslate
import FLatticePaper.Plane.Induction.NativeGrade
import FLatticePaper.Plane.Induction.ParentGradeKernel
import FLatticePaper.Plane.Induction.CutOnePerProper
import FLatticePaper.Plane.Induction.OddFreeH
import FLatticePaper.Plane.Induction.ArcCut
import FLatticePaper.Plane.Induction.PriceDeck
import FLatticePaper.Plane.Induction.ZoneI1
import FLatticePaper.Plane.Induction.FreeEnum
import FLatticePaper.Plane.Induction.SheetFacts
import FLatticePaper.Plane.Induction.BaseMembership

/-! Task 72 / Q31 psi (i)–(iii): the lift `ψ(z) = ⌈j/r⌉` on the nonfinal native free V cut.

Reference values: `hTrace` is the conjugate's H-arc price trace (named hypothesis (a)). The origin and the phase-one top
reference `(0, −1) + V_p` are fixed by the price at the reflected origin. -/

namespace FLatticePaper.LiftPsi

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet NativeGrade

/-- **The conjugate's freeH trace gives the reference instance.** For a free V point `b` of the word with ordinate
`b.2 ∈ [0, r − 1]`, the point `(1 + b.2, −b.1)` is in the conjugate's free H arc (`base_mem_freeH`); the trace there is
`c₀'` at `(1, 0)` and `c₀' − 1` elsewhere, and `(1 + b.2, −b.1) = (1, 0)` exactly when `b.2 = 0`, since the free V point of ordinate
`0` is the origin (`CutOnePerProper`, uniqueness). -/
theorem trace_ref {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hTraceConj : ∀ w ∈ (frameAt (conjWord word)).freeH,
      (frameAt (conjWord word)).price (standardField (conjWord word)) w =
        (frameAt (conjWord word)).cutPrice - (if w = ((1 : ℤ), (0 : ℤ)) then 0 else 1))
    {b : Site} (hb : b ∈ (frameAt word).freeV) (h0 : 0 ≤ b.2)
    (hr : b.2 ≤ (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1)
    (hph : (frameAt word).eps = -1 ∨ b.2 ≤ (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 2) :
    (frameAt (conjWord word)).price (standardField (conjWord word)) ((1 : ℤ) + b.2, -b.1) =
      (frameAt (conjWord word)).cutPrice - (if b.2 = 0 then 0 else 1) := by
  have hm := BaseMembership.base_mem_freeH h hb h0 hr hph
  have ht := hTraceConj _ hm
  by_cases hb0 : b.2 = 0
  · have hL : 0 < (frameAt word).child.den + (frameAt word).child.num := by
      obtain ⟨hn0, hnd, -, -, -⟩ := (frameAt word).child_facts
      omega
    obtain ⟨x0, -, huniq⟩ := CutOnePerProper.cutOnePerOrdinate_of_proper h 0 le_rfl (by unfold FreeEnum.period; omega)
    have hbeq : (b.1, (0 : ℤ)) = b := Prod.ext rfl hb0.symm
    have e1 : b.1 = x0 := huniq b.1 (by show (b.1, (0 : ℤ)) ∈ (frameAt word).freeV; rw [hbeq]; exact hb)
    have e2 : (0 : ℤ) = x0 := huniq 0 (origin_mem_freeV (frameAt word))
    have hb1 : b.1 = 0 := by omega
    have hw : ((1 : ℤ) + b.2, -b.1) = ((1 : ℤ), (0 : ℤ)) := by
      rw [hb0, hb1]
      simp
    rw [if_pos hw] at ht
    rw [ht, if_pos hb0]
  · have hne : ((1 : ℤ) + b.2, -b.1) ≠ ((1 : ℤ), (0 : ℤ)) := by
      intro e
      have h1 := congrArg Prod.fst e
      simp only at h1
      omega
    rw [if_neg hne] at ht
    rw [ht, if_neg hb0]

/-- **The reference value on a free V point.** Under the conjugate's H-arc trace, `ψ(b) = [b.2 ≠ 0]` for the free V points of
ordinate `b.2 ∈ [0, r − 1]` (with `b.2 ≤ r − 2` in phase `ε = +1`). -/
theorem psi_ref {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hTraceConj : ∀ w ∈ (frameAt (conjWord word)).freeH,
      (frameAt (conjWord word)).price (standardField (conjWord word)) w =
        (frameAt (conjWord word)).cutPrice - (if w = ((1 : ℤ), (0 : ℤ)) then 0 else 1))
    {b : Site} (hb : b ∈ (frameAt word).freeV) (h0 : 0 ≤ b.2)
    (hr : b.2 ≤ (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1)
    (hph : (frameAt word).eps = -1 ∨ b.2 ≤ (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 2) :
    FqW word (b + (frameAt word).uq) - FqW word b = if b.2 = 0 then 0 else 1 := by
  rw [PriceReflect.psi_reflect_price h hSE b]
  have hI : reflectionI - zTurn b = ((1 : ℤ) + b.2, -b.1) := by
    ext
    · simp [zTurn, reflectionI]
    · simp [zTurn, reflectionI]
      ring
  rw [hI, trace_ref h hTraceConj hb h0 hr hph]
  ring

/-- **The jump at `(0, −1)` vanishes:** `ψ((0, −1)) = 0`, since `I − zTurn(0,−1) = 0` and `P'(0) = c₀'` (the origin is a
conjugate free V point). -/
theorem psi_neg_one {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) :
    FqW word (((0 : ℤ), (-1 : ℤ)) + (frameAt word).uq) - FqW word ((0 : ℤ), (-1 : ℤ)) = 0 := by
  rw [PriceReflect.psi_reflect_price h hSE]
  have hz : reflectionI - zTurn ((0 : ℤ), (-1 : ℤ)) = ((0 : ℤ), (0 : ℤ)) := by
    ext <;> simp [zTurn, reflectionI]
  have hP := PriceDeck.price_on_freeV (frameAt (conjWord word)) (standardField (conjWord word))
    hSE.packet.strips (origin_mem_freeV (frameAt (conjWord word)))
  rw [hz, hP]
  ring

/-- **`L > r`:** the child's `d + n` exceeds the parent `D + N`, since `L − r = r + d_q + n_q` with `d_q > 0`, `n_q ≥ 0`. -/
theorem r_lt_L (frame : ChildFrame) :
    frame.parents.odd.den + frame.parents.odd.num < frame.child.den + frame.child.num := by
  have he := frame.valid.even_bounds
  have ho := frame.valid.odd_bounds
  unfold Fraction.InUnitInterval at he ho
  rw [ZoneI1.child_num_eq, ZoneI1.child_den_eq]
  omega

/-- `N` and `D` of the odd parent are coprime. -/
theorem isCoprime_ND_of_frame (frame : ChildFrame) :
    IsCoprime frame.parents.odd.num frame.parents.odd.den :=
  ParentGradeKernel.isCoprime_ND _ _ _ _ _ (eps_eq_child frame) frame.eps_unit

/-- **Same parent grade and ordinates differing by `r k` give `b = c + k V_p`.** -/
theorem eq_add_vp_of_pg (frame : ChildFrame) {b c : Site} {k : ℤ}
    (hpg : pg frame b = pg frame c) (hk : b.2 = c.2 + (frame.parents.odd.den + frame.parents.odd.num) * k) :
    b = c + k • TipVertex.tipVertex frame := by
  obtain ⟨hDpos, hN0, hNle, hodd⟩ := odd_parent_facts frame
  have hε := eps_eq_child frame
  have hcop := ParentGradeKernel.isCoprime_ND _ _ _ _ _ hε frame.eps_unit
  have hr : frame.parents.odd.den + frame.parents.odd.num ≠ 0 := by omega
  obtain ⟨k', hk1, hk2⟩ := ParentGradeKernel.same_grade_vp frame.parents.odd.num frame.parents.odd.den hcop
    hodd hr b.1 b.2 c.1 c.2 hpg
  have hkk : k = k' := by
    apply mul_left_cancel₀ hr
    linear_combination hk2 - hk
  rw [← hkk] at hk1 hk2
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, TipVertex.tipVertex]
    linear_combination hk1
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, TipVertex.tipVertex]
    linear_combination hk2

/-- **The residue-zero form:** an ordinate `i ∈ [0, r)` with the parent grade of `(x, i)` equal to that of `c` (ordinate `0`) is `0`. -/
theorem ord_zero_of_pg (frame : ChildFrame) (hN : 0 < frame.parents.odd.num) {x i : ℤ} {c : Site} (hc : c.2 = 0)
    (hpg : pg frame (x, i) = pg frame c) (hi0 : 0 ≤ i)
    (hi1 : i < frame.parents.odd.den + frame.parents.odd.num) : i = 0 := by
  obtain ⟨hDpos, hN0, hNle, hodd⟩ := odd_parent_facts frame
  have hε := eps_eq_child frame
  have hcop := ParentGradeKernel.isCoprime_ND _ _ _ _ _ hε frame.eps_unit
  have hr : frame.parents.odd.den + frame.parents.odd.num ≠ 0 := by omega
  obtain ⟨k, -, hk2⟩ := ParentGradeKernel.same_grade_vp frame.parents.odd.num frame.parents.odd.den hcop
    hodd hr x i c.1 c.2 hpg
  have hr0 : 0 < frame.parents.odd.den + frame.parents.odd.num := by omega
  have hk0 : k = 0 := by
    rcases lt_trichotomy k 0 with hk | hk | hk
    · nlinarith
    · exact hk
    · nlinarith
  rw [hk0, hc] at hk2
  simp at hk2
  omega

/-- **Phase one, top residue.** With `ε = 1`, a nonfinal free V point of ordinate `r − 1` has parent grade `−c_p`. -/
theorem phase1_top (frame : ChildFrame) (hN : 0 < frame.parents.odd.num) (hcut : FreeEnum.CutOnePerOrdinate frame)
    (hε : frame.eps = 1) {b : Site} (hb : b ∈ frame.freeV) (hbne : b ≠ frame.vLast)
    (hbj : b.2 = frame.parents.odd.den + frame.parents.odd.num - 1) :
    pg frame b = -(frame.parents.odd.den - frame.parents.odd.num) := by
  obtain ⟨hDpos, hN0, hNle, hodd⟩ := odd_parent_facts frame
  have hg := grade_mem frame hcut hb hbne
  have e : pg frame b + (frame.parents.odd.den - frame.parents.odd.num) =
      (frame.parents.odd.den + frame.parents.odd.num) * (b.1 + (frame.parents.odd.den - frame.parents.odd.num)) := by
    unfold pg
    rw [hbj]
    ring
  obtain ⟨t, ht⟩ : ∃ t, t = b.1 + (frame.parents.odd.den - frame.parents.odd.num) := ⟨_, rfl⟩
  rw [← ht] at e
  have hcp : 1 ≤ frame.parents.odd.den - frame.parents.odd.num := by omega
  have hr0 : 0 < frame.parents.odd.den + frame.parents.odd.num := by omega
  have hgE' : gE frame = 2 * frame.parents.odd.num - 2 := by
    unfold gE
    rw [if_pos hε]
  have hgLo' : gLo frame = -(frame.parents.odd.den - frame.parents.odd.num) := by
    unfold gLo
    rw [if_neg (by rw [hε]; norm_num)]
  rcases hg with ⟨he, hlo, hhi⟩ | ⟨ho, hlo, hhi⟩
  · exfalso
    rw [hgE'] at hhi
    rcases (show t ≤ 0 ∨ 1 ≤ t by omega) with h1 | h1 <;> nlinarith
  · rw [hgLo'] at hlo
    have ht0 : 0 ≤ t := by nlinarith
    have ht2 : t ≤ 1 := by nlinarith
    rcases (show t = 0 ∨ t = 1 by omega) with h0 | h1
    · rw [h0, mul_zero] at e
      linarith
    · exfalso
      rw [h1, mul_one] at e
      omega

/-- **The core of the lift.** For a nonfinal free V point `z = (x, i + r kq)` with `0 ≤ i < r`:
`ψ(z) = kq + [i ≠ 0]`. -/
theorem psi_core {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hTraceConj : ∀ w ∈ (frameAt (conjWord word)).freeH,
      (frameAt (conjWord word)).price (standardField (conjWord word)) w =
        (frameAt (conjWord word)).cutPrice - (if w = ((1 : ℤ), (0 : ℤ)) then 0 else 1))
    {z : Site} (hz : z ∈ (frameAt word).freeV) (hne : z ≠ (frameAt word).vLast) {i kq : ℤ}
    (hz2 : z.2 = i + ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * kq)
    (hi0 : 0 ≤ i) (hi1 : i < (frameAt word).parents.odd.den + (frameAt word).parents.odd.num) :
    FqW word (z + (frameAt word).uq) - FqW word z = kq + (if i = 0 then 0 else 1) := by
  have hN : 0 < (frameAt word).parents.odd.num := frameAt_odd_num_pos h
  have hcut := CutOnePerProper.cutOnePerOrdinate_of_proper h
  obtain ⟨hDpos, hN0, hNle, hodd⟩ := odd_parent_facts (frameAt word)
  have hLr := r_lt_L (frameAt word)
  have hr0 : 0 < (frameAt word).parents.odd.den + (frameAt word).parents.odd.num := by omega
  obtain ⟨xb, hxb, -⟩ := hcut i hi0 (by unfold FreeEnum.period; omega)
  have hbne : ((xb, i) : Site) ≠ (frameAt word).vLast :=
    ne_vLast_of_ordinate (frameAt word) (by show i < (frameAt word).child.den + (frameAt word).child.num - 1; omega)
  have htri := pg_trichotomy (frameAt word) hcut hN hz hne hxb hbne kq
    (by show z.2 - i = ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * kq; rw [hz2]; ring)
  rcases htri with hEq | ⟨hzg0, hbgr⟩ | ⟨hzgr, hbg0⟩
  · -- the class of the residue representative
    have hzvp : z = ((xb, i) : Site) + kq • TipVertex.tipVertex (frameAt word) :=
      eq_add_vp_of_pg (frameAt word) hEq (by show z.2 = i + _ * kq; exact hz2)
    by_cases hed : (frameAt word).eps = 1 ∧ i = (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1
    · obtain ⟨he1, hi⟩ := hed
      have hpgb := phase1_top (frameAt word) hN hcut he1 hxb hbne (by show i = _; exact hi)
      have hpgc : pg (frameAt word) ((0 : ℤ), (-1 : ℤ)) = -((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) := by
        unfold pg
        ring
      have hwv : ((xb, i) : Site) = ((0 : ℤ), (-1 : ℤ)) + (1 : ℤ) • TipVertex.tipVertex (frameAt word) :=
        eq_add_vp_of_pg (frameAt word) (hpgb.trans hpgc.symm)
          (by show i = -1 + ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * 1; omega)
      have h1 := LiftTranslate.psi_tip_int h hSE 1 ((0 : ℤ), (-1 : ℤ))
      rw [psi_neg_one h hSE] at h1
      have hpsib : FqW word ((xb, i) + (frameAt word).uq) - FqW word (xb, i) = 1 := by
        rw [hwv]
        linarith
      rw [hzvp, LiftTranslate.psi_tip_int h hSE kq (xb, i), hpsib]
      have hi' : i ≠ 0 := by omega
      rw [if_neg hi']
      ring
    · have hph : (frameAt word).eps = -1 ∨ i ≤ (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 2 := by
        rcases (frameAt word).eps_unit with he | he
        · exact Or.inr (by
            have : i ≠ (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1 := fun hi => hed ⟨he, hi⟩
            omega)
        · exact Or.inl he
      have hr := psi_ref h hSE hTraceConj hxb (show (0 : ℤ) ≤ i from hi0)
        (show i ≤ (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1 by omega) hph
      rw [hzvp, LiftTranslate.psi_tip_int h hSE kq (xb, i), hr]
      show (if i = 0 then (0 : ℤ) else 1) + kq = kq + (if i = 0 then 0 else 1)
      ring
  · -- pg z = 0 and pg (xb, i) = r: impossible
    exfalso
    have hbgr' : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * xb +
        ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * i =
        (frameAt word).parents.odd.den + (frameAt word).parents.odd.num := hbgr
    have hpg10 : pg (frameAt word) (xb, i) = pg (frameAt word) ((1 : ℤ), (0 : ℤ)) := by
      rw [hbgr]
      unfold pg
      ring
    have hi0' : i = 0 := ord_zero_of_pg (frameAt word) hN (c := ((1 : ℤ), (0 : ℤ))) rfl hpg10 hi0 hi1
    subst hi0'
    obtain ⟨k, hk1, hk2⟩ := ParentGradeKernel.same_grade_vp (frameAt word).parents.odd.num
      (frameAt word).parents.odd.den (isCoprime_ND_of_frame (frameAt word)) hodd
      (by omega) xb 0 1 0 (by unfold pg at hpg10; linarith)
    have hk0 : k = 0 := by
      have hm : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * k = 0 := by linarith
      rcases mul_eq_zero.mp hm with h0 | h0
      · omega
      · exact h0
    rw [hk0, mul_zero] at hk1
    have hx1 : xb = 1 := by linarith
    obtain ⟨x0, -, huniq⟩ := hcut 0 le_rfl (by unfold FreeEnum.period; omega)
    have e1 : xb = x0 := huniq xb hxb
    have e2 : (0 : ℤ) = x0 := huniq 0 (origin_mem_freeV (frameAt word))
    omega
  · -- pg z = r and pg (xb, i) = 0: the class of (1, 0)
    have hi0' : i = 0 := ord_zero_of_pg (frameAt word) hN (c := ((0 : ℤ), (0 : ℤ))) rfl
      (by rw [hbg0]; unfold pg; ring) hi0 hi1
    subst hi0'
    have hzvp : z = ((1 : ℤ), (0 : ℤ)) + kq • TipVertex.tipVertex (frameAt word) :=
      eq_add_vp_of_pg (frameAt word) (by rw [hzgr]; unfold pg; ring) (by show z.2 = (0 : ℤ) + _ * kq; exact hz2)
    rw [hzvp, LiftTranslate.psi_tip_int h hSE kq ((1 : ℤ), (0 : ℤ)), PriceAtI.psi_at_one_zero h hSE]
    simp

/-- **The lift.** On the nonfinal native free V cut, `ψ(z) = ⌈z.2 / r⌉`, where `r = D + N`. -/
theorem psi_lift {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hTraceConj : ∀ w ∈ (frameAt (conjWord word)).freeH,
      (frameAt (conjWord word)).price (standardField (conjWord word)) w =
        (frameAt (conjWord word)).cutPrice - (if w = ((1 : ℤ), (0 : ℤ)) then 0 else 1))
    {z : Site} (hz : z ∈ (frameAt word).freeV) (hne : z ≠ (frameAt word).vLast) :
    FqW word (z + (frameAt word).uq) - FqW word z =
      ArcCut.ceilDiv z.2 ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) := by
  obtain ⟨hDpos, hN0, hNle, hodd⟩ := odd_parent_facts (frameAt word)
  have hr0 : 0 < (frameAt word).parents.odd.den + (frameAt word).parents.odd.num := by omega
  have hi0 : 0 ≤ z.2 % ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) :=
    Int.emod_nonneg _ hr0.ne'
  have hi1 : z.2 % ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) <
      (frameAt word).parents.odd.den + (frameAt word).parents.odd.num := Int.emod_lt_of_pos _ hr0
  have hz2 : z.2 = z.2 % ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) +
      ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * (z.2 / ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) :=
    by
      rw [Int.emod_def]
      ring
  rw [psi_core h hSE hTraceConj hz hne hz2 hi0 hi1]
  have hc := ArcCut.ceilDiv_lift ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)
    (z.2 / ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num))
    (z.2 % ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) hr0 hi0 hi1
  have e : z.2 % ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) +
      z.2 / ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) *
        ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) = z.2 := by
    rw [Int.emod_def]
    ring
  rw [e] at hc
  rw [hc]

end FLatticePaper.LiftPsi
