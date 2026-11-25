import FLatticePaper.Plane.Induction.W4OldV
import FLatticePaper.Plane.Induction.W4FreeTail
import FLatticePaper.Plane.Induction.W4Exceptional
import FLatticePaper.Plane.Induction.W4FloorArc
import FLatticePaper.Plane.Induction.W4NativeSlip
import FLatticePaper.Plane.Induction.W4Boundary
import FLatticePaper.Plane.Induction.W4OfferB

/-! # W4 (Q35/Q34): the free-tail case with `a(c) = 1`, and `NoRiseForced`

The rise `a(c) ≥ 1`, `a(i) = 0`, `B(c) ≥ 1` reduces to `a(c) = 1` by the unit price bound along `Edge i c` (`aJump_sub_le_one`).
With `a(c) = 1` the free tail is one of: the old V star (a native H label `g` of the conjugate: `g = hFirst` (east), `g = hLast` with
`ε = 1` (exceptional), or ordinary `g`: the guard), or the old H star (a conjugate free V point, `oldH_star_jumpA'`). -/

namespace FLatticePaper.W4Guard

open Farey FLatticePaper FLatticePaper.Induction

/-- The lattice map `φ y = I − Z y = (1 + y₂, −y₁)`. -/
def phi (y : Site) : Site := reflectionI - zTurn y

theorem phi_eq (y : Site) : phi y = (1 + y.2, -y.1) := by
  unfold phi zTurn reflectionI
  ext
  · simp
  · simp
    ring

/-- The input relation as a linear condition on the coordinates and the parity of `x`. -/
theorem edge_iff (y x : Site) : Edge y x ↔
    ((EvenSite x ∧ y.2 = x.2 ∧ (y.1 = x.1 - 1 ∨ y.1 = x.1 + 1)) ∨
      (¬ EvenSite x ∧ y.1 = x.1 ∧ (y.2 = x.2 - 1 ∨ y.2 = x.2 + 1))) := by
  unfold Edge incomingNeg incomingPos EvenSite
  by_cases hx : (x.1 + x.2) % 2 = 0
  · simp [hx, Prod.ext_iff]; omega
  · simp [hx, Prod.ext_iff]; omega

/-- `φ` maps input relations to input relations. -/
theorem edge_phi {y x : Site} (h : Edge y x) : Edge (phi y) (phi x) := by
  rw [edge_iff] at h
  rw [edge_iff, phi_eq, phi_eq]
  unfold EvenSite at h ⊢
  omega

/-- Translation by an even site preserves the input relation. -/
theorem edge_add_even {y x v : Site} (hv : EvenSite v) (h : Edge y x) : Edge (y + v) (x + v) := by
  rw [edge_iff] at h
  rw [edge_iff]
  unfold EvenSite at h hv ⊢
  simp only [Prod.fst_add, Prod.snd_add] at h hv ⊢
  omega

/-- The shift `sheetShift = (1 − W) U_q` is even (`U_q = (eD, eN)`, and `eN + eD` is even). -/
theorem evenSite_sheetShift {word : Word} : EvenSite (frameAt word).sheetShift := by
  have hpe := (frameAt word).valid.even_parity
  unfold Fraction.Even at hpe
  have hk : (frameAt word).parents.even.unmodifiedDeck.kernel =
      ((frameAt word).parents.even.den, (frameAt word).parents.even.num) := rfl
  unfold ChildFrame.sheetShift EvenSite
  rw [hk]
  simp only [Prod.smul_mk, smul_eq_mul]
  have e : (1 - (frameAt word).phaseW) * (frameAt word).parents.even.den +
      (1 - (frameAt word).phaseW) * (frameAt word).parents.even.num =
      (1 - (frameAt word).phaseW) * ((frameAt word).parents.even.num + (frameAt word).parents.even.den) := by ring
  rw [e, Int.mul_emod, hpe]
  simp

/-- **The unit price bound along an input edge.** For `Edge i c`, `|a(c) − a(i)| ≤ 1` (the conjugate's price increments are unit). -/
theorem aJump_sub_le_one {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {c i : Site} (hE : Edge i c) :
    FLatticePaper.W4Reduction.aJump word c - FLatticePaper.W4Reduction.aJump word i ≤ 1 ∧
      FLatticePaper.W4Reduction.aJump word i - FLatticePaper.W4Reduction.aJump word c ≤ 1 := by
  have hs := evenSite_sheetShift (word := word)
  set s := (frameAt word).sheetShift with hsdef
  have hsn : EvenSite (-s) := by
    unfold EvenSite at hs ⊢
    simp only [Prod.fst_neg, Prod.snd_neg]
    omega
  have hE' : Edge (i - s) (c - s) := by
    have := edge_add_even hsn hE
    simpa [sub_eq_add_neg] using this
  have hE'' : Edge (phi (i - s)) (phi (c - s)) := edge_phi hE'
  have hU := hSE.F1_unitPrice (phi (c - s)) (phi (i - s)) hE''
  unfold priceIncrement at hU
  have hac : FLatticePaper.W4Reduction.aJump word c =
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) (c - s) := by
    rw [FLatticePaper.W4FreeTail.aJump_eq_jumpA]
  have hai : FLatticePaper.W4Reduction.aJump word i =
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) (i - s) := by
    rw [FLatticePaper.W4FreeTail.aJump_eq_jumpA]
  have hj : ∀ y : Site, jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) y =
      (frameAt (conjWord word)).cutPrice -
        (frameAt (conjWord word)).price (standardField (conjWord word)) (phi y) := by
    intro y
    rw [jumpA_eq_cutPrice h hSE, zTurn_reflect]
    rfl
  rw [hac, hai, hj, hj]
  constructor <;> linarith [hU.1, hU.2]

/-- The conjugate reflection preserves its free H arc (the mirror of `QueryClassMain.reflH_mem_freeH`). -/
theorem reflH_conj_mem_freeH {word : Word} {g : Site} (hg : g ∈ (frameAt (conjWord word)).freeH) :
    FLatticePaper.ReflectedFan.reflH (frameAt (conjWord word)) g ∈ (frameAt (conjWord word)).freeH := by
  have hr := CollarTop.freeH_reflect (frameAt (conjWord word)) hg
  have e : (frameAt (conjWord word)).centre -
      (g + (frameAt (conjWord word)).child.modifiedDeck.transverse) =
      FLatticePaper.ReflectedFan.reflH (frameAt (conjWord word)) g := by
    unfold FLatticePaper.ReflectedFan.reflH
    rw [CollarTop.centre_eq, ChildFrame.child_modifiedDeck_transverse]
    ext <;> simp <;> ring
  rw [← e]
  exact hr

/-- The conjugate reflection `reflH g` in the grades of the conjugate: `reflH g − U' = I − g`. -/
theorem reflH_sub_kernel_eq {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (g : Site) :
    FLatticePaper.ReflectedFan.reflH (frameAt (conjWord word)) g -
        ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num,
          (frameAt word).parents.odd.den - (frameAt word).parents.odd.num) =
      reflectionI - g := by
  obtain ⟨h1, h2⟩ := FLatticePaper.UnitBound.conj_child_sums h
  unfold FLatticePaper.ReflectedFan.reflH reflectionI
  rw [h1, h2]
  refine Prod.ext ?_ ?_ <;> simp <;> ring

/-- `D'_ε` at `reflH g` is zero (native, `conj_slip_zero_native_H`). -/
theorem slip_reflH_zero {word : Word} (hX : ∃ x ∈ conjWord word, x ≠ Digit.three)
    (hSE' : StrongEstimates (conjWord (conjWord word))) {g : Site}
    (hg : g ∈ (frameAt (conjWord word)).freeH) :
    (frameAt (conjWord word)).slip (standardField (conjWord word)) (frameAt word).eps
      (FLatticePaper.ReflectedFan.reflH (frameAt (conjWord word)) g) = 0 :=
  FLatticePaper.W4NativeSlip.conj_slip_zero_native_H hX hSE' (reflH_conj_mem_freeH hg) (frameAt word).eps_unit

/-- `D'_ε(I − g) = 0`: the kernel drift is zero and `(I − g) + U' = reflH g`. -/
theorem slip_I_sub_zero {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hX : ∃ x ∈ conjWord word, x ≠ Digit.three)
    (hSE' : StrongEstimates (conjWord (conjWord word))) {g : Site}
    (hg : g ∈ (frameAt (conjWord word)).freeH) :
    (frameAt (conjWord word)).slip (standardField (conjWord word)) (frameAt word).eps (reflectionI - g) = 0 := by
  have hdrift := (hSE.slipDrift (frameAt word).eps (frameAt word).eps_unit (reflectionI - g)).1
  rw [W4OldH.conj_kernel_eq h] at hdrift
  have e : reflectionI - g + ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num,
      (frameAt word).parents.odd.den - (frameAt word).parents.odd.num) =
      FLatticePaper.ReflectedFan.reflH (frameAt (conjWord word)) g := by
    rw [← reflH_sub_kernel_eq h g]
    ring
  rw [e, slip_reflH_zero hX hSE' hg, sub_eq_zero] at hdrift
  rw [hdrift]

/-- `D'_ε(I − g + V') = 2ε`: the transverse drift is `2ε`, and `D'_ε(I − g) = 0`. -/
theorem slip_I_sub_add_V {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hX : ∃ x ∈ conjWord word, x ≠ Digit.three)
    (hSE' : StrongEstimates (conjWord (conjWord word))) {g : Site}
    (hg : g ∈ (frameAt (conjWord word)).freeH) :
    (frameAt (conjWord word)).slip (standardField (conjWord word)) (frameAt word).eps
        (reflectionI - g + (-2 * (frameAt word).parents.odd.num, 2 * (frameAt word).parents.odd.den)) =
      2 * (frameAt word).eps := by
  have hdrift := (hSE.slipDrift (frameAt word).eps (frameAt word).eps_unit (reflectionI - g)).2
  rw [W4OldH.conj_transverse_eq h] at hdrift
  rw [slip_I_sub_zero h hSE hX hSE' hg] at hdrift
  linarith

open FLatticePaper.W1 in
/-- **The guard (Q35, ordinary old V root with `a = 1`).** Let `g` be a native free H label of the conjugate and the root satisfy
`ζx = reflH g − U' + c₂V'`, with `c, c + uq` in the closed polygon and `c = x + sheetShift`. If `B(c) ≥ 1` and `c` is strictly
interior, we have a contradiction. The shift `c₂` is `0` or `1` (polygon bounds), `B(c) = 2W − 2ε c₂` (the native slip zero and the
transverse drift), and the boundary contradiction at `c = Zg` (`ε = 1`) or `c = Zg + (d, n)` (`ε = −1`). -/
theorem oldV_guard_a1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hX : ∃ x ∈ conjWord word, x ≠ Digit.three) (hSE' : StrongEstimates (conjWord (conjWord word)))
    {g : Site} (hg : g ∈ (frameAt (conjWord word)).freeH)
    (hne : g ≠ (frameAt (conjWord word)).hLast ∨ (frameAt word).eps = -1)
    {x c : Site} (c2 : ℤ)
    (hx : zTurn x = FLatticePaper.ReflectedFan.reflH (frameAt (conjWord word)) g +
      ((-1) * (frameAt (conjWord word)).child.modifiedDeck.kernel.1 +
          c2 * (frameAt (conjWord word)).child.modifiedDeck.transverse.1,
        (-1) * (frameAt (conjWord word)).child.modifiedDeck.kernel.2 +
          c2 * (frameAt (conjWord word)).child.modifiedDeck.transverse.2))
    (hcx : c = x + (frameAt word).sheetShift)
    (hc : c ∈ (frameAt word).closedPolygon) (hcu : c + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hSI : StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hB : 1 ≤ FLatticePaper.W4Reduction.BOffer word c) : False := by
  obtain ⟨hC1, hC2⟩ := FLatticePaper.UnitBound.conj_child_sums h
  obtain ⟨hD0, hN0, hNleD, hparO⟩ := FLatticePaper.NativeGrade.odd_parent_facts (frameAt word)
  have hND : (frameAt word).parents.odd.num < (frameAt word).parents.odd.den := by omega
  have hcd := FLatticePaper.Induction.ZoneI1.child_den_eq (frameAt word)
  have hcn := FLatticePaper.Induction.ZoneI1.child_num_eq (frameAt word)
  have hn := (frameAt word).child_facts
  have hdn : ((frameAt word).child.num + (frameAt word).child.den) % 2 = 0 := (frameAt word).child_even
  have hε : (frameAt word).parents.odd.num * (frameAt word).child.den -
      (frameAt word).parents.odd.den * (frameAt word).child.num = (frameAt word).eps :=
    ((frameAt word).eps_eq).symm
  have hεu := (frameAt word).eps_unit
  -- the root: `x = Z g + c₂ U_p`
  rw [W4OldH.conj_kernel_eq h, W4OldH.conj_transverse_eq h] at hx
  have hxv : x = (-g.2 + 2 * (frameAt word).parents.odd.den * c2,
      g.1 - 1 + 2 * (frameAt word).parents.odd.num * c2) := by
    apply FLatticePaper.W4OldH.zTurn_injective
    rw [hx]
    unfold zTurn FLatticePaper.ReflectedFan.reflH
    rw [hC1, hC2]
    refine Prod.ext ?_ ?_
    · simp
      ring
    · simp
      ring
  have hpe := (frameAt word).valid.even_parity
  unfold Fraction.Even at hpe
  have hphase : (frameAt word).phaseW = (1 + (frameAt word).eps) / 2 := rfl
  have hshift : (frameAt word).sheetShift =
      (1 - (frameAt word).phaseW) • ((frameAt word).parents.even.den, (frameAt word).parents.even.num) := rfl
  have huq : (frameAt word).uq = ((frameAt word).eps * (frameAt word).parents.even.den,
      (frameAt word).eps * (frameAt word).parents.even.num) := rfl
  set D := (frameAt word).parents.odd.den with hDdef
  set N := (frameAt word).parents.odd.num with hNdef
  set n := (frameAt word).child.num with hndef
  set d := (frameAt word).child.den with hddef
  set eD := (frameAt word).parents.even.den with heDdef
  set eN := (frameAt word).parents.even.num with heNdef
  set v : Site := (-g.2, g.1 - 1) with hvdef
  -- the polygon membership of `x` and of `x + U_q` (`U_q = (eD, eN)`)
  have hxE : x ∈ (frameAt word).closedPolygon ∧ (x.1 + eD, x.2 + eN) ∈ (frameAt word).closedPolygon := by
    rcases hεu with hεu | hεu
    · have hsh : (frameAt word).sheetShift = (0, 0) := by
        rw [hshift, hphase, hεu]
        ext <;> simp
      have hu : (frameAt word).uq = (eD, eN) := by
        rw [huq, hεu]
        simp
      have hxc : x = c := by
        rw [hcx, hsh]
        simp
      rw [hu] at hcu
      refine ⟨?_, ?_⟩
      · rw [hxc]; exact hc
      · rw [hxc]; exact hcu
    · have hsh : (frameAt word).sheetShift = (eD, eN) := by
        rw [hshift, hphase, hεu]
        norm_num
      have hu : (frameAt word).uq = (-eD, -eN) := by
        rw [huq, hεu]
        simp
      have hxc : x = c - (eD, eN) := by
        rw [hcx, hsh]
        simp
      rw [hu] at hcu
      refine ⟨?_, ?_⟩
      · rw [hxc]
        convert hcu using 1
        refine Prod.ext ?_ ?_ <;> simp <;> ring
      · have e : (x.1 + eD, x.2 + eN) = c := by
          rw [hxc]
          refine Prod.ext ?_ ?_ <;> simp
        rw [e]; exact hc
  obtain ⟨hxE1, hxE2⟩ := hxE
  have hxR : closedRect (frameAt word).child.num (frameAt word).child.den x := by
    have h' := hxE1
    rw [FLatticePaper.W1.closedPolygon_eq_closedRect (frameAt word)] at h'
    exact h'
  have hxuR : closedRect (frameAt word).child.num (frameAt word).child.den (x.1 + eD, x.2 + eN) := by
    have h' := hxE2
    rw [FLatticePaper.W1.closedPolygon_eq_closedRect (frameAt word)] at h'
    exact h'
  have hvv := FLatticePaper.W4FloorArc.native_V_arc h hg hne
  have hpar : EvenSite (x.1 + eD, x.2 + eN) ↔ EvenSite x := by
    unfold EvenSite
    simp only
    omega
  have hxv_par : EvenSite x ↔ EvenSite (-g.2, g.1 - 1) := by
    have e : x.1 + x.2 = (-g.2 + g.1 - 1) + 2 * (D * c2 + N * c2) := by
      rw [hxv]
      ring
    unfold EvenSite
    simp only
    omega
  have hsx : FLatticePaper.W1.w1s n d x = FLatticePaper.W1.w1s n d (-g.2, g.1 - 1) +
      2 * c2 * (D * (d + n) + N * (d - n)) := by
    unfold FLatticePaper.W1.w1s
    rw [hxv]
    ring
  have hsu : FLatticePaper.W1.w1s n d (x.1 + eD, x.2 + eN) =
      FLatticePaper.W1.w1s n d x + ((d * d + 2 * d * n - n * n) - 2 * (D * (d + n) + N * (d - n))) := by
    unfold FLatticePaper.W1.w1s
    rw [hcd, hcn]
    ring
  have hTd : (d + n) * eD + (d - n) * eN = (d * d + 2 * d * n - n * n) - 2 * (D * (d + n) + N * (d - n)) := by
    rw [hcd, hcn]
    ring
  have hC : d + n ≤ D * (d + n) + N * (d - n) := by nlinarith
  have hnd' : n + 2 ≤ d := by omega
  have hn1 : 1 ≤ n := by omega
  have hk01 : 0 ≤ c2 ∧ c2 ≤ 1 := by
    by_cases hvE : EvenSite (-g.2, g.1 - 1)
    · have hxEv : EvenSite x := hxv_par.mpr hvE
      have hxuEv : EvenSite (x.1 + eD, x.2 + eN) := hpar.mpr hxEv
      unfold closedRect at hxR hxuR
      rw [if_pos hxEv] at hxR
      rw [if_pos hxuEv] at hxuR
      have hvb := hvv
      unfold FLatticePaper.W1.w1c FLatticePaper.W1.w1h at hvb
      rw [if_pos hvE, if_pos hvE] at hvb
      have hx0 : 0 ≤ FLatticePaper.W1.w1s n d (-g.2, g.1 - 1) + 2 * c2 * (D * (d + n) + N * (d - n)) := by
        rw [← hsx]
        exact hxR.2.2.1
      have hu1 : FLatticePaper.W1.w1s n d (-g.2, g.1 - 1) + 2 * c2 * (D * (d + n) + N * (d - n)) +
          ((d * d + 2 * d * n - n * n) - 2 * (D * (d + n) + N * (d - n))) ≤ (d * d + 2 * d * n - n * n) + 2 * n := by
        have := hxuR.2.2.2
        rw [hsu, hsx] at this
        unfold FLatticePaper.W1.w1T at this
        linarith
      exact FLatticePaper.W4FloorArc.k_even_bounds hn1 hnd' hC hvb.1 hvb.2 hx0 hu1
    · have hxEv : ¬ EvenSite x := fun h' => hvE (hxv_par.mp h')
      have hxuEv : ¬ EvenSite (x.1 + eD, x.2 + eN) := fun h' => hxEv (hpar.mp h')
      unfold closedRect at hxR hxuR
      rw [if_neg hxEv] at hxR
      rw [if_neg hxuEv] at hxuR
      have hvb := hvv
      unfold FLatticePaper.W1.w1c FLatticePaper.W1.w1h at hvb
      rw [if_neg hvE, if_neg hvE] at hvb
      have hx0 : 2 - d + n ≤ FLatticePaper.W1.w1s n d (-g.2, g.1 - 1) + 2 * c2 * (D * (d + n) + N * (d - n)) := by
        rw [← hsx]
        exact hxR.2.2.1
      have hu1 : FLatticePaper.W1.w1s n d (-g.2, g.1 - 1) + 2 * c2 * (D * (d + n) + N * (d - n)) +
          ((d * d + 2 * d * n - n * n) - 2 * (D * (d + n) + N * (d - n))) ≤ (d * d + 2 * d * n - n * n) + d + n - 2 := by
        have := hxuR.2.2.2
        rw [hsu, hsx] at this
        unfold FLatticePaper.W1.w1T at this
        linarith
      exact FLatticePaper.W4FloorArc.k_odd_bounds hn1 hnd' hC hvb.1 hvb.2 hx0 hu1
  -- the value of `B` at `c`: `B = 1 + ε − D'_ε(zTurn x)`, and `zTurn x = (I − g) + c₂ V'`
  have hcs : c - (frameAt word).sheetShift = x := by
    rw [hcx]
    ring
  have hBeq := FLatticePaper.W4OfferB.BOffer_eq_one_add_eps_sub_slip h hSE c
  rw [hcs] at hBeq
  have hzx : (-x.2, x.1 - 1) = reflectionI - g + (c2 * (-2 * N), c2 * (2 * D)) := by
    rw [hxv]
    unfold reflectionI
    refine Prod.ext ?_ ?_ <;> simp <;> ring
  rw [hzx] at hBeq
  rw [hBeq] at hB
  have hc2 : c2 = 0 ∨ c2 = 1 := by omega
  rcases hc2 with rfl | rfl
  · have hpt : reflectionI - g + ((0 : ℤ) * (-2 * N), (0 : ℤ) * (2 * D)) = reflectionI - g := by
      ext <;> simp
    rw [hpt, slip_I_sub_zero h hSE hX hSE' hg] at hB
    rcases hεu with hεu | hεu
    · have hsh0 : (frameAt word).sheetShift = (0, 0) := by
        rw [hshift, hphase, hεu]
        ext <;> simp
      have hcv : c = (-g.2, g.1 - 1) := by
        rw [hcx, hsh0, hxv]
        ext <;> simp
      have hvb : FLatticePaper.W1.w1s n d c ≤ FLatticePaper.W1.w1h n d c := by
        rw [hcv]
        exact hvv.2
      exact FLatticePaper.W4Boundary.not_strict_of_s_le_h n d c hvb hSI
    · rw [hεu] at hB
      norm_num at hB
  · have hpt : reflectionI - g + ((1 : ℤ) * (-2 * N), (1 : ℤ) * (2 * D)) =
        reflectionI - g + (-2 * N, 2 * D) := by
      ext <;> simp
    rw [hpt, slip_I_sub_add_V h hSE hX hSE' hg] at hB
    rcases hεu with hεu | hεu
    · rw [hεu] at hB
      norm_num at hB
    · have hsh1 : (frameAt word).sheetShift = (eD, eN) := by
        rw [hshift, hphase, hεu]
        norm_num
      have hcv : c = (-g.2 + d, g.1 - 1 + n) := by
        rw [hcx, hsh1, hxv, hcd, hcn]
        ext <;> simp <;> ring
      have hdn'' : (d + n) % 2 = 0 := by omega
      rw [hcv] at hSI
      exact FLatticePaper.W4Boundary.not_strict_of_shift_U n d hdn'' (-g.2, g.1 - 1) hvv.1 hSI

/-- `reflH hFirst = hLast` (the reflection exchanges the two ends of the H arc). -/
theorem reflH_hFirst (frame : ChildFrame) :
    FLatticePaper.ReflectedFan.reflH frame hFirst = frame.hLast := by
  unfold FLatticePaper.ReflectedFan.reflH ChildFrame.hLast hFirst
  ext <;> simp

/-- **The free-tail case with `a(c) = 1` (Q35, all free tails).** The free tail of `Z(c − lv)` is a conjugate free H point `h`
(old V, with `g = reflH h`, `g = hFirst`: `j = 0`; `g = hLast` with `ε = 1`: the exceptional endpoint; otherwise the guard) or a
conjugate free V point (old H, `oldH_star_jumpA'`). Each case gives `a(i) ≠ 0`, contradicting `a(i) = 0`. -/
theorem freeTail_a1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hX : ∃ x ∈ conjWord word, x ≠ Digit.three) (hSE' : StrongEstimates (conjWord (conjWord word)))
    (hTr : FLatticePaper.TraceFromPsi.TraceAt (conjWord word))
    {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hPres : ∀ c : Site, FreeClosure.freeClosure (frameAt (conjWord word)) c →
      laplacian (standardField (conjWord word)) c = 0 →
      ∀ j : Site, P.retained c j ↔ FreePolicy.FreePresc (frameAt (conjWord word)) (frameAt word).eps c j)
    {c i : Site}
    (hwc : laplacian (standardField (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) = 0)
    (hSI : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hc : c ∈ (frameAt word).closedPolygon) (hcu : c + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hpol : parentPolicy P (c - (frameAt word).sheetShift) (i - (frameAt word).sheetShift))
    (hEdge : Edge i c)
    (hmem : ∃ v ∈ (frameAt (conjWord word)).child.modifiedDeck.span,
      zTurn (c - (frameAt word).sheetShift) + v ∈
        (frameAt (conjWord word)).freeH ∪ (frameAt (conjWord word)).freeV)
    (ha1 : FLatticePaper.W4Reduction.aJump word c = 1)
    (h0 : FLatticePaper.W4Reduction.aJump word i = 0)
    (hB : 1 ≤ FLatticePaper.W4Reduction.BOffer word c) : False := by
  obtain ⟨v, hv, hmem⟩ := hmem
  obtain ⟨i', j', hvij⟩ := hv
  have hsn : EvenSite (-(frameAt word).sheetShift) := by
    have hs := evenSite_sheetShift (word := word)
    unfold EvenSite at hs ⊢
    simp only [Prod.fst_neg, Prod.snd_neg]
    omega
  have hajc := FLatticePaper.W4FreeTail.aJump_eq_jumpA word c
  have haji := FLatticePaper.W4FreeTail.aJump_eq_jumpA word i
  rw [hajc] at ha1
  rw [haji] at h0
  have hEdge' : Edge (i - (frameAt word).sheetShift) (c - (frameAt word).sheetShift) := by
    have := edge_add_even hsn hEdge
    simpa [sub_eq_add_neg] using this
  have hcx : c = (c - (frameAt word).sheetShift) + (frameAt word).sheetShift := by ring
  set x := c - (frameAt word).sheetShift with hxdef
  rcases hmem with hH | hV
  · -- the free H case: `g = reflH (zTurn x + v)` is a native free H label, `zTurn x = reflH g + combine(−i', −j')`
    set h0' := zTurn x + v with hh0def
    set g := FLatticePaper.ReflectedFan.reflH (frameAt (conjWord word)) h0' with hgdef
    have hg : g ∈ (frameAt (conjWord word)).freeH := reflH_conj_mem_freeH hH
    have hgg : FLatticePaper.ReflectedFan.reflH (frameAt (conjWord word)) g = zTurn x + v :=
      FLatticePaper.ReflectedFan.reflH_reflH _ _
    have hroot : zTurn x = FLatticePaper.ReflectedFan.reflH (frameAt (conjWord word)) g +
        ((-i') * (frameAt (conjWord word)).child.modifiedDeck.kernel.1 +
            (-j') * (frameAt (conjWord word)).child.modifiedDeck.transverse.1,
          (-i') * (frameAt (conjWord word)).child.modifiedDeck.kernel.2 +
            (-j') * (frameAt (conjWord word)).child.modifiedDeck.transverse.2) := by
      rw [hgg, hvij]
      unfold PeriodDeck.combine
      refine Prod.ext ?_ ?_ <;> simp <;> ring
    have hA := FLatticePaper.W4OldV.oldV_jumpA_of_trace h hSE hTr (-i') (-j') x hg hroot
    rw [hA] at ha1
    by_cases hgF : g = ((1 : ℤ), (0 : ℤ))
    · -- `j = 0`: the east target (`oldV_bottom_jumpA_policy`)
      rw [if_pos hgF] at ha1
      have hR : FLatticePaper.ReflectedFan.reflH (frameAt (conjWord word)) g = (frameAt (conjWord word)).hLast := by
        rw [hgF]
        exact reflH_hFirst _
      have hxb : zTurn x = ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num,
          (frameAt word).parents.odd.den - (frameAt word).parents.odd.num - 1) +
        ((-i') * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) +
            (-j') * (-2 * (frameAt word).parents.odd.num),
          (-i') * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) +
            (-j') * (2 * (frameAt word).parents.odd.den)) := by
        rw [hroot, hR, FLatticePaper.W4OldV.conj_hLast_eq h, W4OldH.conj_kernel_eq h, W4OldH.conj_transverse_eq h]
      have hbot := FLatticePaper.W4OldV.oldV_bottom_jumpA_policy h hSE P hPres (-i') (-j') x (i - (frameAt word).sheetShift)
        hxb hwc hpol
      omega
    · by_cases hgL : g = (frameAt (conjWord word)).hLast ∧ (frameAt word).eps = 1
      · -- `j = r − 1` at `ε = 1`: the exceptional endpoint
        obtain ⟨hgL, hW⟩ := hgL
        have hR : FLatticePaper.ReflectedFan.reflH (frameAt (conjWord word)) g = hFirst := by
          rw [hgL]
          exact FLatticePaper.W4Exceptional.reflH_hLast _
        have hx_exc : zTurn x = hFirst + ((-i') * (frameAt (conjWord word)).child.modifiedDeck.kernel.1 +
            (-j') * (frameAt (conjWord word)).child.modifiedDeck.transverse.1,
          (-i') * (frameAt (conjWord word)).child.modifiedDeck.kernel.2 +
            (-j') * (frameAt (conjWord word)).child.modifiedDeck.transverse.2) := by
          rw [hroot, hR]
        obtain ⟨-, -, hexA'⟩ := FLatticePaper.W4Exceptional.oldV_exceptional h hSE hTr hW P hPres (-i') (-j') x
          (i - (frameAt word).sheetShift) hx_exc hwc hpol
        omega
      · -- ordinary `g`: the guard, with `c₁ = −1` (from `a(c) = 1`)
        have hne : g ≠ (frameAt (conjWord word)).hLast ∨ (frameAt word).eps = -1 := by
          by_cases hgl : g = (frameAt (conjWord word)).hLast
          · right
            rcases (frameAt word).eps_unit with he | he
            · exact absurd ⟨hgl, he⟩ hgL
            · exact he
          · left
            exact hgl
        have hc1 : -i' = -1 := by
          rw [if_neg hgF] at ha1
          omega
        rw [hc1] at hroot
        exact oldV_guard_a1 h hSE hX hSE' hg hne (-j') hroot hcx hc hcu hSI hB
  · -- the free V case: the old H star
    have hxq : zTurn x = (zTurn x + v) + ((-i') * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) +
        (-j') * (-2 * (frameAt word).parents.odd.num),
          (-i') * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) +
            (-j') * (2 * (frameAt word).parents.odd.den)) := by
      rw [hvij]
      unfold PeriodDeck.combine
      rw [W4OldH.conj_kernel_eq h, W4OldH.conj_transverse_eq h]
      refine Prod.ext ?_ ?_ <;> simp <;> ring
    have hjx := FLatticePaper.W4OldH.oldH_star_jumpA' h hSE hV (-i') (-j') x hxq (i - (frameAt word).sheetShift) hEdge'
    omega


/-- **`NoRiseForced`, proved.** The rise `a(c) ≥ 1`, `a(i) = 0`, `B(c) ≥ 1` on a forced nonfree white: the unit price bound gives
`a(c) = 1`; a conjugate-nonfree tail is excluded by the class (i) argument (`rise_excluded_nonfree`); a free tail by `freeTail_a1`.

The caller's hypotheses, with their providers:
* `h` (the word is proper): the induction on words (the non-base case).
* `hSE : StrongEstimates (conjWord word)`: the earlier stage's estimates of the conjugate word (`StrongEstimates` of the induction).
* `hX` (the conjugate word is proper, the non-base case) and `hSE' : StrongEstimates (conjWord (conjWord word))` (the grand conjugate's
  estimates, the native slip zero `conj_slip_zero_native_H`): the same inputs as `TraceStep.traceAt_step`.
* `hTr : TraceAt (conjWord word)`: the trace induction (`TraceStep.traceAt_step`, the H-trace price on the conjugate's free H points).
* `hW1`: the conjugate's `W1Forced` (the W1 forcing of the earlier stage, `W1NonfreeHsqC.W1Forced_of_inputs`).
* `P` (the retained policy of the conjugate, with `sheetPolicyA`): the old policy of the earlier stage (`OldPolicyData`).
* `hwhite`: the conjugate's laplacian vanishes at `Z(c − lv)` for every white `c` of the word. Numerically 546/546 on the needed
  roots; not yet derived in Lean (the white condition of the retained edge).
* `hPres`: the free policy's prescription at free-closure whites (`FreePolicy.FreePresc`): the closure property of `freePolicy`.
The strictness `hSI` and the edge `Edge i c` are per-white arguments of `NoRiseForced` itself. -/
theorem noRiseForced_proved {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    (hX : ∃ x ∈ conjWord word, x ≠ Digit.three) (hSE' : StrongEstimates (conjWord (conjWord word)))
    (hTr : FLatticePaper.TraceFromPsi.TraceAt (conjWord word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hwhite : ∀ c : Site, laplacian (standardField word) c = 0 →
      laplacian (standardField (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) = 0)
    (hPres : ∀ c : Site, FreeClosure.freeClosure (frameAt (conjWord word)) c →
      laplacian (standardField (conjWord word)) c = 0 →
      ∀ j : Site, P.retained c j ↔ FreePolicy.FreePresc (frameAt (conjWord word)) (frameAt word).eps c j) :
    FLatticePaper.W4Reduction.NoRiseForced P := by
  intro c i hSI hc hi hcu hiu hΨc hΨi hEdge hfor hlap hnf hret h1 h0 hB
  have hu := aJump_sub_le_one h hSE hEdge
  have ha1 : FLatticePaper.W4Reduction.aJump word c = 1 := by omega
  have hpol : parentPolicy P (c - (frameAt word).sheetShift) (i - (frameAt word).sheetShift) := hret
  by_cases hconj : FLatticePaper.Induction.Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift))
  · have h1' : 1 ≤ jumpA (frameAt word) (quarterTurnField (standardField (conjWord word)))
        (c - (frameAt word).sheetShift) := by
      rw [← FLatticePaper.W4FreeTail.aJump_eq_jumpA]
      exact h1
    have h0' : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word)))
        (i - (frameAt word).sheetShift) = 0 := by
      rw [← FLatticePaper.W4FreeTail.aJump_eq_jumpA]
      exact h0
    exact FLatticePaper.W4FreeTail.rise_excluded_nonfree h hSE P hW1 hconj hpol h1' h0'
  · unfold FLatticePaper.Induction.Nonfree at hconj
    push Not at hconj
    exact freeTail_a1 h hSE hX hSE' hTr P hPres (hwhite c hlap) hSI hc hcu hpol hEdge hconj ha1 h0 hB

end FLatticePaper.W4Guard
