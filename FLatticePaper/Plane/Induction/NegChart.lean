import FLatticePaper.Plane.Induction.SlipReflect

/-! Task 69 (a): the A-case for `−σ` (the negative sign of the slip).

For a rising pair `(c, i)` for `−σ` with both `Ψ ≥ 1`, the reflection `R` gives a rising pair for `σ` at `(Rc, Ri)`, so the
exit cases are the lower-exit lemmas of the `σ`-cover at the reflected pair, and the common chart is the `σ`-common chart
transported by `R` (`common_chart_option` at `(Rc, Ri)`). Two options remain:
* first chart, `c − σ ∈ E`: `F (c − σ) = min (A c, C c + 2) = A c`, so `D_−(c) = 0` is even and cannot rise;
* negative chart, `c + εU_q ∈ E`: `F (z − σ) = F (z + εU_q)` (the `U`-period of `F`), so the rise is
  `min (a c, B c) − min (a i, B i) = 1` with `a z = A (z + εU_q) − A z`, `B z = C (z + εU_q) − A z`. With the unit bound
  `0 ≤ a ≤ 1` and the monotonicity of `B` along the retained edge, the rise forces `a c = 1`, `a i = 0` on a retained edge,
  which `nonfree_drop_excluded` excludes.

Named leaves (the two paper facts): `hG1`, the parent polygon contains `zTurn (I − (z − l_v))` for `z ∈ E` (with the price
range this is the unit bound), and `hbmono`, the raw slip `B` does not decrease along the matched edges. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The shift `εU_q = ε (d_q, n_q)` of the even parent (the shift of the negative chart). -/
def ChildFrame.uq (frame : ChildFrame) : Site :=
  (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num)

theorem ChildFrame.tGrade_neg (frame : ChildFrame) (x : Site) : frame.tGrade (-x) = -frame.tGrade x := by
  unfold ChildFrame.tGrade
  simp only [Prod.fst_neg, Prod.snd_neg]
  ring

theorem ChildFrame.tGrade_neg_shortShift (frame : ChildFrame) : frame.tGrade (-frame.shortShift) = 2 := by
  rw [frame.tGrade_neg, frame.tGrade_shortShift]
  norm_num

/-- `z − σ = (z + εU_q) − εU`, i.e. `z − σ = (z + εU_q) + shiftU (−ε)` (for any integer `ε`). -/
theorem ChildFrame.sub_shortShift_eq (frame : ChildFrame) (z : Site) :
    z - frame.shortShift = (z + frame.uq) + frame.shiftU (-frame.eps) := by
  obtain ⟨hd, hn, -⟩ := frame.linear_facts
  unfold ChildFrame.shortShift ChildFrame.uq ChildFrame.shiftU
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sub, Prod.fst_add]
    rw [hd]
    ring
  · simp only [Prod.snd_sub, Prod.snd_add]
    rw [hn]
    ring

/-- `F (z − σ) = F (z + εU_q)`: the `U`-period of `F` (constant `0`). -/
theorem ChildFrame.F_sub_shortShift {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (z : Site) :
    F (z - frame.shortShift) = F (z + frame.uq) := by
  rw [frame.sub_shortShift_eq z, frame.F_add_shiftU hP]

theorem ChildFrame.reflect_sub_add (frame : ChildFrame) (c τ : Site) :
    frame.centre - (frame.centre - c + τ) = c - τ := by
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sub, Prod.fst_add]
    ring
  · simp only [Prod.snd_sub, Prod.snd_add]
    ring

theorem ChildFrame.reflect_sub_sub (frame : ChildFrame) (c τ : Site) :
    frame.centre - (frame.centre - c - τ) = c + τ := by
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sub, Prod.fst_add]
    ring
  · simp only [Prod.snd_sub, Prod.snd_add]
    ring

theorem ChildFrame.reflect_mem_iff (frame : ChildFrame) {w : Site} :
    frame.centre - w ∈ frame.closedPolygon ↔ w ∈ frame.closedPolygon := by
  constructor
  · intro hw
    have := frame.reflect_mem_closedPolygon hw
    rwa [sub_sub_cancel] at this
  · exact frame.reflect_mem_closedPolygon

/-- The general reflected slip: `D_{−τ}(R z) = D_τ(z) + tGrade τ` (for `τ = σ`, `tGrade σ = −2`). -/
theorem ChildFrame.slip_reflect_gen {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (τ z : Site) :
    F (frame.centre - z) - F (frame.centre - z + -τ) = (F z - F (z + τ)) + frame.tGrade τ := by
  have e : frame.centre - z + -τ = frame.centre - (z + τ) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_sub, Prod.fst_neg]
      ring
    · simp only [Prod.snd_add, Prod.snd_sub, Prod.snd_neg]
      ring
  rw [e, hP.reflection z, hP.reflection (z + τ), frame.tGrade_add z τ]
  ring

/-- A rising pair for `τ` (with `tGrade τ` even) reflects to a rising pair for `−τ`. -/
theorem ChildFrame.rising_reflect_gen {G : Field} (frame : ChildFrame) (hP : frame.Packet G) (τ : Site)
    (hτ : frame.tGrade τ % 2 = 0) {c i : Site} (hr : RisingBlackPair G τ c i) :
    RisingBlackPair G (-τ) (frame.centre - c) (frame.centre - i) := by
  obtain ⟨hin, hlap, hpar, hlap', hslip⟩ := hr
  have e : frame.centre - c + -τ = frame.centre - (c + τ) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_sub, Prod.fst_neg]
      ring
    · simp only [Prod.snd_add, Prod.snd_sub, Prod.snd_neg]
      ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hin with h1 | h1
    · right
      rw [h1]
      exact frame.reflect_input_neg c
    · left
      rw [h1]
      exact frame.reflect_input_pos c
  · rw [frame.laplacian_reflect hP]
    exact hlap
  · rw [frame.slip_reflect_gen hP τ c]
    omega
  · rw [e, frame.laplacian_reflect hP]
    exact hlap'
  · unfold slipIncrement at hslip ⊢
    dsimp only at hslip ⊢
    rw [frame.slip_reflect_gen hP τ i, frame.slip_reflect_gen hP τ c]
    linarith

/-- A rising pair for `−σ` reflects to a rising pair for `σ`. -/
theorem ChildFrame.rising_reflect_neg {G : Field} (frame : ChildFrame) (hP : frame.Packet G) {c i : Site}
    (hr : RisingBlackPair G (-frame.shortShift) c i) :
    RisingBlackPair G frame.shortShift (frame.centre - c) (frame.centre - i) := by
  have h := frame.rising_reflect_gen hP (-frame.shortShift) (by simp [frame.tGrade_neg_shortShift]) hr
  rwa [neg_neg] at h

/-- `A` is `σ`-periodic. -/
theorem sheetA_sub_shortShift {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (z : Site) :
    (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (z - (frameAt word).shortShift) =
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z := by
  have := sheetA_add_shortShift h hSE (z - (frameAt word).shortShift)
  rw [sub_add_cancel] at this
  exact this.symm

/-- `C (z − σ) = C z + 2`. -/
theorem sheetC_sub_shortShift {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (z : Site) :
    (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (z - (frameAt word).shortShift) =
      (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) z + 2 := by
  have := sheetC_add_shortShift h hSE (z - (frameAt word).shortShift)
  rw [sub_add_cancel] at this
  omega

/-- The jump of the sheet `A` over `εU_q` is the jump of the parent field at `z − l_v`. -/
theorem sheetA_uq_eq_jumpA {word : Word} (z : Site) :
    (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (z + (frameAt word).uq) -
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z =
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word)))
        (z - (frameAt word).sheetShift) := by
  unfold ChildFrame.sheetA jumpA
  have e : z + (frameAt word).uq - (frameAt word).sheetShift =
      (z - (frameAt word).sheetShift) +
        ((frameAt word).eps * (frameAt word).parents.even.den,
          (frameAt word).eps * (frameAt word).parents.even.num) := by
    refine Prod.ext ?_ ?_
    · simp only [ChildFrame.uq, Prod.fst_sub, Prod.fst_add]
      ring
    · simp only [ChildFrame.uq, Prod.snd_sub, Prod.snd_add]
      ring
  rw [e]

/-- The unit bound `0 ≤ A (z + εU_q) − A z ≤ 1` for `z ∈ E`, from the parent polygon (leaf `hG1`) and the price range. -/
theorem unit_of_polygon {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {z : Site}
    (hG1 : zTurn ((1, -1) - (z - (frameAt word).sheetShift)) ∈ (frameAt (conjWord word)).closedPolygon) :
    0 ≤ (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (z + (frameAt word).uq) -
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z ∧
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (z + (frameAt word).uq) -
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z ≤ 1 := by
  rw [sheetA_uq_eq_jumpA, jumpA_eq_cutPrice h hSE]
  have hp := hSE.priceRange _ hG1
  constructor <;> linarith [hp.1, hp.2]

/-- The retention for a black centre with `Ψ ≥ 1` (the argument of `sheetPolicyA_of_strict`, for either sign). -/
theorem sheetPolicyA_of_black {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    {c i : Site} (hc : c ∈ (frameAt word).closedPolygon) (hEdge : Edge i c)
    (hb : laplacian (standardField word) c = -1) (hΨc : 1 ≤ sheetDiffW word c) :
    sheetPolicyA P (frameAt word).sheetShift c i := by
  have hlv : EvenSite (frameAt word).sheetShift := (frameAt word).evenSite_sheetShift
  have hinN : Edge (FLatticePaper.incomingNeg c) c := Or.inl rfl
  have hinP : Edge (FLatticePaper.incomingPos c) c := Or.inr rfl
  have hEN := (frameAt word).black_input_mem hpk hc hb hinN
  have hEP := (frameAt word).black_input_mem hpk hc hb hinP
  have hΨc' : 1 ≤ (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) c -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c := hΨc
  have hMc := sheetMin_A_at_input (frameAt word) (quarterTurnField (standardField (conjWord word)))
    (i := c) hΨc' (by omega)
  have hMN := sheetMin_A_of_strict_root h hSE hinN hΨc
  have hMP := sheetMin_A_of_strict_root h hSE hinP hΨc
  have hFc := standardField_eq_sheetMin_of_strong h hSE hc
  have hFN := standardField_eq_sheetMin_of_strong h hSE hEN
  have hFP := standardField_eq_sheetMin_of_strong h hSE hEP
  have hlapF : laplacian (standardField word) c =
      laplacian ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word)))) c := by
    unfold laplacian
    rw [hFc, hFN, hFP, hMc, hMN, hMP]
  have hshiftLap : laplacian ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word)))) c =
      laplacian (quarterTurnField (standardField (conjWord word))) (c - (frameAt word).sheetShift) :=
    laplacian_sub_even (quarterTurnField (standardField (conjWord word))) (frameAt word).sheetShift hlv c
  have hq : laplacian (quarterTurnField (standardField (conjWord word))) (c - (frameAt word).sheetShift) =
      laplacian (standardField (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) :=
    i3_laplacian_quarterTurn (standardField (conjWord word)) (c - (frameAt word).sheetShift)
  have hblack : laplacian (standardField (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) = -1 := by
    rw [← hq, ← hshiftLap, ← hlapF]
    exact hb
  have hEi : Edge (i - (frameAt word).sheetShift) (c - (frameAt word).sheetShift) := by
    unfold Edge at hEdge ⊢
    rcases hEdge with h1 | h1
    · left
      rw [h1, incomingNeg_sub_even' c _ hlv]
    · right
      rw [h1, incomingPos_sub_even' c _ hlv]
  have hzE : Edge (zTurn (i - (frameAt word).sheetShift)) (zTurn (c - (frameAt word).sheetShift)) :=
    i3_edge_Z hEi
  have hret := P.quota.1 (zTurn (c - (frameAt word).sheetShift)) hblack
  dsimp only [sheetPolicyA, parentPolicy]
  unfold Edge at hzE
  rcases hzE with h2 | h2
  · rw [h2]
    exact hret.1
  · rw [h2]
    exact hret.2

/-- The integer core of the negative chart: the rise `min (a c, B c) − min (a i, B i) = 1` with `0 ≤ a ≤ 1`, `B c ≤ B i`
forces `a c = 1` and `a i = 0`. -/
theorem neg_chart_arith (Ac Ai Ac1 Ai1 Cc1 Ci1 mc mi : ℤ)
    (hmc1 : mc ≤ Ac1) (hmc2 : mc ≤ Cc1)
    (hmi3 : mi = Ai1 ∨ mi = Ci1)
    (hac0 : 0 ≤ Ac1 - Ac) (hac1 : Ac1 - Ac ≤ 1) (hai0 : 0 ≤ Ai1 - Ai) (hai1 : Ai1 - Ai ≤ 1)
    (hb : Cc1 - Ac ≤ Ci1 - Ai)
    (hrise : (Ai - mi) - (Ac - mc) = 1) :
    Ac1 - Ac = 1 ∧ Ai1 - Ai = 0 := by
  omega

/-- The first chart for `−σ`: with `c − σ ∈ E` and `Ψ c ≥ 1`, the centre has `D_−(c) = 0` (even), so it cannot rise. -/
theorem neg_first_excluded {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    {c i : Site} (hr : RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i)
    (hcE : c ∈ (frameAt word).closedPolygon) (hcq : c - (frameAt word).shortShift ∈ (frameAt word).closedPolygon)
    (hΨc : 1 ≤ sheetDiffW word c) : False := by
  have hΨ' : 1 ≤ (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) c -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c := hΨc
  have hFc : standardField word c =
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c := by
    rw [standardField_eq_sheetMin_of_strong h hSE hcE]
    exact sheetMin_A_at_input (frameAt word) (quarterTurnField (standardField (conjWord word)))
      (i := c) hΨ' (by omega)
  have hFq : standardField word (c - (frameAt word).shortShift) =
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c := by
    rw [standardField_eq_sheetMin_of_strong h hSE hcq]
    unfold ChildFrame.sheetMin
    rw [sheetA_sub_shortShift h hSE c, sheetC_sub_shortShift h hSE c]
    exact min_eq_left (by omega)
  have hpar := hr.2.2.1
  rw [← sub_eq_add_neg, hFc, hFq, sub_self] at hpar
  norm_num at hpar

/-- The negative chart for `−σ` with `c + εU_q, i + εU_q ∈ E`: the rise forces the jump `a` from `1` to `0` on the retained
edge `(c − l_v, i − l_v)`, which `nonfree_drop_excluded` excludes. -/
theorem neg_adjacent_excluded {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (hG1 : ∀ z ∈ (frameAt word).closedPolygon,
      zTurn ((1, -1) - (z - (frameAt word).sheetShift)) ∈ (frameAt (conjWord word)).closedPolygon)
    (hbmono : ∀ c i, Edge i c → sheetPolicyA P (frameAt word).sheetShift c i →
      (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (c + (frameAt word).uq) -
          (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c ≤
        (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (i + (frameAt word).uq) -
          (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i)
    {c i : Site} (hr : RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i)
    (hcE : c ∈ (frameAt word).closedPolygon) (hiE : i ∈ (frameAt word).closedPolygon)
    (hcu : c + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hiu : i + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hΨc : 1 ≤ sheetDiffW word c) (hΨi : 1 ≤ sheetDiffW word i) : False := by
  have hΨc' : 1 ≤ (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) c -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c := hΨc
  have hΨi' : 1 ≤ (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) i -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i := hΨi
  -- the standard field is the sheet minimum on `E`
  have hG : ∀ z ∈ (frameAt word).closedPolygon,
      standardField word z = min ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z)
        ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) z) := fun z hz =>
    standardField_eq_sheetMin_of_strong h hSE hz
  have hFc : standardField word c =
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c := by
    rw [hG c hcE]
    exact min_eq_left (by omega)
  have hFi : standardField word i =
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i := by
    rw [hG i hiE]
    exact min_eq_left (by omega)
  -- the rise `D_−(i) − D_−(c) = 1`, with `D_−(z) = F z − F (z − σ) = F z − F (z + εU_q)`
  have hrise := hr.2.2.2.2
  unfold slipIncrement at hrise
  dsimp only at hrise
  have e1 : c + -(frameAt word).shortShift = c - (frameAt word).shortShift :=
    (sub_eq_add_neg c _).symm
  have e2 : i + -(frameAt word).shortShift = i - (frameAt word).shortShift :=
    (sub_eq_add_neg i _).symm
  rw [e1, e2, (frameAt word).F_sub_shortShift hpk c, (frameAt word).F_sub_shortShift hpk i, hFc, hFi,
    hG _ hcu, hG _ hiu] at hrise
  -- the unit bounds and the monotonicity of `B` along the retained edge
  obtain ⟨hac0, hac1⟩ := unit_of_polygon h hSE (hG1 c hcE)
  obtain ⟨hai0, hai1⟩ := unit_of_polygon h hSE (hG1 i hiE)
  have hret : sheetPolicyA P (frameAt word).sheetShift c i :=
    sheetPolicyA_of_black h hSE hpk P hcE hr.1 hr.2.1 hΨc
  have hb := hbmono c i hr.1 hret
  obtain ⟨h1, h0⟩ := neg_chart_arith
    ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c)
    ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i)
    ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (c + (frameAt word).uq))
    ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (i + (frameAt word).uq))
    ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (c + (frameAt word).uq))
    ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (i + (frameAt word).uq))
    (min ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (c + (frameAt word).uq))
      ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (c + (frameAt word).uq)))
    (min ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (i + (frameAt word).uq))
      ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (i + (frameAt word).uq)))
    (min_le_left _ _) (min_le_right _ _) (min_choice _ _)
    hac0 hac1 hai0 hai1 hb hrise
  have j1 : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word)))
      (c - (frameAt word).sheetShift) = 1 := by
    rw [← sheetA_uq_eq_jumpA c]
    exact h1
  have j0 : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word)))
      (i - (frameAt word).sheetShift) = 0 := by
    rw [← sheetA_uq_eq_jumpA i]
    exact h0
  exact nonfree_drop_excluded (x := c - (frameAt word).sheetShift) (x' := i - (frameAt word).sheetShift)
    h hSE P hret j1 j0

/-- **The A-case for `−σ` (task 69 (a)).** A rising `−σ` pair with centre in `E` and both `Ψ ≥ 1` is impossible, given
the two named leaves `hG1` (the parent polygon) and `hbmono` (the monotonicity of the raw slip). -/
theorem neg_sign_excluded {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (hG1 : ∀ z ∈ (frameAt word).closedPolygon,
      zTurn ((1, -1) - (z - (frameAt word).sheetShift)) ∈ (frameAt (conjWord word)).closedPolygon)
    (hbmono : ∀ c i, Edge i c → sheetPolicyA P (frameAt word).sheetShift c i →
      (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (c + (frameAt word).uq) -
          (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c ≤
        (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (i + (frameAt word).uq) -
          (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i)
    {c i : Site} (hr : RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i)
    (hcE : c ∈ (frameAt word).closedPolygon) (hΨc : 1 ≤ sheetDiffW word c) (hΨi : 1 ≤ sheetDiffW word i) :
    False := by
  have hn3 : 3 ≤ (frameAt word).child.num := child_num_ge_three h
  have hnd : (frameAt word).child.num + 2 ≤ (frameAt word).child.den := by
    have := (frameAt word).child_facts.2.2.1
    omega
  have hiE : i ∈ (frameAt word).closedPolygon := (frameAt word).black_input_mem hpk hcE hr.2.1 hr.1
  have hr' := (frameAt word).rising_reflect_neg hpk hr
  have hcE' := (frameAt word).reflect_mem_closedPolygon hcE
  have hiE' := (frameAt word).reflect_mem_closedPolygon hiE
  by_cases hnc : (frameAt word).tGrade ((frameAt word).centre - c) - 2 ≥
      (if EvenSite ((frameAt word).centre - c) then 2 else (frameAt word).child.num) -
        (frameAt word).child.periodDenominator
  · by_cases hni : (frameAt word).tGrade ((frameAt word).centre - i) - 2 ≥
        (if EvenSite ((frameAt word).centre - i) then 2 else (frameAt word).child.num) -
          (frameAt word).child.periodDenominator
    · rcases common_chart_option (frameAt word) hn3 hnd hcE' hiE' hr'.1 hnc hni with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · -- the first option: `c − σ ∈ E`
        have hcq : c - (frameAt word).shortShift ∈ (frameAt word).closedPolygon := by
          have h3 := (frameAt word).reflect_mem_iff.mpr h1
          rwa [(frameAt word).reflect_sub_add c (frameAt word).shortShift] at h3
        exact neg_first_excluded h hSE hr hcE hcq hΨc
      · -- the negative option: `c + εU_q ∈ E`
        have hcu : c + (frameAt word).uq ∈ (frameAt word).closedPolygon := by
          have h3 := (frameAt word).reflect_mem_iff.mpr h1
          rw [(frameAt word).reflect_sub_sub c
            ((frameAt word).eps * (frameAt word).parents.even.den,
              (frameAt word).eps * (frameAt word).parents.even.num)] at h3
          exact h3
        have hiu : i + (frameAt word).uq ∈ (frameAt word).closedPolygon := by
          have h3 := (frameAt word).reflect_mem_iff.mpr h2
          rw [(frameAt word).reflect_sub_sub i
            ((frameAt word).eps * (frameAt word).parents.even.den,
              (frameAt word).eps * (frameAt word).parents.even.num)] at h3
          exact h3
        exact neg_adjacent_excluded h hSE hpk P hG1 hbmono hr hcE hiE hcu hiu hΨc hΨi
    · exact (frameAt word).not_rising_of_input_exit hpk hn3 hnd ⟨hcE', hiE', hr'.1, not_le.mp hni⟩ hr'
  · exact (frameAt word).not_rising_of_centre_exit hpk hn3 hnd ⟨hcE', hiE', hr'.1, not_le.mp hnc⟩ hr'

/-- `NoBlackPairRise` from the A-case for `σ` (proved), the A-case for `−σ` (this file, given the leaves `hG1`, `hbmono`)
and the tie leaf `hTie` (task 69 (b)). -/
theorem noBlackPairRise_of_leaves {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (hG1 : ∀ z ∈ (frameAt word).closedPolygon,
      zTurn ((1, -1) - (z - (frameAt word).sheetShift)) ∈ (frameAt (conjWord word)).closedPolygon)
    (hbmono : ∀ c i, Edge i c → sheetPolicyA P (frameAt word).sheetShift c i →
      (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (c + (frameAt word).uq) -
          (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c ≤
        (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (i + (frameAt word).uq) -
          (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i)
    (hTie : ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
      c ∈ (frameAt word).closedPolygon → (sheetDiffW word c = 0 ∨ sheetDiffW word i = 0) → False) :
    NoBlackPairRise (standardField word) (frameAt word).shortShift :=
  noBlackPairRise_of_signs h hSE hpk P
    (fun _ _ hr hc hΨc hΨi => neg_sign_excluded h hSE hpk P hG1 hbmono hr hc hΨc hΨi) hTie

end FLatticePaper.Induction
