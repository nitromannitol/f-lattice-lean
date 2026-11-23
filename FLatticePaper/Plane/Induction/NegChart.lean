import FLatticePaper.Plane.Induction.RawB

/-! Task 69 (a)/(b): the A-case for `−σ` (the negative sign of the slip).

For a rising pair `(c, i)` for `−σ` with both `Ψ ≥ 1`, the reflection `R` gives a rising pair for `σ` at `(Rc, Ri)`, so the
exit cases are the lower-exit lemmas of the `σ`-cover at the reflected pair, and the common chart is the `σ`-common chart
transported by `R` (`common_chart_option` at `(Rc, Ri)`). Two options remain:
* first chart, `c − σ ∈ E`: `F (c − σ) = min (A c, C c + 2) = A c`, so `D_−(c) = 0` is even and cannot rise;
* negative chart, `c + εU_q ∈ E`: `F (z − σ) = F (z + εU_q)` (the `U`-period of `F`), so the rise is
  `min (a c, B c) − min (a i, B i) = 1` with `a z = A (z + εU_q) − A z`, `B z = C (z + εU_q) − A z`. The unit increments of
  `a` come from `HasUnitPrice` (`a_unit_bound`); the monotonicity `B c ≤ B i` on the retained edge comes from the policy's
  raw-slip field (`hbmono_of_raw`). The slip values `D_−(c) = −1`, `D_−(i) = 0` come from the word's slip range `hslip`. Then the rise forces
  `a c = 1`, `a i = 0` on a retained edge, which `nonfree_drop_excluded` excludes.

Named leaf: `hslip`, the slip range of the word's standard field on `E` (`D_+ ∈ [0, 2]`, the slip fields of the word;
its reflection gives `D_− ∈ [−2, 0]`). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

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

/-- The retention for a black centre with `Ψ ≥ 1` and an edge `i → c` (sign-independent: the colour argument of
`sheetPolicyA_of_strict`). -/
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

/-- Retention at a centre whose star has `Ψ ≥ 0` (ties allowed): `F = sheetA` on the star, so the colour argument of
`sheetPolicyA_of_black` applies (task 69 (b): the tied centre). -/
theorem sheetPolicyA_of_nonneg {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    {c i : Site} (hc : c ∈ (frameAt word).closedPolygon) (hEdge : Edge i c)
    (hb : laplacian (standardField word) c = -1) (hΨc : 0 ≤ sheetDiffW word c)
    (hstar : ∀ j, Edge j c → 0 ≤ sheetDiffW word j) :
    sheetPolicyA P (frameAt word).sheetShift c i := by
  have hlv : EvenSite (frameAt word).sheetShift := (frameAt word).evenSite_sheetShift
  have hinN : Edge (FLatticePaper.incomingNeg c) c := Or.inl rfl
  have hinP : Edge (FLatticePaper.incomingPos c) c := Or.inr rfl
  have hEN := (frameAt word).black_input_mem hpk hc hb hinN
  have hEP := (frameAt word).black_input_mem hpk hc hb hinP
  have hmin : ∀ j, Edge j c → (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) j =
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) j := by
    intro j hj
    have h0 : 0 ≤ (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) j -
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) j := hstar j hj
    unfold ChildFrame.sheetMin
    exact min_eq_left (by omega)
  have hMc : (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) c =
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c := by
    unfold ChildFrame.sheetMin
    have h0 : 0 ≤ (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) c -
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c := hΨc
    exact min_eq_left (by omega)
  have hMN := hmin _ hinN
  have hMP := hmin _ hinP
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

/-- The integer core of the negative chart. The rise is `min (a c, B c) − min (a i, B i) = 1` written as
`mc − Ac = 1`, `mi − Ai = 0` (the slip values `D_−(c) = −1`, `D_−(i) = 0`); with the unit increment `a c ≤ a i + 1` and
`B c ≤ B i`, the drop `a c = 1`, `a i = 0` follows. -/
theorem neg_chart_arith (Ac Ai Ac1 Ai1 Cc1 Ci1 mc mi : ℤ)
    (hmc1 : mc ≤ Ac1) (hmc2 : mc ≤ Cc1)
    (hmi3 : mi = Ai1 ∨ mi = Ci1)
    (hunit : Ac1 - Ac ≤ Ai1 - Ai + 1)
    (hb : Cc1 - Ac ≤ Ci1 - Ai)
    (hp : mc - Ac = 1) (hq : mi - Ai = 0) :
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
edge `(c − l_v, i − l_v)`, which `nonfree_drop_excluded` excludes. The slip values come from the word's slip range `hslip`
(`D_+ ∈ [0, 2]` on `E`, transported to `D_−` by the reflection), the odd parity of `D_−(c)`, and the rise. -/
theorem neg_adjacent_excluded {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (hslip : ∀ z ∈ (frameAt word).closedPolygon,
      0 ≤ standardField word z - standardField word (z + (frameAt word).shortShift) ∧
        standardField word z - standardField word (z + (frameAt word).shortShift) ≤ 2)
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
  -- the rise `D_−(i) − D_−(c) = 1` with `D_−(z) = F z − F (z − σ)`
  have e1 : c + -(frameAt word).shortShift = c - (frameAt word).shortShift :=
    (sub_eq_add_neg c _).symm
  have e2 : i + -(frameAt word).shortShift = i - (frameAt word).shortShift :=
    (sub_eq_add_neg i _).symm
  have hrise := hr.2.2.2.2
  unfold slipIncrement at hrise
  dsimp only at hrise
  rw [e1, e2] at hrise
  have hpar := hr.2.2.1
  rw [e1] at hpar
  -- the reflected slip range: `D_−(c) = D_+(R c) − 2 ∈ [−2, 0]`
  have hR := (frameAt word).slip_reflect_gen hpk (frameAt word).shortShift ((frameAt word).centre - c)
  rw [sub_sub_cancel, e1, (frameAt word).tGrade_shortShift] at hR
  obtain ⟨hr0, hr2⟩ := hslip _ ((frameAt word).reflect_mem_closedPolygon hcE)
  -- odd parity and the range give `D_−(c) = −1`; the rise then gives `D_−(i) = 0`
  have hDc : standardField word c - standardField word (c - (frameAt word).shortShift) = -1 := by
    omega
  have hDi : standardField word i - standardField word (i - (frameAt word).shortShift) = 0 := by
    omega
  have hqc : standardField word (c - (frameAt word).shortShift) =
      standardField word (c + (frameAt word).uq) := (frameAt word).F_sub_shortShift hpk c
  have hqi : standardField word (i - (frameAt word).shortShift) =
      standardField word (i + (frameAt word).uq) := (frameAt word).F_sub_shortShift hpk i
  have hp : min ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (c + (frameAt word).uq))
      ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (c + (frameAt word).uq)) -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c = 1 := by
    have := hG _ hcu
    omega
  have hq : min ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (i + (frameAt word).uq))
      ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (i + (frameAt word).uq)) -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i = 0 := by
    have := hG _ hiu
    omega
  -- the unit increment, the monotonicity of `B` along the retained edge, and the arithmetic
  have hret : sheetPolicyA P (frameAt word).sheetShift c i :=
    sheetPolicyA_of_black h hSE hpk P hcE hr.1 hr.2.1 hΨc
  have hb := hbmono_of_raw h hSE P c i hret
  have hunit := (a_unit_bound h hSE hr.1).1
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
    (by linarith [hunit]) hb hp hq
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

/-- The negative chart for `−σ` with the centre star in `Ψ ≥ 0` (ties allowed): the same drop argument, with the retention
`sheetPolicyA_of_nonneg` in place of `sheetPolicyA_of_black`. The rise forces the jump `a` from `1` to `0` on the retained
edge `(c − l_v, i − l_v)`, which `nonfree_drop_excluded` excludes. The slip values come from the word's slip range `hslip`
(`D_+ ∈ [0, 2]` on `E`, transported to `D_−` by the reflection), the odd parity of `D_−(c)`, and the rise. -/
theorem neg_adjacent_nonneg {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (hslip : ∀ z ∈ (frameAt word).closedPolygon,
      0 ≤ standardField word z - standardField word (z + (frameAt word).shortShift) ∧
        standardField word z - standardField word (z + (frameAt word).shortShift) ≤ 2)
    {c i : Site} (hr : RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i)
    (hcE : c ∈ (frameAt word).closedPolygon) (hiE : i ∈ (frameAt word).closedPolygon)
    (hcu : c + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hiu : i + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hΨc : 0 ≤ sheetDiffW word c) (hstar : ∀ j, Edge j c → 0 ≤ sheetDiffW word j) : False := by
  have hΨc' : 0 ≤ (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) c -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c := hΨc
  have hΨi' : 0 ≤ (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) i -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i := hstar i hr.1
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
  -- the rise `D_−(i) − D_−(c) = 1` with `D_−(z) = F z − F (z − σ)`
  have e1 : c + -(frameAt word).shortShift = c - (frameAt word).shortShift :=
    (sub_eq_add_neg c _).symm
  have e2 : i + -(frameAt word).shortShift = i - (frameAt word).shortShift :=
    (sub_eq_add_neg i _).symm
  have hrise := hr.2.2.2.2
  unfold slipIncrement at hrise
  dsimp only at hrise
  rw [e1, e2] at hrise
  have hpar := hr.2.2.1
  rw [e1] at hpar
  -- the reflected slip range: `D_−(c) = D_+(R c) − 2 ∈ [−2, 0]`
  have hR := (frameAt word).slip_reflect_gen hpk (frameAt word).shortShift ((frameAt word).centre - c)
  rw [sub_sub_cancel, e1, (frameAt word).tGrade_shortShift] at hR
  obtain ⟨hr0, hr2⟩ := hslip _ ((frameAt word).reflect_mem_closedPolygon hcE)
  -- odd parity and the range give `D_−(c) = −1`; the rise then gives `D_−(i) = 0`
  have hDc : standardField word c - standardField word (c - (frameAt word).shortShift) = -1 := by
    omega
  have hDi : standardField word i - standardField word (i - (frameAt word).shortShift) = 0 := by
    omega
  have hqc : standardField word (c - (frameAt word).shortShift) =
      standardField word (c + (frameAt word).uq) := (frameAt word).F_sub_shortShift hpk c
  have hqi : standardField word (i - (frameAt word).shortShift) =
      standardField word (i + (frameAt word).uq) := (frameAt word).F_sub_shortShift hpk i
  have hp : min ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (c + (frameAt word).uq))
      ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (c + (frameAt word).uq)) -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c = 1 := by
    have := hG _ hcu
    omega
  have hq : min ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (i + (frameAt word).uq))
      ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (i + (frameAt word).uq)) -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i = 0 := by
    have := hG _ hiu
    omega
  -- the unit increment, the monotonicity of `B` along the retained edge, and the arithmetic
  have hret : sheetPolicyA P (frameAt word).sheetShift c i :=
    sheetPolicyA_of_nonneg h hSE hpk P hcE hr.1 hr.2.1 hΨc hstar
  have hb := hbmono_of_raw h hSE P c i hret
  have hunit := (a_unit_bound h hSE hr.1).1
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
    (by linarith [hunit]) hb hp hq
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

/-- **The A-case for `−σ` (task 69 (a)).** A rising `−σ` pair with centre in `E` and both `Ψ ≥ 1` is impossible, given the
slip-range leaf `hslip`. -/
theorem neg_sign_excluded {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (hslip : ∀ z ∈ (frameAt word).closedPolygon,
      0 ≤ standardField word z - standardField word (z + (frameAt word).shortShift) ∧
        standardField word z - standardField word (z + (frameAt word).shortShift) ≤ 2)
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
        exact neg_adjacent_excluded h hSE hpk P hslip hr hcE hiE hcu hiu hΨc hΨi
    · exact (frameAt word).not_rising_of_input_exit hpk hn3 hnd ⟨hcE', hiE', hr'.1, not_le.mp hni⟩ hr'
  · exact (frameAt word).not_rising_of_centre_exit hpk hn3 hnd ⟨hcE', hiE', hr'.1, not_le.mp hnc⟩ hr'

/-- `NoBlackPairRise` from the A-case for `σ` (proved), the A-case for `−σ` (this file, given the slip-range leaf `hslip`) and the
tie leaf `hTie` (task 69 (b)). -/
theorem noBlackPairRise_of_leaves {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (hslip : ∀ z ∈ (frameAt word).closedPolygon,
      0 ≤ standardField word z - standardField word (z + (frameAt word).shortShift) ∧
        standardField word z - standardField word (z + (frameAt word).shortShift) ≤ 2)
    (hTie : ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
      c ∈ (frameAt word).closedPolygon → (sheetDiffW word c = 0 ∨ sheetDiffW word i = 0) → False) :
    NoBlackPairRise (standardField word) (frameAt word).shortShift :=
  noBlackPairRise_of_signs h hSE hpk P
    (fun _ _ hr hc hΨc hΨi => neg_sign_excluded h hSE hpk P hslip hr hc hΨc hΨi) hTie

end FLatticePaper.Induction
