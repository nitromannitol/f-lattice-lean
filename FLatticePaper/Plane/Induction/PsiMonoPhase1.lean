import FLatticePaper.Plane.Induction.PhaseOnePrice
import FLatticePaper.Plane.Induction.QueryClassMain
import FLatticePaper.Plane.Induction.PsiMonoMain
import FLatticePaper.Plane.Induction.FreeTraceBox
import FLatticePaper.Plane.Induction.PsiMonoOffset
import FLatticePaper.Plane.Induction.FreeHWhite

/-! Phase one: `Ψ(reflH r) ≤ Ψ(reflH (r + prescribedH η r))` for a free H root `r ≠ H_0`, in the main class.

The sheet shift is `0` in phase one. The query of `reflH r` is `q = Z(reflH r)` and the image step under `reflH (r + p)` is the prescribed
V step at sign `+1` of the native point: the image of an east step at an even root is `(0,−1)` at the odd native point, and the image of a
north step at an odd root is `(1,0)` at the even native point. -/

namespace FLatticePaper.PsiMonoPhase1

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Step FLatticePaper.FreePolicy FLatticePaper.DeckSelection
  FLatticePaper.FreeEnum FLatticePaper.PsiCalibration

/-- A free H root with first coordinate `1` is `H_0`. -/
theorem freeH_x_one_eq_hFirst (frame : ChildFrame) {r : Site} (hr : r ∈ frame.freeH) (h1 : r.1 = 1) : r = hFirst := by
  obtain ⟨hb1, hb2, hb3, hb4⟩ := FLatticePaper.Induction.FreeTraceBox.freeH_box frame hr
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  have hsp := hr.2.2
  unfold ChildFrame.hSpectrum at hsp
  unfold ChildFrame.tGrade at hsp
  have hr2 : r.2 = 0 := by
    by_contra hne
    have hpos : 1 ≤ r.2 := by omega
    have hdr : frame.child.den ≤ frame.child.den * r.2 := by nlinarith
    rw [h1] at hsp
    rcases hsp with ⟨-, h2, -⟩ | ⟨-, h2, -⟩ <;> nlinarith
  ext
  · simp [FLatticePaper.Induction.hFirst, h1]
  · simp [FLatticePaper.Induction.hFirst, hr2]

/-- **Phase one, main class.** `Ψ(reflH r) ≤ Ψ(reflH (r + prescribedH η r))` for a free H root `r ≠ H_0`, when the query of `reflH r` is a
translate of a free V point (the first branch of `transport_class`). -/
theorem psi_mono_phase1_main {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1) (hG : GamesWithRank (conjWord word))
    {base : ℤ → Site}
    (hbase : ∀ r : ℤ, 0 ≤ r → r < period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    {r : Site} (hr1 : r ≠ hFirst) (η : ℤ)
    (hmain : vAt (frameAt (conjWord word)) base (-(ArcPsi.reflH word r).2, (ArcPsi.reflH word r).1 - 1).2 =
        (-(ArcPsi.reflH word r).2, (ArcPsi.reflH word r).1 - 1)) :
    sheetPsi word (ArcPsi.reflH word r) ≤ sheetPsi word (ArcPsi.reflH word (r + (frameAt word).prescribedH η r)) := by
  have hp := period_pos (frameAt (conjWord word))
  obtain ⟨hn0, hnd, -, -, -⟩ := (frameAt word).child_facts
  obtain ⟨hco1, hco2⟩ := (frameAt word).child_odd
  have hshift : (frameAt word).sheetShift = 0 := sheetShift_W1 word hW1
  obtain ⟨K, hK⟩ := sheetDifference_identifies h hSE.packet
  have hΨ : ∀ z : Site, sheetPsi word z = K - (frameAt (conjWord word)).chainPotential
      (standardField (conjWord word)) 1 (-z.2, z.1 - 1) := by
    intro z
    have e := hK z
    have ec := FLatticePaper.ChainEnd.earlierP_eq_chainPotential word (-(z - (frameAt word).sheetShift).2, (z - (frameAt word).sheetShift).1 - 1)
    rw [hW1] at e ec
    rw [hshift, sub_zero] at e ec
    unfold sheetPsi
    linarith [e, ec]
  obtain ⟨P, R, cU, cV, hPres, -, hNon, -, -, -, -, -⟩ := policy_of_gamesWithRank_prescribed hG
  have hdr := FLatticePaper.FreeChain.chain_drift_of_periods (frameAt (conjWord word)) hSE.packet.periods hSE.packet 1
  obtain ⟨q, hq⟩ : ∃ q : Site, q = (-(ArcPsi.reflH word r).2, (ArcPsi.reflH word r).1 - 1) := ⟨_, rfl⟩
  obtain ⟨q', hq'⟩ : ∃ q' : Site, q' = (-(ArcPsi.reflH word (r + (frameAt word).prescribedH η r)).2,
      (ArcPsi.reflH word (r + (frameAt word).prescribedH η r)).1 - 1) := ⟨_, rfl⟩
  rw [hΨ (ArcPsi.reflH word r), hΨ (ArcPsi.reflH word (r + (frameAt word).prescribedH η r)), ← hq, ← hq']
  suffices hmono : (frameAt (conjWord word)).chainPotential (standardField (conjWord word)) 1 q' ≤
      (frameAt (conjWord word)).chainPotential (standardField (conjWord word)) 1 q by linarith
  rw [← hq] at hmain
  have hq1 : q.1 = r.2 + 1 - (frameAt word).child.num := by
    rw [hq]
    unfold ArcPsi.reflH
    simp only
    ring
  have hq2 : q.2 = (frameAt word).child.den - r.1 := by
    rw [hq]
    unfold ArcPsi.reflH
    simp only
    ring
  have hmem := hbase (q.2 % period (frameAt (conjWord word))) (Int.emod_nonneg _ hp.ne') (Int.emod_lt_of_pos _ hp)
  have hv := hmain.symm
  unfold FreeEnum.vAt at hv
  set n0 := base (q.2 % period (frameAt (conjWord word))) with hn0def
  set m := q.2 / period (frameAt (conjWord word)) with hmdef
  have hVsum : (Vdeck (frameAt (conjWord word))).1 + (Vdeck (frameAt (conjWord word))).2 =
      2 * (frameAt (conjWord word)).child.num := by
    unfold Vdeck
    ring
  have hv1 : q.1 = n0.1 + m * (Vdeck (frameAt (conjWord word))).1 := by rw [hv]
  have hv2 : q.2 = n0.2 + m * (Vdeck (frameAt (conjWord word))).2 := by rw [hv]
  have hpn : (n0.1 + n0.2) % 2 = (q.1 + q.2) % 2 := by
    have e : q.1 + q.2 = n0.1 + n0.2 + 2 * (m * (frameAt (conjWord word)).child.num) := by
      rw [hv1, hv2]
      linear_combination m * hVsum
    generalize m * (frameAt (conjWord word)).child.num = M at e
    omega
  have hlap : laplacian (standardField (conjWord word)) n0 = 0 :=
    (frameAt (conjWord word)).laplacian_eq_zero_of_freeV hSE.packet.strips hmem.1
  have hcomb : (frameAt (conjWord word)).child.modifiedDeck.combine 0 m =
      (m * (Vdeck (frameAt (conjWord word))).1, m * (Vdeck (frameAt (conjWord word))).2) := by
    rw [combine_eq (frameAt (conjWord word)) 0 m, EndpointDeck.transverse_eq_Vdeck]
    ext <;> simp [Vdeck]
  obtain ⟨c, hc⟩ := hdr 0 m
  by_cases hev : EvenSite r
  · unfold EvenSite at hev
    have hpH : (frameAt word).prescribedH η r = (1, 0) := pH_even (frameAt word) η (by unfold EvenSite; exact hev)
    have hq'eq : q' = (q.1, q.2 - 1) := by
      rw [hq', hpH, hq1, hq2]
      unfold ArcPsi.reflH
      ext
      · simp only [Prod.snd_add]
        ring
      · simp only [Prod.fst_add]
        ring
    have hno : ¬ EvenSite n0 := by
      unfold EvenSite
      have hqp : (q.1 + q.2) % 2 = 1 := by
        rw [hq1, hq2]
        have : (frameAt word).child.den - (frameAt word).child.num = 2 * ((frameAt word).child.den - (frameAt word).child.num) / 2 := by
          omega
        omega
      omega
    have hpV : (frameAt (conjWord word)).prescribedV 1 n0 = (0, -1) := by
      rw [pV_odd (frameAt (conjWord word)) 1 hno]
    have hP : P n0 (n0 + (0, -1)) := by
      refine (hPres.2 n0 hmem.1 hlap (n0 + (0, -1))).mpr ?_
      rw [hpV]
    have hNon' := hNon n0 (n0 + (0, -1)) hP
    have e1 : q - (frameAt (conjWord word)).child.modifiedDeck.combine 0 m = n0 := by
      rw [hcomb]
      ext
      · simp only [Prod.fst_sub]
        linarith
      · simp only [Prod.snd_sub]
        linarith
    have e2 : q' - (frameAt (conjWord word)).child.modifiedDeck.combine 0 m = n0 + (0, -1) := by
      rw [hcomb, hq'eq]
      ext
      · simp only [Prod.fst_sub, Prod.fst_add]
        linarith
      · simp only [Prod.snd_sub, Prod.snd_add]
        linarith
    have hc1 := hc q
    have hc2 := hc q'
    rw [e1] at hc1
    rw [e2] at hc2
    linarith
  · have hodd : ¬ EvenSite r := by
      unfold EvenSite
      exact hev
    have hpH : (frameAt word).prescribedH η r = (0, 1) := pH_odd' (frameAt word) η hodd hr1
    have hq'eq : q' = (q.1 + 1, q.2) := by
      rw [hq', hpH, hq1, hq2]
      unfold ArcPsi.reflH
      ext
      · simp only [Prod.snd_add]
        ring
      · simp only [Prod.fst_add]
        ring
    have hev0 : EvenSite n0 := by
      unfold EvenSite
      unfold EvenSite at hodd
      have hqp : (q.1 + q.2) % 2 = 0 := by
        rw [hq1, hq2]
        omega
      omega
    have hpV : (frameAt (conjWord word)).prescribedV 1 n0 = (1, 0) := by
      rw [pV_even (frameAt (conjWord word)) 1 hev0]
      split_ifs <;> rfl
    have hP : P n0 (n0 + (1, 0)) := by
      refine (hPres.2 n0 hmem.1 hlap (n0 + (1, 0))).mpr ?_
      rw [hpV]
    have hNon' := hNon n0 (n0 + (1, 0)) hP
    have e1 : q - (frameAt (conjWord word)).child.modifiedDeck.combine 0 m = n0 := by
      rw [hcomb]
      ext
      · simp only [Prod.fst_sub]
        linarith
      · simp only [Prod.snd_sub]
        linarith
    have e2 : q' - (frameAt (conjWord word)).child.modifiedDeck.combine 0 m = n0 + (1, 0) := by
      rw [hcomb, hq'eq]
      ext
      · simp only [Prod.fst_sub, Prod.fst_add]
        linarith
      · simp only [Prod.snd_sub, Prod.snd_add]
        linarith
    have hc1 := hc q
    have hc2 := hc q'
    rw [e1] at hc1
    rw [e2] at hc2
    linarith

/-- **Phase one, offset class.** For the reflected query `Z(reflH r) = (1,0) + m·V'`, the native point is `H'_0 = (1,0)`, whose
prescribed step at sign `+1` is `(0,−1)`, which is the image step. -/
theorem psi_mono_phase1_offset {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1) (hG : GamesWithRank (conjWord word)) {r : Site} (η : ℤ)
    (hoff : ∃ m : ℤ, (-(ArcPsi.reflH word r).2, (ArcPsi.reflH word r).1 - 1) =
      ((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word))) :
    sheetPsi word (ArcPsi.reflH word r) ≤ sheetPsi word (ArcPsi.reflH word (r + (frameAt word).prescribedH η r)) := by
  obtain ⟨m, hm⟩ := hoff
  obtain ⟨hn0, hnd, -, -, -⟩ := (frameAt word).child_facts
  obtain ⟨hco1, hco2⟩ := (frameAt word).child_odd
  have hshift : (frameAt word).sheetShift = 0 := sheetShift_W1 word hW1
  obtain ⟨K, hK⟩ := sheetDifference_identifies h hSE.packet
  have hΨ : ∀ z : Site, sheetPsi word z = K - (frameAt (conjWord word)).chainPotential
      (standardField (conjWord word)) 1 (-z.2, z.1 - 1) := by
    intro z
    have e := hK z
    have ec := FLatticePaper.ChainEnd.earlierP_eq_chainPotential word (-(z - (frameAt word).sheetShift).2, (z - (frameAt word).sheetShift).1 - 1)
    rw [hW1] at e ec
    rw [hshift, sub_zero] at e ec
    unfold sheetPsi
    linarith [e, ec]
  obtain ⟨P, R, cU, cV, hPres, -, hNon, -, -, -, -, -⟩ := policy_of_gamesWithRank_prescribed hG
  have hdr := FLatticePaper.FreeChain.chain_drift_of_periods (frameAt (conjWord word)) hSE.packet.periods hSE.packet 1
  have hF0 : hFirst ∈ (frameAt (conjWord word)).freeH := FLatticePaper.PsiMonoOffset.hFirst_mem_freeH (frameAt (conjWord word))
  have hlap0 : laplacian (standardField (conjWord word)) hFirst = 0 :=
    laplacian_eq_zero_of_freeH (frameAt (conjWord word)) hSE.packet.strips hF0
  obtain ⟨q, hq⟩ : ∃ q : Site, q = (-(ArcPsi.reflH word r).2, (ArcPsi.reflH word r).1 - 1) := ⟨_, rfl⟩
  obtain ⟨q', hq'⟩ : ∃ q' : Site, q' = (-(ArcPsi.reflH word (r + (frameAt word).prescribedH η r)).2,
      (ArcPsi.reflH word (r + (frameAt word).prescribedH η r)).1 - 1) := ⟨_, rfl⟩
  rw [hΨ (ArcPsi.reflH word r), hΨ (ArcPsi.reflH word (r + (frameAt word).prescribedH η r)), ← hq, ← hq']
  suffices hmono : (frameAt (conjWord word)).chainPotential (standardField (conjWord word)) 1 q' ≤
      (frameAt (conjWord word)).chainPotential (standardField (conjWord word)) 1 q by linarith
  rw [← hq] at hm
  have hVsum : (Vdeck (frameAt (conjWord word))).1 + (Vdeck (frameAt (conjWord word))).2 =
      2 * (frameAt (conjWord word)).child.num := by
    unfold Vdeck
    ring
  have hm1 : q.1 = 1 + m * (Vdeck (frameAt (conjWord word))).1 := by
    rw [hm]
    simp
  have hm2 : q.2 = 0 + m * (Vdeck (frameAt (conjWord word))).2 := by
    rw [hm]
    simp
  have hq1 : q.1 = r.2 + 1 - (frameAt word).child.num := by
    rw [hq]
    unfold ArcPsi.reflH
    simp only
    ring
  have hq2 : q.2 = (frameAt word).child.den - r.1 := by
    rw [hq]
    unfold ArcPsi.reflH
    simp only
    ring
  have hev : EvenSite r := by
    have e : q.1 + q.2 = 1 + 2 * (m * (frameAt (conjWord word)).child.num) := by
      rw [hm1, hm2]
      linear_combination m * hVsum
    generalize m * (frameAt (conjWord word)).child.num = M at e
    unfold EvenSite
    omega
  have hpH : (frameAt word).prescribedH η r = (1, 0) := pH_even (frameAt word) η hev
  have hq'eq : q' = (q.1, q.2 - 1) := by
    rw [hq', hpH, hq1, hq2]
    unfold ArcPsi.reflH
    ext
    · simp only [Prod.snd_add]
      ring
    · simp only [Prod.fst_add]
      ring
  have hP : P hFirst (hFirst + (0, -1)) := by
    refine (hPres.1 hFirst hF0 hlap0 (hFirst + (0, -1))).mpr ?_
    rw [ChildFrame.prescribedH_hFirst]
  have hNon' := hNon hFirst (hFirst + (0, -1)) hP
  have hcomb : (frameAt (conjWord word)).child.modifiedDeck.combine 0 m =
      (m * (Vdeck (frameAt (conjWord word))).1, m * (Vdeck (frameAt (conjWord word))).2) := by
    rw [combine_eq (frameAt (conjWord word)) 0 m, EndpointDeck.transverse_eq_Vdeck]
    ext <;> simp [Vdeck]
  have e1 : q - (frameAt (conjWord word)).child.modifiedDeck.combine 0 m = hFirst := by
    rw [hcomb]
    ext
    · simp only [Prod.fst_sub, hFirst]
      linarith
    · simp only [Prod.snd_sub, hFirst]
      linarith
  have e2 : q' - (frameAt (conjWord word)).child.modifiedDeck.combine 0 m = hFirst + (0, -1) := by
    rw [hcomb, hq'eq]
    ext
    · simp only [Prod.fst_sub, Prod.fst_add, hFirst]
      linarith
    · simp only [Prod.snd_sub, Prod.snd_add, hFirst]
      linarith
  obtain ⟨c, hc⟩ := hdr 0 m
  have hc1 := hc q
  have hc2 := hc q'
  rw [e1] at hc1
  rw [e2] at hc2
  linarith

/-- **The phase-one comparison off the origin.** For a free H root `r ≠ H_0`, `Ψ(reflH r) ≤ Ψ(reflH (r + prescribedH η r))`. -/
theorem psi_mono_phase1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1) (hG : GamesWithRank (conjWord word))
    {base : ℤ → Site}
    (hbase : ∀ r : ℤ, 0 ≤ r → r < period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    {r : Site} (hr : r ∈ (frameAt word).freeH) (hr1 : r ≠ hFirst) (η : ℤ) :
    sheetPsi word (ArcPsi.reflH word r) ≤ sheetPsi word (ArcPsi.reflH word (r + (frameAt word).prescribedH η r)) := by
  have hcutC := FLatticePaper.CutRowsAll.cut_one_per_ordinate_all (frameAt (conjWord word))
  have hw := FLatticePaper.QueryClassMain.reflH_mem_freeH hr
  have hW1' : (frameAt word).eps = 1 → (ArcPsi.reflH word r).1 ≠ (frameAt word).child.den := by
    intro _ hcontra
    apply hr1
    apply freeH_x_one_eq_hFirst (frameAt word) hr
    unfold ArcPsi.reflH at hcontra
    omega
  rcases FLatticePaper.QueryClassMain.transport_class h hcutC hw hW1' hbase with ⟨hv, -⟩ | ⟨m, hm1, -⟩
  · rw [PsiCalibration.sheetShift_W1 word hW1, sub_zero] at hv
    exact psi_mono_phase1_main h hSE hW1 hG hbase hr1 η hv
  · rw [PsiCalibration.sheetShift_W1 word hW1, sub_zero] at hm1
    exact psi_mono_phase1_offset h hSE hW1 hG η ⟨m, hm1⟩

end FLatticePaper.PsiMonoPhase1
