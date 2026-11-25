import FLatticePaper.Plane.Induction.PsiMonoMain
import FLatticePaper.Plane.Induction.QueryClassMain
import FLatticePaper.Plane.Induction.CutRowsAll
import FLatticePaper.Plane.Induction.FreeHWhite

/-! Phase zero, the offset class and the full non-H_0 comparison.

* `hFirst_mem_freeH`: the origin of the H arc `H_0 = (1,0)` is a free H point of every child frame.
* `psi_mono_offset`: for the offset query `q = (1,0) + m·V'` (branch 2 of `transport_class`), the native point is `H'_0 = (1,0)`, whose
  prescribed step at sign `−1` is north `(0,1)`, which is the image step. The same retention and drift argument as `psi_mono_main`.
* `psi_mono_phase0`: for every free H root `r ≠ H_0` in phase zero, `Ψ(r) ≤ Ψ(r + prescribedH η r)`. The two cases are the two branches of
  `transport_class`; in branch 1 the native point has second coordinate `≠ 0`, so it is not the origin (`hnv` is not an extra premise). -/

namespace FLatticePaper.PsiMonoOffset

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Step FLatticePaper.FreePolicy FLatticePaper.DeckSelection
  FLatticePaper.FreeEnum FLatticePaper.PsiMonoMain

/-- The origin of the H arc is a free H point. -/
theorem hFirst_mem_freeH (frame : ChildFrame) : hFirst ∈ frame.freeH := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  obtain ⟨hco1, hco2⟩ := frame.child_odd
  have ht : frame.tGrade hFirst = frame.child.num := by
    unfold ChildFrame.tGrade hFirst
    ring
  have hs : frame.sGrade hFirst = frame.child.den + frame.child.num := by
    unfold ChildFrame.sGrade hFirst
    ring
  have hT2 : 2 ≤ frame.child.periodDenominator := by
    unfold Fraction.periodDenominator
    nlinarith
  have hodd : ¬ EvenSite hFirst := by
    unfold EvenSite hFirst
    omega
  have hdn : (hFirst.1, hFirst.2 - 1) = ((1 : ℤ), (-1 : ℤ)) := by
    unfold hFirst
    ext <;> simp
  refine ⟨?_, ?_, ?_⟩
  · rw [frame.mem_closedPolygon_iff]
    refine Or.inr ⟨hodd, ?_, ?_, ?_, ?_⟩
    · rw [ht]; omega
    · rw [ht]; omega
    · rw [hs]; omega
    · rw [hs]; omega
  · intro hmem
    rw [frame.mem_closedPolygon_iff, hdn] at hmem
    rcases hmem with ⟨_, h1, h2, _, _⟩ | ⟨hne, _⟩
    · have ht' : frame.tGrade ((1 : ℤ), (-1 : ℤ)) = frame.child.num + frame.child.den := by
        unfold ChildFrame.tGrade
        ring
      rw [ht'] at h2
      omega
    · exact hne (by unfold EvenSite; omega)
  · unfold ChildFrame.hSpectrum
    rw [ht]
    exact Or.inr ⟨by omega, le_refl _, by omega⟩

/-- **The offset class, phase zero.** For the query `q = (1,0) + m·V'` the image step is north and the native point is `H'_0 = (1,0)`. -/
theorem psi_mono_offset {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW0 : (frameAt word).eps = -1) (hG : GamesWithRank (conjWord word)) {r : Site} (η : ℤ)
    (hoff : ∃ m : ℤ, (-(r - (frameAt word).sheetShift).2, (r - (frameAt word).sheetShift).1 - 1) =
      ((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word))) :
    sheetPsi word r ≤ sheetPsi word (r + (frameAt word).prescribedH η r) := by
  obtain ⟨m, hm⟩ := hoff
  obtain ⟨hn0, hnd, -, -, -⟩ := (frameAt word).child_facts
  obtain ⟨hco1, hco2⟩ := (frameAt word).child_odd
  obtain ⟨hN1, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps, -⟩ := FLatticePaper.PriceInputs.pdata h
  have hW : (frameAt word).phaseW = 0 := by
    unfold ChildFrame.phaseW
    rw [hW0]
    norm_num
  have hshift : (frameAt word).sheetShift = ((frameAt word).parents.even.den, (frameAt word).parents.even.num) := by
    unfold ChildFrame.sheetShift
    rw [hW]
    simp [Fraction.unmodifiedDeck]
  have hs1 : (frameAt word).parents.even.den % 2 = 1 := by omega
  have hs2 : (frameAt word).parents.even.num % 2 = 1 := by omega
  have hsh1 : (frameAt word).sheetShift.1 % 2 = 1 := by rw [hshift]; exact hs1
  have hsh2 : (frameAt word).sheetShift.2 % 2 = 1 := by rw [hshift]; exact hs2
  obtain ⟨K, hK⟩ := sheetDifference_identifies h hSE.packet
  have hΨ : ∀ z : Site, sheetPsi word z = K - (frameAt (conjWord word)).chainPotential
      (standardField (conjWord word)) (-1)
      (-(z - (frameAt word).sheetShift).2, (z - (frameAt word).sheetShift).1 - 1) := by
    intro z
    have e := hK z
    have ec := FLatticePaper.ChainEnd.earlierP_eq_chainPotential word
      (-(z - (frameAt word).sheetShift).2, (z - (frameAt word).sheetShift).1 - 1)
    rw [hW0] at e ec
    unfold sheetPsi
    linarith [e, ec]
  obtain ⟨P, R, cU, cV, hPres, -, hNon, -, -, -, -, -⟩ := policy_of_gamesWithRank_prescribed_neg hG
  have hdr := FLatticePaper.FreeChain.chain_drift_of_periods (frameAt (conjWord word)) hSE.packet.periods hSE.packet (-1)
  have hF0 : hFirst ∈ (frameAt (conjWord word)).freeH := hFirst_mem_freeH (frameAt (conjWord word))
  have hlap0 : laplacian (standardField (conjWord word)) hFirst = 0 :=
    laplacian_eq_zero_of_freeH (frameAt (conjWord word)) hSE.packet.strips hF0
  obtain ⟨q, hq⟩ : ∃ q : Site, q = (-(r - (frameAt word).sheetShift).2, (r - (frameAt word).sheetShift).1 - 1) :=
    ⟨_, rfl⟩
  obtain ⟨q', hq'⟩ : ∃ q' : Site,
      q' = (-((r + (frameAt word).prescribedH η r) - (frameAt word).sheetShift).2,
        ((r + (frameAt word).prescribedH η r) - (frameAt word).sheetShift).1 - 1) := ⟨_, rfl⟩
  have hq1 : q.1 = (frameAt word).sheetShift.2 - r.2 := by rw [hq]; simp
  have hq2 : q.2 = r.1 - (frameAt word).sheetShift.1 - 1 := by rw [hq]; simp
  rw [hΨ r, hΨ (r + (frameAt word).prescribedH η r), ← hq, ← hq']
  suffices hmono : (frameAt (conjWord word)).chainPotential (standardField (conjWord word)) (-1) q' ≤
      (frameAt (conjWord word)).chainPotential (standardField (conjWord word)) (-1) q by linarith
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
  have hpar : (q.1 + q.2) % 2 = 1 := by
    have e : q.1 + q.2 = 1 + 2 * (m * (frameAt (conjWord word)).child.num) := by
      rw [hm1, hm2]
      linear_combination m * hVsum
    generalize m * (frameAt (conjWord word)).child.num = M at e
    omega
  have hev : EvenSite r := by
    unfold EvenSite
    omega
  have hpH : (frameAt word).prescribedH η r = (1, 0) := pH_even (frameAt word) η hev
  have hq'eq : q' = (q.1, q.2 + 1) := by
    rw [hq', hpH, hq1, hq2]
    ext
    · simp
    · simp
      ring
  have hP : P hFirst (hFirst + (0, 1)) := by
    refine (hPres.1 hFirst hF0 hlap0 (hFirst + (0, 1))).mpr ?_
    rw [ChildFrame.prescribedH_hFirst]
    norm_num
  have hNon' := hNon hFirst (hFirst + (0, 1)) hP
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
  have e2 : q' - (frameAt (conjWord word)).child.modifiedDeck.combine 0 m = hFirst + (0, 1) := by
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

/-- **The phase-zero comparison off the origin.** For a free H root `r ≠ H_0`, `Ψ(r) ≤ Ψ(r + prescribedH η r)`, in both classes of
`transport_class`. -/
theorem psi_mono_phase0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW0 : (frameAt word).eps = -1) (hG : GamesWithRank (conjWord word))
    {base : ℤ → Site}
    (hbase : ∀ r : ℤ, 0 ≤ r → r < period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    {r : Site} (hr : r ∈ (frameAt word).freeH) (hr1 : r ≠ hFirst) (η : ℤ) :
    sheetPsi word r ≤ sheetPsi word (r + (frameAt word).prescribedH η r) := by
  have hp := period_pos (frameAt (conjWord word))
  have hcutC := FLatticePaper.CutRowsAll.cut_one_per_ordinate_all (frameAt (conjWord word))
  rcases FLatticePaper.QueryClassMain.transport_class h hcutC hr
    (fun h1 => by rw [hW0] at h1; norm_num at h1) hbase with ⟨hv, hj⟩ | ⟨m, hm1, -⟩
  · have hj' : (QueryGrade.zq (r - (frameAt word).sheetShift)).2 % period (frameAt (conjWord word)) ≠ 0 :=
      hj.resolve_right (fun h1 => by
        have h2 := h1.1
        rw [hW0] at h2
        norm_num at h2)
    have hnv : base ((QueryGrade.zq (r - (frameAt word).sheetShift)).2 % period (frameAt (conjWord word))) ≠
        FLatticePaper.Induction.vFirst := by
      intro heq
      have hb := (hbase ((QueryGrade.zq (r - (frameAt word).sheetShift)).2 % period (frameAt (conjWord word)))
        (Int.emod_nonneg _ hp.ne') (Int.emod_lt_of_pos _ hp)).2
      rw [heq] at hb
      apply hj'
      unfold FLatticePaper.Induction.vFirst at hb
      simp only at hb
      omega
    exact psi_mono_main h hSE hW0 hG hbase hr1 η hv hnv
  · exact psi_mono_offset h hSE hW0 hG η ⟨m, hm1⟩

end FLatticePaper.PsiMonoOffset
