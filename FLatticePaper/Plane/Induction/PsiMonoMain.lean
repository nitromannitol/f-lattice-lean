import FLatticePaper.Plane.Induction.GamesPolicyNeg
import FLatticePaper.Plane.Induction.SheetDifference
import FLatticePaper.Plane.Induction.ChainEnd
import FLatticePaper.Plane.Induction.FreeChain
import FLatticePaper.Plane.Induction.QueryGrade
import FLatticePaper.Plane.Induction.EndpointDeck
import FLatticePaper.Plane.Induction.Q3White
import FLatticePaper.Plane.Induction.FreePolicy
import FLatticePaper.Plane.Induction.FreeEnum
import FLatticePaper.Plane.Induction.PriceInputs
import FLatticePaper.Plane.Induction.DeckSelection

/-! The phase-zero comparison `Ψ(r) ≤ Ψ(i)` in the main class, where the query `q = Z(r − s)` is a translate `n₀ + m·V` of a free V point
`n₀ = base (q₂ mod L')`.

* `Ψ(z) = K − Φ(Z(z − s))`, with `Φ` the chain potential of the conjugate at sign `−1` (`sheetDifference_identifies`, `earlierP_eq_chainPotential`).
* The image step `q → q'` is the prescribed V step of `n₀` with sign `−1` (parity: `r` even gives `q` odd, `r` odd gives `q` even; `s` has
  odd components, so `Z` flips the parity), and `n₀` is free V with zero Laplacian, so `PrescribedAt` retains `n₀ → n₀'`.
* The drift `Φ(x − m·V) = Φ x + c` moves both points to `n₀` and `n₀'`, and `NonincreasingAlong` gives `Φ(n₀') ≤ Φ(n₀)`. -/

namespace FLatticePaper.PsiMonoMain

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Step FLatticePaper.FreePolicy FLatticePaper.DeckSelection
  FLatticePaper.FreeEnum

theorem psi_mono_main {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW0 : (frameAt word).eps = -1) (hG : GamesWithRank (conjWord word))
    {base : ℤ → Site}
    (hbase : ∀ r : ℤ, 0 ≤ r → r < period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r)
    {r : Site} (hr1 : r ≠ hFirst) (η : ℤ)
    (hmain : vAt (frameAt (conjWord word)) base (-(r - (frameAt word).sheetShift).2, (r - (frameAt word).sheetShift).1 - 1).2 =
        (-(r - (frameAt word).sheetShift).2, (r - (frameAt word).sheetShift).1 - 1))
    (hnv : base ((-(r - (frameAt word).sheetShift).2, (r - (frameAt word).sheetShift).1 - 1).2 %
        period (frameAt (conjWord word))) ≠ FLatticePaper.Induction.vFirst) :
    sheetPsi word r ≤ sheetPsi word (r + (frameAt word).prescribedH η r) := by
  have hp := period_pos (frameAt (conjWord word))
  obtain ⟨hn0, hnd, -, -, -⟩ := (frameAt word).child_facts
  obtain ⟨hco1, hco2⟩ := (frameAt word).child_odd
  obtain ⟨hN1, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps, -⟩ := FLatticePaper.PriceInputs.pdata h
  -- the sheet shift in phase zero is the even parent's kernel (den, num), both odd
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
  -- Ψ as the chain potential of the conjugate at the image point
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
  -- the retained policy of the conjugate at sign -1
  obtain ⟨P, R, cU, cV, hPres, -, hNon, -, -, -, -, -⟩ := policy_of_gamesWithRank_prescribed_neg hG
  have hdr := FLatticePaper.FreeChain.chain_drift_of_periods (frameAt (conjWord word)) hSE.packet.periods hSE.packet (-1)
  obtain ⟨q, hq⟩ : ∃ q : Site, q = (-(r - (frameAt word).sheetShift).2, (r - (frameAt word).sheetShift).1 - 1) :=
    ⟨_, rfl⟩
  obtain ⟨q', hq'⟩ : ∃ q' : Site,
      q' = (-((r + (frameAt word).prescribedH η r) - (frameAt word).sheetShift).2,
        ((r + (frameAt word).prescribedH η r) - (frameAt word).sheetShift).1 - 1) := ⟨_, rfl⟩
  have hsh1 : (frameAt word).sheetShift.1 % 2 = 1 := by rw [hshift]; exact hs1
  have hsh2 : (frameAt word).sheetShift.2 % 2 = 1 := by rw [hshift]; exact hs2
  have hq1 : q.1 = (frameAt word).sheetShift.2 - r.2 := by rw [hq]; simp
  have hq2 : q.2 = r.1 - (frameAt word).sheetShift.1 - 1 := by rw [hq]; simp
  rw [hΨ r, hΨ (r + (frameAt word).prescribedH η r), ← hq, ← hq']
  suffices hmono : (frameAt (conjWord word)).chainPotential (standardField (conjWord word)) (-1) q' ≤
      (frameAt (conjWord word)).chainPotential (standardField (conjWord word)) (-1) q by linarith
  rw [← hq] at hmain hnv
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
    have hq'eq : q' = (q.1, q.2 + 1) := by
      rw [hq', hpH, hq1, hq2]
      ext
      · simp
      · simp
        ring
    have hno : ¬ EvenSite n0 := by
      unfold EvenSite
      omega
    have hpV : (frameAt (conjWord word)).prescribedV (-1) n0 = (0, 1) := by
      rw [pV_odd (frameAt (conjWord word)) (-1) hno]
      norm_num
    have hP : P n0 (n0 + (0, 1)) := by
      refine (hPres.2 n0 hmem.1 hlap (n0 + (0, 1))).mpr ?_
      rw [hpV]
    have hNon' := hNon n0 (n0 + (0, 1)) hP
    have e1 : q - (frameAt (conjWord word)).child.modifiedDeck.combine 0 m = n0 := by
      rw [hcomb]
      ext
      · simp only [Prod.fst_sub]
        linarith
      · simp only [Prod.snd_sub]
        linarith
    have e2 : q' - (frameAt (conjWord word)).child.modifiedDeck.combine 0 m = n0 + (0, 1) := by
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
    have hq'eq : q' = (q.1 - 1, q.2) := by
      rw [hq', hpH, hq1, hq2]
      ext
      · simp
        ring
      · simp
    have hev0 : EvenSite n0 := by
      unfold EvenSite
      unfold EvenSite at hodd
      omega
    have hpV : (frameAt (conjWord word)).prescribedV (-1) n0 = (-1, 0) := by
      rw [pV_even (frameAt (conjWord word)) (-1) hev0]
      rw [if_neg hnv]
    have hP : P n0 (n0 + (-1, 0)) := by
      refine (hPres.2 n0 hmem.1 hlap (n0 + (-1, 0))).mpr ?_
      rw [hpV]
    have hNon' := hNon n0 (n0 + (-1, 0)) hP
    have e1 : q - (frameAt (conjWord word)).child.modifiedDeck.combine 0 m = n0 := by
      rw [hcomb]
      ext
      · simp only [Prod.fst_sub]
        linarith
      · simp only [Prod.snd_sub]
        linarith
    have e2 : q' - (frameAt (conjWord word)).child.modifiedDeck.combine 0 m = n0 + (-1, 0) := by
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

end FLatticePaper.PsiMonoMain
