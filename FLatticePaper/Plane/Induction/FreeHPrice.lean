import FLatticePaper.Plane.Induction.FirstOfferGrade
import FLatticePaper.Plane.Induction.TieReduce
import FLatticePaper.Plane.Induction.EHPrice
import FLatticePaper.Plane.Induction.SheetPieces

/-! The H neighbour price, ingredient (a): `F i = 0` at the prescribed neighbour `i = r + prescribedH η r` of a free H root `r`.
The first strip of the word's standard field gives `F = 0` on the child-grade window `[1 − d, n + 2d − 1]`. The grade of `i` is
`t(r) + n` (even `r`, east), `t(r) − d` (odd `r`, north) or `n + η d` (`r = H_0`). -/

namespace FLatticePaper.FreeHPrice

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.Induction.TipVertex FLatticePaper.PriceInputs
  FLatticePaper.W1Step FLatticePaper.W1MSheet

theorem neighbour_F_zero (frame : ChildFrame) {F : Field} (hS : frame.HasStrips F) {r : Site}
    (hr : r ∈ frame.freeH) {η : ℤ} (hη : η = 1 ∨ η = -1) :
    F (r + frame.prescribedH η r) = 0 := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  obtain ⟨hco1, hco2⟩ := frame.child_odd
  obtain ⟨hb1, hb2, hb3, hb4⟩ := FLatticePaper.Induction.FreeTraceBox.freeH_box frame hr
  have hsp := hr.2.2
  unfold ChildFrame.hSpectrum at hsp
  unfold ChildFrame.tGrade at hsp
  obtain ⟨t, ht⟩ : ∃ t, t = frame.child.num * r.1 - frame.child.den * r.2 := ⟨_, rfl⟩
  rw [← ht] at hsp
  have hpar : t % 2 = (r.1 + r.2) % 2 := by
    rw [ht, Int.sub_emod, Int.mul_emod, Int.mul_emod frame.child.den, hco1, hco2]
    omega
  by_cases h1 : r = hFirst
  · subst h1
    rw [ChildFrame.prescribedH_hFirst]
    have hv : frame.tGrade (hFirst + (0, -η)) = frame.child.num + η * frame.child.den := by
      unfold ChildFrame.tGrade hFirst
      simp only [Prod.fst_add, Prod.snd_add]
      ring
    apply hS.1
    · rw [hv]
      rcases hη with rfl | rfl <;> omega
    · rw [hv]
      rcases hη with rfl | rfl <;> omega
  · by_cases he : EvenSite r
    · unfold EvenSite at he
      rw [FLatticePaper.FreePolicy.pH_even frame η he]
      have hv : frame.tGrade (r + (1, 0)) = t + frame.child.num := by
        unfold ChildFrame.tGrade
        simp only [Prod.fst_add, Prod.snd_add]
        rw [ht]
        ring
      apply hS.1
      · rw [hv]; omega
      · rw [hv]; omega
    · unfold EvenSite at he
      rw [FLatticePaper.FreePolicy.pH_odd' frame η he h1]
      have hv : frame.tGrade (r + (0, 1)) = t - frame.child.den := by
        unfold ChildFrame.tGrade
        simp only [Prod.fst_add, Prod.snd_add]
        rw [ht]
        ring
      apply hS.1
      · rw [hv]; omega
      · rw [hv]; omega

/-- The grade bounds of the tip shift `c_t = n(N−D) − d(N+D)`, with `T = d² + 2dn − n²`. -/
theorem tip_bounds (n d N D nq dq T : ℤ) (hN1 : 1 ≤ N) (hND : N < D) (hD2 : 2 ≤ D) (hnq : 0 ≤ nq)
    (hdq : 0 ≤ dq) (hn : n = 2 * N + nq) (hd : d = 2 * D + dq) (hnd : n + 2 ≤ d)
    (hT : T = d * d + 2 * d * n - n * n) :
    -T ≤ n * (N - D) - d * (N + D) ∧ n * (N - D) - d * (N + D) ≤ -2 ∧
      n * (N - D) - d * (N + D) ≤ 2 - 2 * n ∧ d - n + 2 ≤ T + (n * (N - D) - d * (N + D)) := by
  have hn0 : 0 ≤ n := by omega
  have hd0 : 0 ≤ d := by omega
  have hk : 0 ≤ d - n := by omega
  have hDN : 0 ≤ D - N - 1 := by omega
  have hNDm : 0 ≤ N + D - 3 := by omega
  have hC : n * (N - D) - d * (N + D) ≤ -2 := by
    nlinarith [mul_nonneg hn0 hDN, mul_nonneg hd0 hNDm]
  have hD : d - n + 2 ≤ T + (n * (N - D) - d * (N + D)) := by
    rw [hT]
    nlinarith [mul_nonneg hn0 (show (0:ℤ) ≤ d - 2 * D by omega), mul_nonneg hk (show (0:ℤ) ≤ d - 2 * D by omega),
      mul_nonneg hk (show (0:ℤ) ≤ n - 2 * N by omega), mul_nonneg (show (0:ℤ) ≤ n - 2 by omega) hk,
      sq_nonneg n, sq_nonneg (d - n)]
  refine ⟨by linarith, hC, by nlinarith [mul_nonneg hn0 hDN, mul_nonneg hd0 hNDm], hD⟩

/-- **The closed-polygon membership of the prescribed H neighbour, phase zero.** The point `i + tip` (with `i = r + prescribedH η r`)
lies in `closedPolygon`: its grades are `t(r) + (shift)  + c_t` and `s(r) + (shift) − 2`, and the windows of `r` (box and H spectrum)
give the bounds. -/
theorem tip_closed_neighbour_W0 (frame : ChildFrame) (hN1 : 1 ≤ frame.parents.odd.num)
    (hND : frame.parents.odd.num < frame.parents.odd.den) (hD2 : 2 ≤ frame.parents.odd.den)
    (hnq : 0 ≤ frame.parents.even.num) (hdq : 0 ≤ frame.parents.even.den)
    (hn_eq : frame.child.num = 2 * frame.parents.odd.num + frame.parents.even.num)
    (hd_eq : frame.child.den = 2 * frame.parents.odd.den + frame.parents.even.den)
    (heps : frame.eps = frame.parents.odd.num * frame.parents.even.den - frame.parents.even.num * frame.parents.odd.den)
    (hε : frame.eps = -1) {r : Site} (hr : r ∈ frame.freeH) {η : ℤ} (hη : η = 1 ∨ η = -1) :
    r + frame.prescribedH η r + tipVertex frame ∈ frame.closedPolygon := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  obtain ⟨hco1, hco2⟩ := frame.child_odd
  have hnd2 : frame.child.num + 2 ≤ frame.child.den := by omega
  have hn1 : 1 ≤ frame.child.num := by omega
  obtain ⟨hb1, hb2, hb3, hb4⟩ := FLatticePaper.Induction.FreeTraceBox.freeH_box frame hr
  have hsp := hr.2.2
  unfold ChildFrame.hSpectrum at hsp
  have hpar : frame.tGrade r % 2 = (r.1 + r.2) % 2 := by
    unfold ChildFrame.tGrade
    rw [Int.sub_emod, Int.mul_emod, Int.mul_emod frame.child.den, hco1, hco2]
    omega
  have hTdef : frame.child.periodDenominator = frame.child.den * frame.child.den +
      2 * frame.child.den * frame.child.num - frame.child.num * frame.child.num := by
    unfold Fraction.periodDenominator
    ring
  obtain ⟨hA0, hC0, hB0, hD0⟩ := tip_bounds frame.child.num frame.child.den frame.parents.odd.num
    frame.parents.odd.den frame.parents.even.num frame.parents.even.den frame.child.periodDenominator
    hN1 hND hD2 hnq hdq hn_eq hd_eq hnd2 hTdef
  have hTbig : 2 * frame.child.den + 2 * frame.child.num ≤ frame.child.periodDenominator := by
    rw [hTdef]
    nlinarith [mul_nonneg hn0.le (show (0:ℤ) ≤ frame.child.den - frame.child.num by omega)]
  have htipT : ∀ z : Site, frame.tGrade (z + tipVertex frame) = frame.tGrade z +
      (frame.child.num * (frame.parents.odd.num - frame.parents.odd.den) -
        frame.child.den * (frame.parents.odd.num + frame.parents.odd.den)) := by
    intro z
    unfold ChildFrame.tGrade tipVertex
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have htipS : ∀ z : Site, frame.sGrade (z + tipVertex frame) = frame.sGrade z + 2 * frame.eps := by
    intro z
    unfold ChildFrame.sGrade tipVertex
    simp only [Prod.fst_add, Prod.snd_add]
    rw [heps, hn_eq, hd_eq]
    ring
  have hsr : frame.sGrade r = (frame.child.den + frame.child.num) * r.1 + (frame.child.den - frame.child.num) * r.2 := by
    unfold ChildFrame.sGrade
    ring
  have hS : frame.child.den + frame.child.num ≤ frame.sGrade r ∧ frame.sGrade r ≤
      frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num - frame.child.num * frame.child.num
        - frame.child.den + frame.child.num := by
    rw [hsr]
    exact FLatticePaper.PriceInputs.s_box frame.child.num frame.child.den r.1 r.2 hn0 hnd2 hb1 hb2 hb3 hb4
  by_cases h1 : r = hFirst
  · subst h1
    rw [ChildFrame.prescribedH_hFirst]
    rcases hη with rfl | rfl
    · have e1 : frame.tGrade (hFirst + (0, -1)) = frame.child.num + frame.child.den := by
        unfold ChildFrame.tGrade hFirst
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      have e2 : frame.sGrade (hFirst + (0, -1)) = 2 * frame.child.num := by
        unfold ChildFrame.sGrade hFirst
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      have hev : EvenSite (hFirst + (0, -1) + tipVertex frame) := by
        unfold EvenSite tipVertex hFirst
        simp only [Prod.fst_add, Prod.snd_add]
        omega
      rw [frame.mem_closedPolygon_iff]
      refine Or.inl ⟨hev, ?_, ?_, ?_, ?_⟩
      · rw [htipT, e1]; linarith
      · rw [htipT, e1]; linarith
      · rw [htipS, e2, hε]; linarith
      · rw [htipS, e2, hε]; linarith
    · have e1 : frame.tGrade (hFirst + (0, -(-1))) = frame.child.num - frame.child.den := by
        unfold ChildFrame.tGrade hFirst
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      have e2 : frame.sGrade (hFirst + (0, -(-1))) = 2 * frame.child.den := by
        unfold ChildFrame.sGrade hFirst
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      have hev : EvenSite (hFirst + (0, -(-1)) + tipVertex frame) := by
        unfold EvenSite tipVertex hFirst
        simp only [Prod.fst_add, Prod.snd_add]
        omega
      rw [frame.mem_closedPolygon_iff]
      refine Or.inl ⟨hev, ?_, ?_, ?_, ?_⟩
      · rw [htipT, e1]; linarith
      · rw [htipT, e1]; linarith
      · rw [htipS, e2, hε]; linarith
      · rw [htipS, e2, hε]; linarith
  · by_cases he : EvenSite r
    · unfold EvenSite at he
      rw [FLatticePaper.FreePolicy.pH_even frame η he]
      have ht_e : 2 ≤ frame.tGrade r ∧ frame.tGrade r ≤ frame.child.den + frame.child.num - 2 := by
        rcases hsp with ⟨h1', h2, h3⟩ | ⟨h1', h2, h3⟩ <;> omega
      have e1 : frame.tGrade (r + (1, 0)) = frame.tGrade r + frame.child.num := by
        unfold ChildFrame.tGrade
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      have e2 : frame.sGrade (r + (1, 0)) = frame.sGrade r + (frame.child.den + frame.child.num) := by
        unfold ChildFrame.sGrade
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      have hnev : ¬ EvenSite (r + (1, 0) + tipVertex frame) := by
        unfold EvenSite tipVertex
        simp only [Prod.fst_add, Prod.snd_add]
        omega
      rw [frame.mem_closedPolygon_iff]
      refine Or.inr ⟨hnev, ?_, ?_, ?_, ?_⟩
      · rw [htipT, e1]; linarith [ht_e.1, ht_e.2, hS.1, hS.2, hA0, hB0]
      · rw [htipT, e1]; linarith [ht_e.1, ht_e.2, hS.1, hS.2, hA0, hB0]
      · rw [htipS, e2, hε]; linarith [ht_e.1, ht_e.2, hS.1, hS.2]
      · rw [htipS, e2, hε]; linarith [ht_e.1, ht_e.2, hS.1, hS.2]
    · unfold EvenSite at he
      rw [FLatticePaper.FreePolicy.pH_odd' frame η he h1]
      have ht_o : frame.child.num ≤ frame.tGrade r ∧ frame.tGrade r ≤ frame.child.den := by
        rcases hsp with ⟨h1', h2, h3⟩ | ⟨h1', h2, h3⟩ <;> omega
      have e1 : frame.tGrade (r + (0, 1)) = frame.tGrade r - frame.child.den := by
        unfold ChildFrame.tGrade
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      have e2 : frame.sGrade (r + (0, 1)) = frame.sGrade r + (frame.child.den - frame.child.num) := by
        unfold ChildFrame.sGrade
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      have hev : EvenSite (r + (0, 1) + tipVertex frame) := by
        unfold EvenSite tipVertex
        simp only [Prod.fst_add, Prod.snd_add]
        omega
      rw [frame.mem_closedPolygon_iff]
      refine Or.inl ⟨hev, ?_, ?_, ?_, ?_⟩
      · rw [htipT, e1]; linarith [ht_o.1, ht_o.2, hD0, hB0, hC0]
      · rw [htipT, e1]; linarith [ht_o.1, ht_o.2, hD0, hB0, hC0]
      · rw [htipS, e2, hε]; linarith [hS.1, hS.2]
      · rw [htipS, e2, hε]; linarith [hS.1, hS.2]

/-- **The price of the prescribed H neighbour, phase zero.** `P(i) = c₀ − (1 + min 0 (Ψ(i) − 1))` at `i = r + prescribedH η r`, from
`EHPrice.price_W0` with its three site facts: `F i = 0`, `A i = 0` (`first_offer_neighbour_W0`), and the sheet-minimum identity at
`i + tip` (`tip_closed_neighbour_W0`). -/
theorem price_neighbour_W0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hW0 : (frameAt word).eps = -1) {r : Site}
    (hr : r ∈ (frameAt word).freeH) {η : ℤ} (hη : η = 1 ∨ η = -1) :
    (frameAt word).price (standardField word) (r + (frameAt word).prescribedH η r) =
      (frameAt word).cutPrice - (1 + min 0 (sheetPsi word (r + (frameAt word).prescribedH η r) - 1)) := by
  obtain ⟨hN1, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps, -⟩ := pdata h
  have hstr : (frameAt word).HasStrips (standardField word) := (packet_of_strong h hSE).strips
  have hz0 := neighbour_F_zero (frameAt word) hstr hr hη
  have hA0 := FLatticePaper.FirstOfferGrade.first_offer_neighbour_W0 h hSE hW0 hr hη
  have hcl := tip_closed_neighbour_W0 (frameAt word) hN1 hND hD2 hnq hdq hn_eq hd_eq heps hW0 hr hη
  have hFV := standardField_eq_sheetMin_of_strong h hSE hcl
  exact FLatticePaper.EHPrice.price_W0 h hSE hW0 _ hz0 hA0 hFV

end FLatticePaper.FreeHPrice
