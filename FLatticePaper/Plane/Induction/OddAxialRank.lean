import FLatticePaper.Plane.Induction.EasyHRankDiag
import FLatticePaper.Plane.Induction.EastColour
import FLatticePaper.Plane.Induction.HGap
import FLatticePaper.Plane.Induction.StrictNonfree
import FLatticePaper.Plane.Induction.PassageRank
import FLatticePaper.Plane.Induction.RowPairWord

/-! # Rank 3 of the easy H entries: the odd axial N-E-S passage (Q1 short passage)

For an odd free H entry `z = hpath m` (`1 ≤ m`, `m + 1 < d`) with axial successor `z + (1,0)` (`east_freeH_of_odd`), the label
`ℓ = H_{m−d} = z − U` is odd. Its prescribed input is north, `p' = ℓ + (0,1)` (even), whose horizontal input is `q' = ℓ + (1,1)`
(odd), whose vertical input is `ℓ + (1,0) = H_{m+1−d}`, the earlier entry. The white rule runs twice:
* `p = z + (0,1)` is white (its band and the even zero interval) and strict-interior, hence nonfree;
* `q = z + (1,1)` is white when `t(z) ≥ d + 2 − 2n` (its input `z + (1,2)` lies in the even zero interval), and strict-interior
  (`s(q) < T + 2 − d + n` from the H gap at the east neighbour), hence nonfree.

The black case `t(z) < d + 2 − 2n` is the fan case (not here). -/

namespace FLatticePaper.OddAxialRank

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.RefuteTree FLatticePaper.EasyHRank
open FLatticePaper.EasyHRankDiag

/-- `t(z) ≠ n` on the chain: `n (z₁ − 1) = d z₂` would force `d ∣ z₁ − 1`, impossible for `2 ≤ z₁ < d`. -/
theorem t_ne_num (frame : ChildFrame) {z : Site} (hx2 : 2 ≤ z.1) (hxd : z.1 < frame.child.den) :
    frame.tGrade z ≠ frame.child.num := by
  intro hteq
  have hdv : frame.child.den ∣ frame.child.num * (z.1 - 1) := ⟨z.2, by
    unfold ChildFrame.tGrade at hteq
    linear_combination hteq⟩
  obtain ⟨c, hc⟩ := (frame.child_reduced.symm).dvd_of_dvd_mul_left hdv
  have hd3 := (frame.child_facts).2.2.2.1
  rcases le_or_gt c 0 with h | h
  · nlinarith
  · nlinarith

/-- `t(z) ≠ d` on the chain: `n z₁ = d (z₂ + 1)` would force `d ∣ z₁`, impossible for `1 ≤ z₁ < d`. -/
theorem t_ne_den (frame : ChildFrame) {z : Site} (hx1 : 1 ≤ z.1) (hxd : z.1 < frame.child.den) :
    frame.tGrade z ≠ frame.child.den := by
  intro hteq
  have hdv : frame.child.den ∣ frame.child.num * z.1 := ⟨z.2 + 1, by
    unfold ChildFrame.tGrade at hteq
    linear_combination hteq⟩
  obtain ⟨c, hc⟩ := (frame.child_reduced.symm).dvd_of_dvd_mul_left hdv
  have hd3 := (frame.child_facts).2.2.2.1
  rcases le_or_gt c 0 with h | h
  · nlinarith
  · nlinarith

/-- The odd chain points before `hLast` have `t` in `[n + 2, d − 2]`. -/
theorem odd_t_range (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z)
    (hx2 : 2 ≤ z.1) (hxd : z.1 < frame.child.den) :
    frame.child.num + 2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den - 2 := by
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz
  obtain ⟨-, -, hsp⟩ := hz
  unfold ChildFrame.hSpectrum at hsp
  have hpar : frame.tGrade z % 2 = 1 := by
    rw [EasyHRankDiag.tGrade_parity frame z]
    unfold EvenSite at hodd
    omega
  have hr : frame.child.num ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den := by
    rcases hsp with ⟨h0, -⟩ | ⟨-, h2, h3⟩
    · omega
    · exact ⟨h2, h3⟩
  have hn := t_ne_num frame hx2 hxd
  have hd := t_ne_den frame (by omega) hxd
  omega

/-- **The odd s-gap at the north-east input.** For an odd closed-polygon point with `2 ≤ z₁`, `n + 2 ≤ t ≤ d − 2`, the value `s`
is above `d + n`: otherwise the identity `T z₂ = n s − L t` gives `z₂ = 0`, and then `s = L z₁ ≤ d + n` forces `z₁ ≤ 1`. -/
theorem odd_low (frame : ChildFrame) {z : Site} (hz : z ∈ frame.closedPolygon) (hodd : ¬ EvenSite z)
    (ht1 : frame.child.num ≤ frame.tGrade z) (ht2 : frame.tGrade z ≤ frame.child.den - 2) (hx2 : 2 ≤ z.1) :
    frame.child.den + frame.child.num < frame.sGrade z := by
  obtain ⟨hn0, hnd, hd2', hd3, hTd⟩ := frame.child_facts
  have hT0 : 0 < frame.child.periodDenominator := by
    rw [hTd]
    nlinarith
  have hcl := hz
  unfold ChildFrame.closedPolygon at hcl
  simp only [Set.mem_setOf_eq] at hcl
  rw [if_neg hodd] at hcl
  obtain ⟨-, -, hslo, -⟩ := hcl
  have hid : frame.child.periodDenominator * z.2 =
      frame.child.num * frame.sGrade z - (frame.child.den + frame.child.num) * frame.tGrade z := by
    rw [hTd]
    unfold ChildFrame.sGrade ChildFrame.tGrade
    ring
  by_contra hcon
  push Not at hcon
  have hA1 : frame.child.num * (2 - frame.child.den + frame.child.num) ≤ frame.child.num * frame.sGrade z :=
    mul_le_mul_of_nonneg_left hslo (by omega)
  have hA2 : (frame.child.den + frame.child.num) * frame.tGrade z
      ≤ (frame.child.den + frame.child.num) * (frame.child.den - 2) :=
    mul_le_mul_of_nonneg_left ht2 (by omega)
  have hB1 : frame.child.num * frame.sGrade z ≤ frame.child.num * (frame.child.den + frame.child.num) :=
    mul_le_mul_of_nonneg_left hcon (by omega)
  have hB2 : (frame.child.den + frame.child.num) * frame.child.num
      ≤ (frame.child.den + frame.child.num) * frame.tGrade z :=
    mul_le_mul_of_nonneg_left ht1 (by omega)
  have e1 : frame.child.num * (2 - frame.child.den + frame.child.num)
      - (frame.child.den + frame.child.num) * (frame.child.den - 2)
      = -frame.child.periodDenominator + 2 * frame.child.den + 4 * frame.child.num := by
    rw [hTd]
    ring
  have hlo : -frame.child.periodDenominator + 2 * frame.child.den + 4 * frame.child.num
      ≤ frame.child.periodDenominator * z.2 := by
    linarith
  have e2 : frame.child.num * (frame.child.den + frame.child.num)
      - (frame.child.den + frame.child.num) * frame.child.num = 0 := by
    ring
  have hhi : frame.child.periodDenominator * z.2 ≤ 0 := by
    linarith
  have hy0 : 0 ≤ z.2 := by
    by_contra h
    push Not at h
    have h1 : z.2 ≤ -1 := by omega
    have := mul_le_mul_of_nonneg_left h1 hT0.le
    linarith
  have hy1 : z.2 ≤ 0 := by
    by_contra h
    push Not at h
    have h1 : 1 ≤ z.2 := by omega
    have := mul_le_mul_of_nonneg_left h1 hT0.le
    linarith
  have hy : z.2 = 0 := by omega
  unfold ChildFrame.sGrade at hcon
  rw [hy] at hcon
  have h2 : (frame.child.den + frame.child.num) * 2 ≤ (frame.child.den + frame.child.num) * z.1 :=
    mul_le_mul_of_nonneg_left hx2 (by omega)
  linarith

/-- The colour of `p = z + (0,1)`: for an odd point with `n + 2 ≤ t ≤ d − 2` the north neighbour is white. Its three
inputs-and-self lie in the zero band (`t` in `[1 − d, n + 2d − 1]`). -/
theorem colour_north_odd (frame : ChildFrame) {G : Field} (hS : frame.HasStrips G) {z : Site}
    (hodd : ¬ EvenSite z) (ht1 : frame.child.num + 2 ≤ frame.tGrade z) (ht2 : frame.tGrade z ≤ frame.child.den - 2) :
    laplacian G (z + ((0 : ℤ), (1 : ℤ))) = 0 := by
  obtain ⟨hn0, hnd, -, hd3, -⟩ := frame.child_facts
  have hpE : EvenSite (z + ((0 : ℤ), (1 : ℤ))) := by
    unfold EvenSite at hodd ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have eP : frame.tGrade (z + ((0 : ℤ), (1 : ℤ))) = frame.tGrade z - frame.child.den := by
    unfold ChildFrame.tGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have eN : frame.tGrade (incomingNeg (z + ((0 : ℤ), (1 : ℤ))))
      = frame.tGrade z - frame.child.num - frame.child.den := by
    unfold incomingNeg
    rw [if_pos hpE]
    unfold ChildFrame.tGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have eQ : frame.tGrade (incomingPos (z + ((0 : ℤ), (1 : ℤ))))
      = frame.tGrade z + frame.child.num - frame.child.den := by
    unfold incomingPos
    rw [if_pos hpE]
    unfold ChildFrame.tGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have hGp : G (z + ((0 : ℤ), (1 : ℤ))) = 0 :=
    hS.1 _ (by rw [eP]; linarith) (by rw [eP]; linarith)
  have hGn : G (incomingNeg (z + ((0 : ℤ), (1 : ℤ)))) = 0 :=
    hS.1 _ (by rw [eN]; linarith) (by rw [eN]; linarith)
  have hGq : G (incomingPos (z + ((0 : ℤ), (1 : ℤ)))) = 0 :=
    hS.1 _ (by rw [eQ]; linarith) (by rw [eQ]; linarith)
  unfold laplacian
  rw [hGn, hGq, hGp]
  ring

/-- The colour of `q = z + (1,1)` for an odd point with `t ≤ d − 2` and `d + 2 − 2n ≤ t`: the east input is in the band, `q` is in
the band, and the north input `z + (1,2)` lies in the even zero interval `[2 − L, 2L − 2]` (the input `hZ`). -/
theorem colour_q_odd (frame : ChildFrame) {G : Field} (hS : frame.HasStrips G)
    (hZ : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → G w = 0)
    {z : Site} (hodd : ¬ EvenSite z) (ht2 : frame.tGrade z ≤ frame.child.den - 2)
    (hlate : frame.child.den + 2 - 2 * frame.child.num ≤ frame.tGrade z) :
    laplacian G (z + ((1 : ℤ), (1 : ℤ))) = 0 := by
  obtain ⟨hn0, hnd, -, hd3, -⟩ := frame.child_facts
  have hqO : ¬ EvenSite (z + ((1 : ℤ), (1 : ℤ))) := by
    unfold EvenSite at hodd ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hRE : EvenSite (z + ((1 : ℤ), (2 : ℤ))) := by
    unfold EvenSite at hodd ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hNeg : incomingNeg (z + ((1 : ℤ), (1 : ℤ))) = z + ((1 : ℤ), (0 : ℤ)) := by
    unfold incomingNeg
    rw [if_neg hqO]
    ext <;> simp
  have hPos : incomingPos (z + ((1 : ℤ), (1 : ℤ))) = z + ((1 : ℤ), (2 : ℤ)) := by
    unfold incomingPos
    rw [if_neg hqO]
    refine Prod.ext ?_ ?_
    · simp
    · simp only [Prod.snd_add]
      ring
  have eE : frame.tGrade (z + ((1 : ℤ), (0 : ℤ))) = frame.tGrade z + frame.child.num := by
    unfold ChildFrame.tGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have eQ : frame.tGrade (z + ((1 : ℤ), (1 : ℤ))) = frame.tGrade z + frame.child.num - frame.child.den := by
    unfold ChildFrame.tGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have eR : frame.tGrade (z + ((1 : ℤ), (2 : ℤ)))
      = frame.tGrade z + frame.child.num - 2 * frame.child.den := by
    unfold ChildFrame.tGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have hGE : G (z + ((1 : ℤ), (0 : ℤ))) = 0 :=
    hS.1 _ (by rw [eE]; linarith) (by rw [eE]; linarith)
  have hGQ : G (z + ((1 : ℤ), (1 : ℤ))) = 0 :=
    hS.1 _ (by rw [eQ]; linarith) (by rw [eQ]; linarith)
  have hGR : G (z + ((1 : ℤ), (2 : ℤ))) = 0 :=
    hZ _ hRE (by rw [eR]; linarith) (by rw [eR]; linarith)
  unfold laplacian
  rw [hNeg, hPos, hGE, hGQ, hGR]
  ring

/-- The north neighbour `z + (0,1)` of an odd free H point before `hLast` is strict-interior (hence nonfree). -/
theorem si_north_odd (frame : ChildFrame) {z : Site}
    (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z) (hx2 : 2 ≤ z.1) (hxd : z.1 < frame.child.den) :
    FLatticePaper.W1.StrictInterior frame.child.num frame.child.den (z + ((0 : ℤ), (1 : ℤ))) := by
  obtain ⟨hn0, hnd, hd2', hd3, hTd⟩ := frame.child_facts
  have hrange := odd_t_range frame hz hodd hx2 hxd
  have hcl : z ∈ frame.closedPolygon := by
    simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz
    exact hz.1
  have hlow := odd_low frame hcl hodd (by omega) hrange.2 hx2
  have hgap := odd_gap frame hcl hodd (by omega) hrange.2
  have hpE : EvenSite (z + ((0 : ℤ), (1 : ℤ))) := by
    unfold EvenSite at hodd ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have eT : FLatticePaper.W1.w1t frame.child.num frame.child.den (z + ((0 : ℤ), (1 : ℤ)))
      = frame.tGrade z - frame.child.den := by
    unfold FLatticePaper.W1.w1t ChildFrame.tGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have eS : FLatticePaper.W1.w1s frame.child.num frame.child.den (z + ((0 : ℤ), (1 : ℤ)))
      = frame.sGrade z + (frame.child.den - frame.child.num) := by
    unfold FLatticePaper.W1.w1s ChildFrame.sGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have eA : FLatticePaper.W1.w1b frame.child.num frame.child.den (z + ((0 : ℤ), (1 : ℤ)))
      = frame.child.den + frame.child.num - 2 := by
    unfold FLatticePaper.W1.w1b
    rw [if_pos hpE]
  have eA2 : FLatticePaper.W1.w1a frame.child.num (z + ((0 : ℤ), (1 : ℤ))) = 2 := by
    unfold FLatticePaper.W1.w1a
    rw [if_pos hpE]
  have eH : FLatticePaper.W1.w1h frame.child.num frame.child.den (z + ((0 : ℤ), (1 : ℤ)))
      = 2 * frame.child.num := by
    unfold FLatticePaper.W1.w1h
    rw [if_pos hpE]
  have eC : FLatticePaper.W1.w1c frame.child.num frame.child.den (z + ((0 : ℤ), (1 : ℤ))) = 0 := by
    unfold FLatticePaper.W1.w1c
    rw [if_pos hpE]
  have eTT : FLatticePaper.W1.w1T frame.child.num frame.child.den = frame.child.periodDenominator := by
    rw [hTd]
    unfold FLatticePaper.W1.w1T
    ring
  have hT : 2 * frame.child.den < frame.child.periodDenominator := by
    rw [hTd]
    nlinarith
  unfold FLatticePaper.W1.StrictInterior
  rw [eA, eA2, eH, eC, eT, eS, eTT]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The east-north input `z + (1,1)` of an odd free H point before `hLast` (with a free east neighbour) is strict-interior. -/
theorem si_q_odd (frame : ChildFrame) (hd2 : 2 * frame.child.num ≤ frame.child.den) {z : Site}
    (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z) (hx2 : 2 ≤ z.1) (hxd : z.1 < frame.child.den)
    (hE : (z.1 + 1, z.2) ∈ frame.freeH) :
    FLatticePaper.W1.StrictInterior frame.child.num frame.child.den (z + ((1 : ℤ), (1 : ℤ))) := by
  obtain ⟨hn0, hnd, hd2', hd3, hTd⟩ := frame.child_facts
  have hrange := odd_t_range frame hz hodd hx2 hxd
  have hcl : z ∈ frame.closedPolygon := by
    simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz
    exact hz.1
  have hslo : 2 - frame.child.den + frame.child.num ≤ frame.sGrade z := by
    unfold ChildFrame.closedPolygon at hcl
    simp only [Set.mem_setOf_eq] at hcl
    rw [if_neg hodd] at hcl
    exact hcl.2.2.1
  have hEven : EvenSite (z.1 + 1, z.2) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  have hHE := HGap.sGrade_lt_of_freeH_even frame hd2 hE hEven
  have eSE : frame.sGrade (z.1 + 1, z.2) = frame.sGrade z + (frame.child.den + frame.child.num) := by
    unfold ChildFrame.sGrade
    dsimp only
    ring
  have hqO : ¬ EvenSite (z + ((1 : ℤ), (1 : ℤ))) := by
    unfold EvenSite at hodd ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have eT : FLatticePaper.W1.w1t frame.child.num frame.child.den (z + ((1 : ℤ), (1 : ℤ)))
      = frame.tGrade z + frame.child.num - frame.child.den := by
    unfold FLatticePaper.W1.w1t ChildFrame.tGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have eS : FLatticePaper.W1.w1s frame.child.num frame.child.den (z + ((1 : ℤ), (1 : ℤ)))
      = frame.sGrade z + 2 * frame.child.den := by
    unfold FLatticePaper.W1.w1s ChildFrame.sGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have eA : FLatticePaper.W1.w1b frame.child.num frame.child.den (z + ((1 : ℤ), (1 : ℤ))) = frame.child.den := by
    unfold FLatticePaper.W1.w1b
    rw [if_neg hqO]
  have eA2 : FLatticePaper.W1.w1a frame.child.num (z + ((1 : ℤ), (1 : ℤ))) = frame.child.num := by
    unfold FLatticePaper.W1.w1a
    rw [if_neg hqO]
  have eH : FLatticePaper.W1.w1h frame.child.num frame.child.den (z + ((1 : ℤ), (1 : ℤ)))
      = frame.child.den + frame.child.num - 2 := by
    unfold FLatticePaper.W1.w1h
    rw [if_neg hqO]
  have eC : FLatticePaper.W1.w1c frame.child.num frame.child.den (z + ((1 : ℤ), (1 : ℤ)))
      = 2 - frame.child.den + frame.child.num := by
    unfold FLatticePaper.W1.w1c
    rw [if_neg hqO]
  have eTT : FLatticePaper.W1.w1T frame.child.num frame.child.den = frame.child.periodDenominator := by
    rw [hTd]
    unfold FLatticePaper.W1.w1T
    ring
  have hT : 2 * frame.child.den < frame.child.periodDenominator := by
    rw [hTd]
    nlinarith
  unfold FLatticePaper.W1.StrictInterior
  rw [eA, eA2, eH, eC, eT, eS, eTT]
  rw [eSE] at hHE
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hrange.1, hrange.2]

/-- **Rank 3, the odd axial N-E-S passage.** For an odd free H point `z = hpath m` (`1 ≤ m`, `m + 1 < d`) with the white late
east-north input (`d + 2 − 2n ≤ t(z)`), the label `H_{m−d}` is refuted: through its north input `p'`, whose horizontal input
`q'` is white and nonfree, and whose vertical input is the earlier entry `H_{m+1−d}`. -/
theorem refuted_odd_H_axial (frame : ChildFrame) (F : Field) (hP : frame.Packet F) {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV)
    (hd2 : 2 * frame.child.num ≤ frame.child.den)
    (hZ : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den) (hodd : ¬ EvenSite (HChain.hpath frame m))
    (hlate : frame.child.den + 2 - 2 * frame.child.num ≤ frame.tGrade (HChain.hpath frame m))
    {E C : Site → Prop} (hE : E (RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den))) :
    Refuted frame F (-1) E C (RowAt.hAt frame ((m : ℤ) - frame.child.den)) := by
  set z := HChain.hpath frame m with hz
  set l := RowAt.hAt frame ((m : ℤ) - frame.child.den) with hl
  have hzfree : z ∈ frame.freeH := RowPairWord.hpath_mem_all frame m (by omega)
  have hz1 : z.1 = (m : ℤ) + 1 := RowPair.hpath_fst frame m
  have hx2 : 2 ≤ z.1 := by omega
  have hxd : z.1 < frame.child.den := by omega
  have hdom : z ≠ FLatticePaper.Induction.hFirst := by
    intro h
    have h3 : z.1 = 1 := congrArg Prod.fst h
    omega
  have hlast : z ≠ frame.hLast := by
    intro h
    have h3 : z.1 = frame.child.den := congrArg Prod.fst h
    omega
  have hEast := EasyHRankDiag.east_freeH_of_odd frame hzfree hodd (by omega) hxd
  have hsucc_eq : HChain.hpath frame (m + 1) = (z.1 + 1, z.2) := by
    rw [HChain.hpath_succ, ← hz, EasyHRank.hsucc_east hEast]
  have hU := EasyHRank.combine_one_zero_eq_Uvec frame
  have hA : l = z - RowAt.Uvec frame := by
    rw [hl, EasyHRank.hAt_sub_den frame (by omega), ← hz]
  have heU : l + frame.child.modifiedDeck.combine 1 0 = z := by
    rw [hU, hA]
    abel
  have hlodd : ¬ EvenSite l := by
    rw [hA]
    obtain ⟨hnodd, hdodd⟩ := frame.child_odd
    unfold EvenSite at hodd ⊢
    unfold RowAt.Uvec
    simp only [Prod.fst_sub, Prod.snd_sub]
    omega
  -- the successor and the label of the east entry
  have hAt_next : RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den) = (z.1 + 1, z.2) - RowAt.Uvec frame := by
    rw [show (m : ℤ) + 1 - frame.child.den = ((m + 1 : ℕ) : ℤ) - frame.child.den by push_cast; ring,
      EasyHRank.hAt_sub_den frame (show ((m + 1 : ℕ) : ℤ) < frame.child.den by push_cast; omega), hsucc_eq]
  have hE_l : RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den) = l + ((1 : ℤ), (0 : ℤ)) := by
    rw [hAt_next, hA]
    refine Prod.ext ?_ ?_
    · simp only [RowAt.Uvec, Prod.fst_sub, Prod.fst_add]
      omega
    · simp [RowAt.Uvec]
  have hE' : E (l + ((1 : ℤ), (0 : ℤ))) := by
    rw [← hE_l]
    exact hE
  -- colours: the label, the north input, the east-north input
  have hcol : laplacian F l = 0 := by
    have h := laplacian_add_combine hper l 1 0
    rw [heU] at h
    rw [← h]
    exact FLatticePaper.Induction.laplacian_eq_zero_of_freeH frame hP.strips hzfree
  obtain ⟨hrng1, hrng2⟩ := odd_t_range frame hzfree hodd hx2 hxd
  have hcolP : laplacian F (z + ((0 : ℤ), (1 : ℤ))) = 0 :=
    colour_north_odd frame hP.strips hodd hrng1 hrng2
  have hcolQ : laplacian F (z + ((1 : ℤ), (1 : ℤ))) = 0 :=
    colour_q_odd frame hP.strips hZ hodd hrng2 hlate
  -- strict interior, hence nonfree
  have hcl : z ∈ frame.closedPolygon := by
    simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hzfree
    exact hzfree.1
  have hnfP : Nonfree frame (z + ((0 : ℤ), (1 : ℤ))) :=
    strictInterior_nonfree frame (si_north_odd frame hzfree hodd hx2 hxd)
  have hnfQ : Nonfree frame (z + ((1 : ℤ), (1 : ℤ))) :=
    strictInterior_nonfree frame (si_q_odd frame hd2 hzfree hodd hx2 hxd hEast)
  -- the label-level translates by `−U`
  have hcomb_neg : frame.child.modifiedDeck.combine (-1) 0 = -RowAt.Uvec frame := by
    rw [← hU]
    ext <;> simp [PeriodDeck.combine]
  have hPl : l + ((0 : ℤ), (1 : ℤ)) = (z + ((0 : ℤ), (1 : ℤ))) + frame.child.modifiedDeck.combine (-1) 0 := by
    rw [hcomb_neg, hA]
    abel
  have hQl : l + ((1 : ℤ), (1 : ℤ)) = (z + ((1 : ℤ), (1 : ℤ))) + frame.child.modifiedDeck.combine (-1) 0 := by
    rw [hcomb_neg, hA]
    abel
  have hcolPl : laplacian F (l + ((0 : ℤ), (1 : ℤ))) = 0 := by
    rw [hPl, laplacian_add_combine hper]
    exact hcolP
  have hcolQl : laplacian F (l + ((1 : ℤ), (1 : ℤ))) = 0 := by
    rw [hQl, laplacian_add_combine hper]
    exact hcolQ
  have hnfPl : Nonfree frame (l + ((0 : ℤ), (1 : ℤ))) := by
    rw [hPl]
    exact PassageRank.nonfree_add_span frame hnfP ⟨-1, 0, rfl⟩
  have hnfQl : Nonfree frame (l + ((1 : ℤ), (1 : ℤ))) := by
    rw [hQl]
    exact PassageRank.nonfree_add_span frame hnfQ ⟨-1, 0, rfl⟩
  have hncfPl : ¬ FreeClosure.freeClosure frame (l + ((0 : ℤ), (1 : ℤ))) := by
    rintro ⟨s, hs, h⟩
    exact hnfPl s hs ((Set.mem_union _ _ _).2 h)
  have hncfQl : ¬ FreeClosure.freeClosure frame (l + ((1 : ℤ), (1 : ℤ))) := by
    rintro ⟨s, hs, h⟩
    exact hnfQl s hs ((Set.mem_union _ _ _).2 h)
  -- parities of the label, its north input and its east-north input
  have hPl_even : EvenSite (l + ((0 : ℤ), (1 : ℤ))) := by
    unfold EvenSite at hlodd ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hQl_odd : ¬ EvenSite (l + ((1 : ℤ), (1 : ℤ))) := by
    unfold EvenSite at hlodd ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  -- the label is white with its prescribed north input (odd entries)
  have hcomb_pos : frame.child.modifiedDeck.combine 1 0 = RowAt.Uvec frame := hU
  have hprescH : frame.prescribedH (-1) z = ((0 : ℤ), (1 : ℤ)) := by
    unfold ChildFrame.prescribedH
    rw [if_neg hdom, if_neg hlast, if_neg hodd]
  have hFP : FreePolicy.FreePresc frame (-1) l (l + ((0 : ℤ), (1 : ℤ))) := by
    refine ⟨frame.child.modifiedDeck.combine 1 0, ⟨1, 0, rfl⟩, Or.inl ⟨?_, ?_⟩⟩
    · rw [heU]
      exact hzfree
    · rw [heU, hprescH]
  have hfc : FreeClosure.freeClosure frame l := by
    refine ⟨frame.child.modifiedDeck.combine 1 0, ⟨1, 0, rfl⟩, Or.inl ?_⟩
    rw [heU]
    exact hzfree
  have hpermL : permitsQ1 frame F (-1) l (l + ((0 : ℤ), (1 : ℤ))) :=
    Or.inr ⟨hcol, Or.inl ⟨hfc, hFP⟩⟩
  -- the north input `p'` has the horizontal input `q'`
  have hQl_eq_pos : incomingPos (l + ((0 : ℤ), (1 : ℤ))) = l + ((1 : ℤ), (1 : ℤ)) := by
    unfold incomingPos
    rw [if_pos hPl_even]
    refine Prod.ext ?_ ?_
    · simp
    · simp
  have hpermP : permitsQ1 frame F (-1) (l + ((0 : ℤ), (1 : ℤ))) (l + ((1 : ℤ), (1 : ℤ))) :=
    Or.inr ⟨hcolPl, Or.inr ⟨hncfPl, Or.inr hQl_eq_pos.symm⟩⟩
  -- the east-north input `q'` has the vertical input `ℓ + (1,0)`, the earlier entry
  have hEneg : incomingNeg (l + ((1 : ℤ), (1 : ℤ))) = l + ((1 : ℤ), (0 : ℤ)) := by
    unfold incomingNeg
    rw [if_neg hQl_odd]
    refine Prod.ext ?_ ?_
    · simp
    · simp
  have hpermQ : permitsQ1 frame F (-1) (l + ((1 : ℤ), (1 : ℤ))) (RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den)) :=
    Or.inr ⟨hcolQl, Or.inr ⟨hncfQl, Or.inl (by rw [hE_l, hEneg])⟩⟩
  have hRq : Refuted frame F (-1) E C (l + ((1 : ℤ), (1 : ℤ))) :=
    Refuted.white hcolQl hpermQ (Refuted.earlier hE)
  have hRp : Refuted frame F (-1) E C (l + ((0 : ℤ), (1 : ℤ))) :=
    Refuted.white hcolPl hpermP hRq
  exact Refuted.white hcol hpermL hRp

end FLatticePaper.OddAxialRank
