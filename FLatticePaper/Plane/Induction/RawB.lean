import FLatticePaper.Plane.Induction.SlipReflect

/-! Task 69 (b): the raw slip of the sheets, and `hbmono` derived from the policy's raw-slip field.

With `x = z − l_v`, the sheet difference `B z = C (z + εU_q) − A z` is paragraph 6's left side
`f (x − V_q) − f x + a_q·x + c_e` (`a_q·εU_q = 0`), which equals `(1 + ε) − Φ_ε (Z x)` with
`Φ_η y = G y − G (y + η σ_c)` the conjugate's raw slip (`paragraph6_of_strong`). So `B` is nondecreasing along the matched
edges, because `Φ_ε` is nonincreasing along the retained edges (`OldPolicyData.rawSlipNonincreasing`). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The shift `εU_q = ε (d_q, n_q)` of the even parent (the shift of the negative chart). -/
def ChildFrame.uq (frame : ChildFrame) : Site :=
  (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num)

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


theorem sheetB_eq {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (z : Site) :
    (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (z + (frameAt word).uq) -
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z =
      (1 + (frameAt word).eps) -
        (standardField (conjWord word) (-(z - (frameAt word).sheetShift).2, (z - (frameAt word).sheetShift).1 - 1) -
          standardField (conjWord word)
            ((-(z - (frameAt word).sheetShift).2, (z - (frameAt word).sheetShift).1 - 1) +
              (frameAt word).eps • (frameAt (conjWord word)).shortShift)) := by
  have key := paragraph6_of_strong h hSE (z - (frameAt word).sheetShift)
  have hsm : (frameAt word).eps • (frameAt (conjWord word)).shortShift =
      ((frameAt word).eps * (2 * (frameAt (conjWord word)).eps * (frameAt (conjWord word)).parents.odd.den),
        (frameAt word).eps * (2 * (frameAt (conjWord word)).eps * (frameAt (conjWord word)).parents.odd.num)) := by
    unfold ChildFrame.shortShift
    refine Prod.ext ?_ ?_
    · simp only [Prod.smul_fst, smul_eq_mul]
    · simp only [Prod.smul_snd, smul_eq_mul]
  have hoff : (frameAt word).sheetOffset =
      ((frameAt word).parents.even.num - (frameAt word).parents.even.den +
          (frameAt word).eps * (frameAt word).parents.even.den,
        (frameAt word).parents.even.num + (frameAt word).parents.even.den +
          (frameAt word).eps * (frameAt word).parents.even.num) := by
    unfold ChildFrame.sheetOffset
    refine Prod.ext ?_ ?_
    · simp only [Fraction.unmodifiedDeck, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    · simp only [Fraction.unmodifiedDeck, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  have e1 : z + (frameAt word).uq - (frameAt word).sheetShift - (frameAt word).sheetOffset =
      (z - (frameAt word).sheetShift) -
        ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den) := by
    rw [hoff]
    refine Prod.ext ?_ ?_
    · simp only [ChildFrame.uq, Prod.fst_sub, Prod.fst_add]
      ring
    · simp only [ChildFrame.uq, Prod.snd_sub, Prod.snd_add]
      ring
  have hsib : (frameAt word).siblingSlope (z + (frameAt word).uq - (frameAt word).sheetShift) =
      (frameAt word).siblingSlope (z - (frameAt word).sheetShift) := by
    unfold ChildFrame.siblingSlope ChildFrame.uq
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
    ring
  have hconst : (frameAt word).sheetConstant =
      ((frameAt word).parents.even.den ^ 2 + 2 * (frameAt word).parents.even.den * (frameAt word).parents.even.num -
          (frameAt word).parents.even.num ^ 2 - (frameAt word).parents.even.den - (frameAt word).parents.even.num) / 2 +
        2 * ((1 + (frameAt word).eps) / 2) := by
    unfold ChildFrame.sheetConstant ChildFrame.phaseW Fraction.periodDenominator
    ring_nf
  unfold ChildFrame.sheetC ChildFrame.sheetA
  rw [e1, hsib, hconst, hsm]
  unfold ChildFrame.siblingSlope at key ⊢
  linarith [key]

/-- `hbmono` from the policy's raw-slip field: `B` is nondecreasing along the matched edges. -/
theorem hbmono_of_raw {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (c i : Site) (hret : sheetPolicyA P (frameAt word).sheetShift c i) :
    (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (c + (frameAt word).uq) -
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c ≤
      (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) (i + (frameAt word).uq) -
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i := by
  have hmono := P.rawSlipNonincreasing
    (zTurn (c - (frameAt word).sheetShift)) (zTurn (i - (frameAt word).sheetShift)) hret
  dsimp only at hmono
  rw [sheetB_eq h hSE c, sheetB_eq h hSE i]
  unfold zTurn at hmono
  linarith [hmono]

/-- Reflection about an even centre `e` preserves edges (the two inputs are exchanged). -/
theorem reflect_edge_even (e : Site) (he : EvenSite e) {j c : Site} (h : Edge j c) :
    Edge (e - j) (e - c) := by
  have hiff : ∀ w : Site, EvenSite (e - w) ↔ EvenSite w := by
    intro w
    unfold EvenSite at he ⊢
    simp only [Prod.fst_sub, Prod.snd_sub]
    omega
  unfold Edge at h ⊢
  rcases h with h1 | h1
  · right
    rw [h1]
    unfold FLatticePaper.incomingNeg FLatticePaper.incomingPos
    by_cases hc : EvenSite c
    · rw [if_pos hc, if_pos ((hiff c).2 hc)]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_sub]
        try ring
      · simp only [Prod.snd_sub]
        try ring
    · rw [if_neg hc, if_neg (fun h' => hc ((hiff c).1 h'))]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_sub]
        try ring
      · simp only [Prod.snd_sub]
        try ring
  · left
    rw [h1]
    unfold FLatticePaper.incomingNeg FLatticePaper.incomingPos
    by_cases hc : EvenSite c
    · rw [if_pos hc, if_pos ((hiff c).2 hc)]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_sub]
        try ring
      · simp only [Prod.snd_sub]
        try ring
    · rw [if_neg hc, if_neg (fun h' => hc ((hiff c).1 h'))]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_sub]
        try ring
      · simp only [Prod.snd_sub]
        try ring

/-- The unit bound on the negative chart's jump `a`, from the unit increments of the conjugate's price (`HasUnitPrice`):
`|a c − a i| ≤ 1` for an edge `(i, c)`, with `a z = A (z + εU_q) − A z = c₀ − P'(Z (I − (z − l_v)))`. -/
theorem a_unit_bound {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {c i : Site} (hEdge : Edge i c) :
    (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (c + (frameAt word).uq) -
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c -
      ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (i + (frameAt word).uq) -
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i) ≤ 1 ∧
    -1 ≤ (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (c + (frameAt word).uq) -
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c -
      ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) (i + (frameAt word).uq) -
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i) := by
  have hlv : EvenSite (frameAt word).sheetShift := (frameAt word).evenSite_sheetShift
  have hE' : Edge (i - (frameAt word).sheetShift) (c - (frameAt word).sheetShift) := by
    unfold Edge at hEdge ⊢
    rcases hEdge with h1 | h1
    · left
      rw [h1, incomingNeg_sub_even' c _ hlv]
    · right
      rw [h1, incomingPos_sub_even' c _ hlv]
  have hR := reflect_edge_even (1, -1) (by unfold EvenSite; norm_num) hE'
  have hZ : Edge (zTurn ((1, -1) - (i - (frameAt word).sheetShift)))
      (zTurn ((1, -1) - (c - (frameAt word).sheetShift))) := i3_edge_Z hR
  have hU := hSE.F1_unitPrice _ _ hZ
  unfold priceIncrement at hU
  rw [sheetA_uq_eq_jumpA c, sheetA_uq_eq_jumpA i, jumpA_eq_cutPrice h hSE, jumpA_eq_cutPrice h hSE]
  constructor <;> linarith [hU.1, hU.2]

end FLatticePaper.Induction
