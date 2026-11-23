import FLatticePaper.Plane.Induction.TwosTile

/-! Task 36 (hbaseTwoId), step 3: the nine neighbour cases of the tile identity on the alternate tile. Each case is a lemma
whose heartbeat use is kept within the default budget by proving the piecewise relation (`C7_Q`) first and closing the
identity with a linear `omega` on facts without disjunctions. -/

namespace FLatticePaper.Induction.TwosTile

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Induction.TwosBaseIdentity

/-- The bump indicators and the piecewise terms of the dominant case: the relation `Q = 0` that makes the identity exact. -/
theorem C7_Q (d : ℤ) (hd : 4 ≤ d) (w : Site)
    (hw : w ∈ (BaseMask.ladderOddAlt.raw d).sites)
    (hqa : (w.1 + 2, w.2) ∈ (BaseMask.ladderOdd.raw d).sites)
    (hqb : (w.1 + 1, w.2 + 1) ∈ (BaseMask.ladderOdd.raw d).sites) :
    -1 ≤ (min 0 (w.1 + 1) - min 0 w.1 - min (d - 1 - w.1) 0 + min (d - w.1) 0) +
      ((if BaseMask.LadderOddBump d (w.1 + 2, w.2) then (1 : ℤ) else 0) +
        (if BaseMask.LadderOddBump d (w.1 + 1, w.2 + 1) then 1 else 0) -
          2 * (if BaseMask.LadderOddAltCorner d w ∨ BaseMask.LadderOddAltDiagonal d w then 1 else 0)) - 1 ∧
    (min 0 (w.1 + 1) - min 0 w.1 - min (d - 1 - w.1) 0 + min (d - w.1) 0) +
      ((if BaseMask.LadderOddBump d (w.1 + 2, w.2) then (1 : ℤ) else 0) +
        (if BaseMask.LadderOddBump d (w.1 + 1, w.2 + 1) then 1 else 0) -
          2 * (if BaseMask.LadderOddAltCorner d w ∨ BaseMask.LadderOddAltDiagonal d w then 1 else 0)) - 1 ≤ 0 := by
  rw [BaseMask.mem_ladderOdd_raw_iff] at hqa hqb
  rw [BaseMask.mem_ladderOddAlt_raw_iff] at hw
  simp only [not_and_or, not_or, not_le] at hqa hqb hw
  by_cases h1 : BaseMask.LadderOddBump d (w.1 + 2, w.2)
  <;> by_cases h2 : BaseMask.LadderOddBump d (w.1 + 1, w.2 + 1)
  <;> by_cases h3 : BaseMask.LadderOddAltCorner d w ∨ BaseMask.LadderOddAltDiagonal d w
  <;> simp only [h1, h2, h3, if_true, if_false] at ⊢
  <;> (try unfold BaseMask.LadderOddBump at h1 h2)
  <;> (try rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ | ⟨h1a, h1b, h1c⟩)
  <;> (try rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ | ⟨h2a, h2b, h2c⟩)
  <;> (try unfold BaseMask.LadderOddAltCorner BaseMask.LadderOddAltDiagonal at h3)
  <;> (try rcases h3 with (⟨h3a, h3b⟩ | ⟨h3a, h3b⟩) | ⟨h3a, h3b, h3c⟩)
  <;> (try clear h1 h2 h3)
  <;> omega


/-- The dominant case: the twos midpoint at `w`, with `w + (2,0)` and `w + (d,-d)` reduced into the odd tile by one step. -/
theorem leaf_C7 (d : ℤ) (hd : 4 ≤ d) (hcV : 2 * stairEvenConstantV d = -d ^ 2 - 3 * d) (w : Site)
    (hw : w ∈ (BaseMask.ladderOddAlt.raw d).sites)
    (hqa : (w.1 + 2, w.2) ∈ (BaseMask.ladderOdd.raw d).sites)
    (hqb : (w.1 + 1, w.2 + 1) ∈ (BaseMask.ladderOdd.raw d).sites) :
    halfCeil (BaseMask.ladderOddValue d (w.1 + 2, w.2) + BaseMask.ladderOddValue d (w.1 + 1, w.2 + 1) -
        stairEvenConstantV d + (d * (w.2 + 1) - (w.1 + 1)) - (d ^ 2 + 2 * d - 1) + dcorr d w) - w.2 =
      BaseMask.ladderOddAltValue d w := by
  have ha := two_mul_ladderOddValue d (w.1 + 2, w.2)
  have hb := two_mul_ladderOddValue d (w.1 + 1, w.2 + 1)
  have hc := two_mul_ladderOddAltValue d w
  have hk := two_mul_dcorr_half d
  have hQ := C7_Q d hd w hw hqa hqb
  dsimp only at ha hb
  unfold dcorr halfCeil
  generalize BaseMask.ladderOddValue d (w.1 + 2, w.2) = Va at *
  generalize BaseMask.ladderOddValue d (w.1 + 1, w.2 + 1) = Vb at *
  generalize BaseMask.ladderOddAltValue d w = Aw at *
  generalize d * (d + 1) / 2 = K at *
  generalize (if BaseMask.LadderOddBump d (w.1 + 2, w.2) then (1 : ℤ) else 0) = bA at ha hQ
  generalize (if BaseMask.LadderOddBump d (w.1 + 1, w.2 + 1) then (1 : ℤ) else 0) = bB at hb hQ
  generalize (if BaseMask.LadderOddAltCorner d w ∨ BaseMask.LadderOddAltDiagonal d w then (1 : ℤ) else 0) = bW at hc hQ
  clear hqa hqb hw
  ring_nf at ha hb hc hcV hk ⊢
  omega


theorem C2_Q (d : ℤ) (hd : 4 ≤ d) (w : Site)
    (hw : w ∈ (BaseMask.ladderOddAlt.raw d).sites)
    (hqa : (w.1 + 2 * d + 2, w.2 + 2) ∈ (BaseMask.ladderOdd.raw d).sites)
    (hqb : (w.1 + 2 * d + 1, w.2 + 3) ∈ (BaseMask.ladderOdd.raw d).sites) :
    -1 ≤ (min (-w.1 - d - 1) 0 + min (-w.1 - d) 0 - 2 * min (-w.1 + d - 1) 0 - 2 * min (w.1) 0 + min (w.1 + 2 * d) 0 + min (w.1 + 2 * d + 1) 0 + 2 * min (w.1 + w.2 - d) 0 - 2 * min (w.1 + w.2 + d + 2) 0 + (if BaseMask.LadderOddBump d (w.1 + 2 * d + 2, w.2 + 2) then (1 : ℤ) else 0) + (if BaseMask.LadderOddBump d (w.1 + 2 * d + 1, w.2 + 3) then (1 : ℤ) else 0) - 2 * (if BaseMask.LadderOddAltCorner d w ∨ BaseMask.LadderOddAltDiagonal d w then (1 : ℤ) else 0) - 1 + 4 * d - 4 * w.2) ∧ (min (-w.1 - d - 1) 0 + min (-w.1 - d) 0 - 2 * min (-w.1 + d - 1) 0 - 2 * min (w.1) 0 + min (w.1 + 2 * d) 0 + min (w.1 + 2 * d + 1) 0 + 2 * min (w.1 + w.2 - d) 0 - 2 * min (w.1 + w.2 + d + 2) 0 + (if BaseMask.LadderOddBump d (w.1 + 2 * d + 2, w.2 + 2) then (1 : ℤ) else 0) + (if BaseMask.LadderOddBump d (w.1 + 2 * d + 1, w.2 + 3) then (1 : ℤ) else 0) - 2 * (if BaseMask.LadderOddAltCorner d w ∨ BaseMask.LadderOddAltDiagonal d w then (1 : ℤ) else 0) - 1 + 4 * d - 4 * w.2) ≤ 0 := by
  rw [BaseMask.mem_ladderOdd_raw_iff] at hqa hqb
  rw [BaseMask.mem_ladderOddAlt_raw_iff] at hw
  simp only [not_and_or, not_or, not_le] at hqa hqb hw
  by_cases h1 : BaseMask.LadderOddBump d (w.1 + 2 * d + 2, w.2 + 2)
  <;> by_cases h2 : BaseMask.LadderOddBump d (w.1 + 2 * d + 1, w.2 + 3)
  <;> by_cases h3 : BaseMask.LadderOddAltCorner d w ∨ BaseMask.LadderOddAltDiagonal d w
  <;> simp only [h1, h2, h3, if_true, if_false] at ⊢
  <;> (try unfold BaseMask.LadderOddBump at h1 h2)
  <;> (try rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ | ⟨h1a, h1b, h1c⟩)
  <;> (try rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ | ⟨h2a, h2b, h2c⟩)
  <;> (try unfold BaseMask.LadderOddAltCorner BaseMask.LadderOddAltDiagonal at h3)
  <;> (try rcases h3 with (⟨h3a, h3b⟩ | ⟨h3a, h3b⟩) | ⟨h3a, h3b, h3c⟩)
  <;> (try clear h1 h2 h3)
  <;> omega

theorem leaf_C2 (d : ℤ) (hd : 4 ≤ d) (hcV : 2 * stairEvenConstantV d = -d ^ 2 - 3 * d) (w : Site)
    (hw : w ∈ (BaseMask.ladderOddAlt.raw d).sites)
    (hqa : (w.1 + 2 * d + 2, w.2 + 2) ∈ (BaseMask.ladderOdd.raw d).sites)
    (hqb : (w.1 + 2 * d + 1, w.2 + 3) ∈ (BaseMask.ladderOdd.raw d).sites) :
    halfCeil (BaseMask.ladderOddValue d (w.1 + 2 * d + 2, w.2 + 2) + BaseMask.ladderOddValue d (w.1 + 2 * d + 1, w.2 + 3) + (0 * (stairEvenConstantV d - (d * (w.2 + 2) - (w.1 + 2 * d + 2))) - (d ^ 2 + 2 * d - 1) * (0)) + (-1 * (stairEvenConstantV d - (d * (w.2 + 3) - (w.1 + 2 * d + 1))) - (d ^ 2 + 2 * d - 1) * (1)) +
        dcorr d w) - w.2 = BaseMask.ladderOddAltValue d w := by
  have ha := two_mul_ladderOddValue d (w.1 + 2 * d + 2, w.2 + 2)
  have hb := two_mul_ladderOddValue d (w.1 + 2 * d + 1, w.2 + 3)
  have hc := two_mul_ladderOddAltValue d w
  have hk := two_mul_dcorr_half d
  have hQ := C2_Q d hd w hw hqa hqb
  dsimp only at ha hb
  unfold dcorr halfCeil
  generalize BaseMask.ladderOddValue d (w.1 + 2 * d + 2, w.2 + 2) = Va at *
  generalize BaseMask.ladderOddValue d (w.1 + 2 * d + 1, w.2 + 3) = Vb at *
  generalize BaseMask.ladderOddAltValue d w = Aw at *
  generalize d * (d + 1) / 2 = K at *
  generalize (if BaseMask.LadderOddBump d (w.1 + 2 * d + 2, w.2 + 2) then (1 : ℤ) else 0) = bA at ha hQ
  generalize (if BaseMask.LadderOddBump d (w.1 + 2 * d + 1, w.2 + 3) then (1 : ℤ) else 0) = bB at hb hQ
  generalize (if BaseMask.LadderOddAltCorner d w ∨ BaseMask.LadderOddAltDiagonal d w then (1 : ℤ) else 0) = bW at hc hQ
  clear hqa hqb hw
  ring_nf at ha hb hc hcV hk ⊢
  omega

theorem C6_Q (d : ℤ) (hd : 4 ≤ d) (w : Site)
    (hw : w ∈ (BaseMask.ladderOddAlt.raw d).sites)
    (hqa : (w.1 + 2, w.2) ∈ (BaseMask.ladderOdd.raw d).sites)
    (hqb : (w.1 + 2 * d + 1, w.2 + 3) ∈ (BaseMask.ladderOdd.raw d).sites) :
    -1 ≤ (min (-w.1 - d) 0 - min (-w.1 + d - 1) 0 - 2 * min (w.1) 0 + min (w.1 + 1) 0 + min (w.1 + 2 * d) 0 + min (w.1 + w.2 - d) 0 - min (w.1 + w.2 + d + 2) 0 + (if BaseMask.LadderOddBump d (w.1 + 2, w.2) then (1 : ℤ) else 0) + (if BaseMask.LadderOddBump d (w.1 + 2 * d + 1, w.2 + 3) then (1 : ℤ) else 0) - 2 * (if BaseMask.LadderOddAltCorner d w ∨ BaseMask.LadderOddAltDiagonal d w then (1 : ℤ) else 0) - 2 + 2 * d - 2 * w.2) ∧ (min (-w.1 - d) 0 - min (-w.1 + d - 1) 0 - 2 * min (w.1) 0 + min (w.1 + 1) 0 + min (w.1 + 2 * d) 0 + min (w.1 + w.2 - d) 0 - min (w.1 + w.2 + d + 2) 0 + (if BaseMask.LadderOddBump d (w.1 + 2, w.2) then (1 : ℤ) else 0) + (if BaseMask.LadderOddBump d (w.1 + 2 * d + 1, w.2 + 3) then (1 : ℤ) else 0) - 2 * (if BaseMask.LadderOddAltCorner d w ∨ BaseMask.LadderOddAltDiagonal d w then (1 : ℤ) else 0) - 2 + 2 * d - 2 * w.2) ≤ 0 := by
  rw [BaseMask.mem_ladderOdd_raw_iff] at hqa hqb
  rw [BaseMask.mem_ladderOddAlt_raw_iff] at hw
  simp only [not_and_or, not_or, not_le] at hqa hqb hw
  by_cases h1 : BaseMask.LadderOddBump d (w.1 + 2, w.2)
  <;> by_cases h2 : BaseMask.LadderOddBump d (w.1 + 2 * d + 1, w.2 + 3)
  <;> by_cases h3 : BaseMask.LadderOddAltCorner d w ∨ BaseMask.LadderOddAltDiagonal d w
  <;> simp only [h1, h2, h3, if_true, if_false] at ⊢
  <;> (try unfold BaseMask.LadderOddBump at h1 h2)
  <;> (try rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ | ⟨h1a, h1b, h1c⟩)
  <;> (try rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ | ⟨h2a, h2b, h2c⟩)
  <;> (try unfold BaseMask.LadderOddAltCorner BaseMask.LadderOddAltDiagonal at h3)
  <;> (try rcases h3 with (⟨h3a, h3b⟩ | ⟨h3a, h3b⟩) | ⟨h3a, h3b, h3c⟩)
  <;> (try clear h1 h2 h3)
  <;> omega

theorem leaf_C6 (d : ℤ) (hd : 4 ≤ d) (hcV : 2 * stairEvenConstantV d = -d ^ 2 - 3 * d) (w : Site)
    (hw : w ∈ (BaseMask.ladderOddAlt.raw d).sites)
    (hqa : (w.1 + 2, w.2) ∈ (BaseMask.ladderOdd.raw d).sites)
    (hqb : (w.1 + 2 * d + 1, w.2 + 3) ∈ (BaseMask.ladderOdd.raw d).sites) :
    halfCeil (BaseMask.ladderOddValue d (w.1 + 2, w.2) + BaseMask.ladderOddValue d (w.1 + 2 * d + 1, w.2 + 3) + (0 * (stairEvenConstantV d - (d * (w.2) - (w.1 + 2))) - (d ^ 2 + 2 * d - 1) * (0)) + (-1 * (stairEvenConstantV d - (d * (w.2 + 3) - (w.1 + 2 * d + 1))) - (d ^ 2 + 2 * d - 1) * (1)) +
        dcorr d w) - w.2 = BaseMask.ladderOddAltValue d w := by
  have ha := two_mul_ladderOddValue d (w.1 + 2, w.2)
  have hb := two_mul_ladderOddValue d (w.1 + 2 * d + 1, w.2 + 3)
  have hc := two_mul_ladderOddAltValue d w
  have hk := two_mul_dcorr_half d
  have hQ := C6_Q d hd w hw hqa hqb
  dsimp only at ha hb
  unfold dcorr halfCeil
  generalize BaseMask.ladderOddValue d (w.1 + 2, w.2) = Va at *
  generalize BaseMask.ladderOddValue d (w.1 + 2 * d + 1, w.2 + 3) = Vb at *
  generalize BaseMask.ladderOddAltValue d w = Aw at *
  generalize d * (d + 1) / 2 = K at *
  generalize (if BaseMask.LadderOddBump d (w.1 + 2, w.2) then (1 : ℤ) else 0) = bA at ha hQ
  generalize (if BaseMask.LadderOddBump d (w.1 + 2 * d + 1, w.2 + 3) then (1 : ℤ) else 0) = bB at hb hQ
  generalize (if BaseMask.LadderOddAltCorner d w ∨ BaseMask.LadderOddAltDiagonal d w then (1 : ℤ) else 0) = bW at hc hQ
  clear hqa hqb hw
  ring_nf at ha hb hc hcV hk ⊢
  omega

end FLatticePaper.Induction.TwosTile
