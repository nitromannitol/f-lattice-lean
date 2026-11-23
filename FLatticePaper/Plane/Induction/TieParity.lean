import FLatticePaper.Plane.Induction.NegChart

/-! Task 69 (b): ties, option 1.

For a rising pair `(c, i)` for `σ` with `c + σ ∈ E`, the centre slip is
`D(c) = min (A c, C c) − min (A c, C c − 2)` (`F = sheetMin` on `E`, `A` is `σ`-periodic, `C (z + σ) = C z − 2`).
This is odd only when `Ψ c = C c − A c = 1`: `Ψ ≥ 2` gives `0`, `Ψ = 1` gives `1`, and `Ψ ≤ 0` gives `2`. So a tie at the
centre (and every `Ψ ≤ 0` centre) is excluded by parity, and a rising pair in option 1 has a strict root, which the first
chart excludes. This is the paper's "the first chart formula holds at ties" (task 69 (b), item 2). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The centre slip for `σ` with `c + σ ∈ E`: its parity forces `Ψ c = 1`. -/
theorem sheetDiffW_eq_one_of_parity {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {c : Site}
    (hcE : c ∈ (frameAt word).closedPolygon) (hcq : c + (frameAt word).shortShift ∈ (frameAt word).closedPolygon)
    (hpar : (standardField word c - standardField word (c + (frameAt word).shortShift)) % 2 = 1) :
    sheetDiffW word c = 1 := by
  have hFc := standardField_eq_sheetMin_of_strong h hSE hcE
  have hFs := standardField_eq_sheetMin_of_strong h hSE hcq
  unfold ChildFrame.sheetMin at hFc hFs
  rw [sheetA_add_shortShift h hSE c, sheetC_add_shortShift h hSE c] at hFs
  rw [hFc, hFs] at hpar
  have h1 := min_le_left ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c)
    ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) c)
  have h2 := min_le_right ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c)
    ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) c)
  have h3 := min_choice ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c)
    ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) c)
  have h4 := min_le_left ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c)
    ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) c - 2)
  have h5 := min_le_right ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c)
    ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) c - 2)
  have h6 := min_choice ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c)
    ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) c - 2)
  unfold sheetDiffW
  omega

/-- A rising `σ`-pair in option 1 (`c + σ, i + σ ∈ E`) is excluded: parity forces `Ψ c = 1`, and the first chart excludes
the strict root. Ties at the centre are excluded here with no further hypothesis. -/
theorem rising_option1_excluded {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    {c i : Site} (hr : RisingBlackPair (standardField word) (frameAt word).shortShift c i)
    (hcE : c ∈ (frameAt word).closedPolygon) (hiE : i ∈ (frameAt word).closedPolygon)
    (hcs : c + (frameAt word).shortShift ∈ (frameAt word).closedPolygon)
    (his : i + (frameAt word).shortShift ∈ (frameAt word).closedPolygon) : False := by
  have hΨ1 := sheetDiffW_eq_one_of_parity h hSE hcE hcs hr.2.2.1
  have hΨc : 1 ≤ sheetDiffW word c := by omega
  have hEdge : Edge i c := hr.1
  exact first_chart_excluded h hSE P
    (firstChart_witness h hSE P hcE hiE hEdge hcs his hΨc
      (sheetPolicyA_of_strict h hSE hpk P hcE hr hΨc)) hr

end FLatticePaper.Induction
