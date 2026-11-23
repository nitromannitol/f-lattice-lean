import FLatticePaper.Plane.Induction.SheetCases
import FLatticePaper.Plane.Induction.I3CSheet
import FLatticePaper.Plane.Induction.I3Application
import FLatticePaper.Plane.Induction.SheetMinRank
import FLatticePaper.Plane.Induction.Q3VStar

/-! Task 64: `Ψ = C − A` at word level, the first and adjacent charts, and `hT`.

* (a) `sheetDiff_eq_neg_chain`: `Ψ(z) = −Ξ(z − l_v) + K` for a constant `K`, where `Ξ` is the sheet chain potential of
  the word (`i3_sheet_eq_chainPotential`). From `i3_chainSheet_identity`, `chainPotential = G − chainSheet` and
  `quarterTurnField G = G ∘ Z + h₀`. Consequently the unit bound of `Ξ` (`i3_sheet_unit_of_strong`) gives the unit bound of `Ψ`
  on edges, and the chain monotonicity of the conjugate policy (`chainNonincreasing`) gives `Ψ` nondecreasing along the
  A-policy edges (`sheetDiff_mono_A`). `sheetMin_A_of_strict_root`: a strict root selects the `A` sheet at its inputs.
* (b) `first_chart_excluded`: in the first common chart (both ends `A`, the shifted value minus `A` equal to
  `min(0, Ψ − 2)`), `D_1 = max(0, 2 − Ψ)` and `Ψ` does not decrease along the retained edge, so no rise.
* (c) `adjacent_chart_excluded`: at a strict `A` target (`Ψ(i) ≥ 1`) the shifted value minus `A` is `p(x_i)`, at the root it
  is at most `p(x_c)`, and `p` does not decrease along the retained edge, so no rise.
* (d) `exceptional_hT_proved`: `a(v − (1,0)) = p(1,0) + 1` from `v − (1,0) = (0,−1) + V_p`, `aVal_translate_V` and the
  reflection `a(x) = p(I − x)`.

Named (cover): the cover of a rising black pair by the cases, and the exit leaf. The chart formulas are the paper's
computations of the shifted value in each chart; they are part of the cover's witnesses (`FirstChartEdge`,
`AdjacentChartEdge`). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- `Ψ = C − A` of the word's two sheets on the parent field `f = quarterTurnField G`, `G = standardField (conjWord word)`. -/
noncomputable def sheetDiffW (word : Word) (z : Site) : ℤ :=
  (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) z -
    (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z

/-- The paragraph-5 price `p(x) = c₀ − P'(Zx)` of the conjugate, as a function of the sheet coordinate. -/
noncomputable def pW (word : Word) (x : Site) : ℤ :=
  (frameAt (conjWord word)).cutPrice -
    (frameAt (conjWord word)).price (standardField (conjWord word)) (zTurn x)

/-- (a) `Ψ(z) = −Ξ(z − l_v) + K`: the sheet difference is the negated sheet chain potential at the sheet coordinate. -/
theorem sheetDiff_eq_neg_chain {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) :
    ∃ K : ℤ, ∀ z : Site, sheetDiffW word z =
      -sheetChainPotential word (standardField (conjWord word)) (z - (frameAt word).sheetShift) + K := by
  obtain ⟨K', hK⟩ := i3_chainSheet_identity hw hSE.packet
  refine ⟨(frameAt word).sheetConstant - K', fun z => ?_⟩
  have hΞ := i3_sheet_eq_chainPotential word (standardField (conjWord word)) (z - (frameAt word).sheetShift)
  rw [hΞ, ChildFrame.chainPotential_eq_sub_chainSheet, hK (z - (frameAt word).sheetShift)]
  have hq : quarterTurnField (standardField (conjWord word)) (z - (frameAt word).sheetShift) =
      standardField (conjWord word) (i3Z (z - (frameAt word).sheetShift)) +
        harmonicGrid (z - (frameAt word).sheetShift) := by
    unfold quarterTurnField
    rw [i3_mapSite_eq]
  unfold sheetDiffW ChildFrame.sheetC ChildFrame.sheetA
  linarith

/-- The unit bound of `Ψ` on the edges `Edge i c` (from the unit bound of `Ξ`, translated by the even `−l_v`). -/
theorem sheetDiff_unit {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) :
    ∀ c i : Site, Edge i c →
      -1 ≤ sheetDiffW word i - sheetDiffW word c ∧ sheetDiffW word i - sheetDiffW word c ≤ 1 := by
  intro c i hic
  obtain ⟨K, hK⟩ := sheetDiff_eq_neg_chain hw hSE
  have hE := i3_edge_translate (-(frameAt word).sheetShift)
    (evenSite_neg_site _ (frameAt word).evenSite_sheetShift) hic
  have hu := i3_sheet_unit_of_strong hSE (c + -(frameAt word).sheetShift) (i + -(frameAt word).sheetShift) hE
  simp only [← sub_eq_add_neg] at hu
  rw [hK i, hK c]
  obtain ⟨hu1, hu2⟩ := hu
  constructor <;> linarith

/-- (a) `Ψ` does not decrease along the A-policy edges: the conjugate chain potential does not increase along the retained
edges, at the sheet coordinates `c − l_v`, `i − l_v`. -/
theorem sheetDiff_mono_A {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    {c i : Site} (h : sheetPolicyA P (frameAt word).sheetShift c i) :
    sheetDiffW word c ≤ sheetDiffW word i := by
  obtain ⟨K, hK⟩ := sheetDiff_eq_neg_chain hw hSE
  have hmono := P.chainNonincreasing (frameAt word).eps (frameAt word).eps_unit
    (zTurn (c - (frameAt word).sheetShift)) (zTurn (i - (frameAt word).sheetShift)) h
  have key : sheetChainPotential word (standardField (conjWord word)) (i - (frameAt word).sheetShift) ≤
      sheetChainPotential word (standardField (conjWord word)) (c - (frameAt word).sheetShift) := by
    rw [i3_sheet_eq_chainPotential, i3_sheet_eq_chainPotential]
    exact hmono
  rw [hK c, hK i]
  linarith

/-- Paragraph 3, strict root: `Ψ(c) ≥ 1` selects the `A` sheet at each input `i` of `c`. -/
theorem sheetMin_A_of_strict_root {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {c i : Site} (hEdge : Edge i c) (hc : 1 ≤ sheetDiffW word c) :
    (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) i =
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i := by
  have hu := (sheetDiff_unit hw hSE c i hEdge).1
  unfold sheetDiffW at hc hu
  exact sheetMin_A_at_input (frameAt word) _ hc (by linarith)

/-- The first common chart (paragraph 4, `η = 1`): both ends in the active sheet `A`, the shifted value minus `A` equal to
`min(0, Ψ − 2)` at both ends (the paper's chart formula, part of the cover's witness), and the edge retained by the
A-policy. -/
def FirstChartEdge {word : Word} {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed) (c i : Site) : Prop :=
  standardField word c = (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c ∧
  standardField word i = (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i ∧
  standardField word (c + (frameAt word).shortShift) -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c =
    min 0 (sheetDiffW word c - 2) ∧
  standardField word (i + (frameAt word).shortShift) -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i =
    min 0 (sheetDiffW word i - 2) ∧
  sheetPolicyA P (frameAt word).sheetShift c i

/-- (b) A rise is impossible in the first common chart. -/
theorem first_chart_excluded {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed) {c i : Site}
    (h : FirstChartEdge P c i) :
    ¬ RisingBlackPair (standardField word) (frameAt word).shortShift c i := by
  intro hr
  obtain ⟨hFc, hFi, hcc, hci, hpol⟩ := h
  obtain ⟨-, -, -, -, hone⟩ := hr
  have hmono := sheetDiff_mono_A hw hSE P hpol
  have hmin : min 0 (sheetDiffW word c - 2) ≤ min 0 (sheetDiffW word i - 2) :=
    min_le_min le_rfl (by linarith)
  simp only [slipIncrement] at hone
  linarith

/-- The adjacent chart (paragraph 5, `η = 1`): a strict `A` target (`Ψ(i) ≥ 1`), both ends in `A`, the shifted value minus
`A` equal to `min{p(x), Ψ + p(x − e)}` at `x = z − l_v` (the paper's chart formula, part of the cover's witness), and the edge
retained by the A-policy. -/
def AdjacentChartEdge {word : Word} {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed) (c i : Site) : Prop :=
  standardField word c = (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c ∧
  standardField word i = (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i ∧
  1 ≤ sheetDiffW word i ∧
  standardField word (c + (frameAt word).shortShift) -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c =
    min (pW word (c - (frameAt word).sheetShift))
      (sheetDiffW word c + pW word (c - (frameAt word).sheetShift - (frameAt word).sheetStep)) ∧
  standardField word (i + (frameAt word).shortShift) -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i =
    min (pW word (i - (frameAt word).sheetShift))
      (sheetDiffW word i + pW word (i - (frameAt word).sheetShift - (frameAt word).sheetStep)) ∧
  sheetPolicyA P (frameAt word).sheetShift c i

/-- (c) A rise is impossible in the adjacent chart: at the strict target the value is `p(x_i)`, at the root it is at most
`p(x_c)`, and `p` does not decrease along the retained edge. -/
theorem adjacent_chart_excluded {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed) {c i : Site}
    (h : AdjacentChartEdge P c i) :
    ¬ RisingBlackPair (standardField word) (frameAt word).shortShift c i := by
  intro hr
  obtain ⟨hFc, hFi, hΨi, hcc, hci, hpol⟩ := h
  obtain ⟨-, -, -, -, hone⟩ := hr
  have hp : (frameAt (conjWord word)).cutPrice -
        (frameAt (conjWord word)).price (standardField (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) ≤
      (frameAt (conjWord word)).cutPrice -
        (frameAt (conjWord word)).price (standardField (conjWord word)) (zTurn (i - (frameAt word).sheetShift)) :=
    sheetPolicyA_price P (frameAt word).sheetShift c i hpol
  have hfo : min (pW word (i - (frameAt word).sheetShift))
      (sheetDiffW word i + pW word (i - (frameAt word).sheetShift - (frameAt word).sheetStep)) =
      pW word (i - (frameAt word).sheetShift) :=
    first_offer_of_strict hw hSE (i - (frameAt word).sheetShift) hΨi
  have hroot : min (pW word (c - (frameAt word).sheetShift))
      (sheetDiffW word c + pW word (c - (frameAt word).sheetShift - (frameAt word).sheetStep)) ≤
      pW word (c - (frameAt word).sheetShift) := min_le_left _ _
  unfold pW at hfo hroot hcc hci
  simp only [slipIncrement] at hone
  linarith

/-- Paragraph 7 in the form used for `hT`: the jump `a(x) = f(x + εU_q) − f(x)` is the paragraph-5 price `p(I − x)`. -/
theorem jumpA_eq_pJump {word : Word} (hSE : StrongEstimates (conjWord word)) (x : Site) :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x =
      pJump (frameAt word) (quarterTurnField (standardField (conjWord word))) ((1, -1) - x) := by
  unfold jumpA pJump
  rw [paragraph7_of_strong hSE x]
  have e : (1, -1) - x + (-((frameAt word).eps * (frameAt word).parents.even.den),
      -((frameAt word).eps * (frameAt word).parents.even.num)) =
      (1, -1) - x - ((frameAt word).eps * (frameAt word).parents.even.den,
        (frameAt word).eps * (frameAt word).parents.even.num) := by
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;> ring
  rw [e]

/-- (d) The exceptional drop value: `a(v − (1,0)) = p(1,0) + 1`, from `v − (1,0) = (0,−1) + V_p`, `aVal_translate_V` and the
reflection `a(x) = p(I − x)` (paragraph 7). -/
theorem exceptional_hT_proved {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word)))
        (excVertex (frameAt word) - (1, 0)) =
      pJump (frameAt word) (quarterTurnField (standardField (conjWord word))) (1, 0) + 1 := by
  have hx : excVertex (frameAt word) - (1, 0) =
      (0, -1) + ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den) := by
    unfold excVertex
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;> ring
  rw [hx]
  have h1 : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word)))
      ((0, -1) + ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den)) =
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) (0, -1) + 1 :=
    aVal_translate_V h hSE (0, -1)
  have h2 := jumpA_eq_pJump hSE (0, -1)
  have h3 : ((1 : ℤ), (-1 : ℤ)) - ((0 : ℤ), (-1 : ℤ)) = ((1 : ℤ), (0 : ℤ)) := by
    ext <;> simp
  rw [h3] at h2
  rw [h1, h2]

/-- The cover of a rising black pair (named) and the exit leaf (named); the first chart, the adjacent chart, the nonfree and
exceptional drops, the H drop (with the named `hweb` inside the cover) and the free V block are closed. -/
theorem noBlackPairRise_of_charts {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (exitSameSlip : Site → Site → Prop)
    (hcover : ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
      FirstChartEdge P c i ∨ AdjacentChartEdge P c i ∨ exitSameSlip c i ∨
      (∃ x x', parentPolicy P x x' ∧
        jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = 1 ∧
        jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x' = 0) ∨
      (∃ x, HRootWeb (frameAt word).parents.odd.num (frameAt word).parents.odd.den
          ((frameAt word).parentTGrade x) ∧
        jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = 1) ∨
      ChildFrame.BlockPairAt (frameAt word) c ∨
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word)))
        (excVertex (frameAt word) - (1, 0)) = 0)
    (hexit : ∀ c i, exitSameSlip c i → ¬ RisingBlackPair (standardField word) (frameAt word).shortShift c i) :
    NoBlackPairRise (standardField word) (frameAt word).shortShift := by
  intro c hc hpar hbs i hi hone
  have hr : RisingBlackPair (standardField word) (frameAt word).shortShift c i := ⟨hi, hc, hpar, hbs, hone⟩
  rcases hcover c i hr with h1 | h1 | h1 | ⟨x, x', hpol, j1, j0⟩ | ⟨x, hw', j1⟩ | hblk | j0
  · exact first_chart_excluded hw hSE P h1 hr
  · exact adjacent_chart_excluded hw hSE P h1 hr
  · exact hexit c i h1 hr
  · exact nonfree_drop_excluded hw hSE P hpol j1 j0
  · exact H_drop_excluded hw hSE x hw' j1
  · exact (frameAt word).not_rising_of_blockPair hpk hc hbs hblk
  · exact exceptional_drop_excluded hw hSE _ (exceptional_hT_proved hw hSE) j0

end FLatticePaper.Induction
