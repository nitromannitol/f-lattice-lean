import FLatticePaper.Plane.Induction.NegChart
import FLatticePaper.Plane.Induction.SheetCharts

/-! Task 72 (queue Q16 / hResP, the tied black centre): the sheet A is white and the A-policy retains the other input.

Let `A = sheetA Fp`, `C = sheetC Fp`, `M = standardField word = min(A, C)` on `E`, `Ψ = C − A`. For a black centre `c` of `M`
with `Ψ c = 0` and an input `j` with `Ψ j = −1`:

* `tie_sheetA_white`: `ΔA c = 0` and `A i = M i` for the other input `i` (the identity `ΔA − ΔM = Σ (A − M)` on the star, with
  `(A − M) j = 1`, and `ΔA ∈ {−1, 0}`).
* `sheetPolicyA_of_tie`: the A-policy retains `c → i` (the quota at the white conjugate root gives one retained input; the input
  `j` is not retained, since `sheetDiff_mono_A` would give `Ψ c ≤ Ψ j = −1`). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- If one of the two retained-by-quota inputs `q` is not retained, the other input `p` is. -/
theorem retained_of_quota {retained : Site → Site → Prop} {z p q : Site}
    (hquota : retained z (FLatticePaper.incomingNeg z) ∨ retained z (FLatticePaper.incomingPos z))
    (hp : p = FLatticePaper.incomingNeg z ∨ p = FLatticePaper.incomingPos z)
    (hq : q = FLatticePaper.incomingNeg z ∨ q = FLatticePaper.incomingPos z) (hpq : p ≠ q)
    (hnq : ¬ retained z q) : retained z p := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact absurd rfl hpq
  · exact hquota.resolve_right hnq
  · exact hquota.resolve_left hnq
  · exact absurd rfl hpq

/-- **The tied sheet A.** At a black centre of `M = standardField word` in `E` with `Ψ c = 0` and an input `j` with `Ψ j = −1`,
the sheet `A` is white at `c` and `A i = M i` for the other input `i`. -/
theorem tie_sheetA_white {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {c i j : Site} (hc : c ∈ (frameAt word).closedPolygon) (hi : Edge i c) (hj : Edge j c) (hij : i ≠ j)
    (hb : laplacian (standardField word) c = -1) (hΨc : sheetDiffW word c = 0) (hΨj : sheetDiffW word j ≤ -1) :
    laplacian ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word)))) c = 0 ∧
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) i ≤
        (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) i := by
  have hlv : EvenSite (frameAt word).sheetShift := (frameAt word).evenSite_sheetShift
  set Fp := quarterTurnField (standardField (conjWord word)) with hFp
  set A := (frameAt word).sheetA Fp with hA
  set C := (frameAt word).sheetC Fp with hC
  have hΨc' : C c - A c = 0 := hΨc
  have hΨj' : C j - A j ≤ -1 := hΨj
  have hG : ∀ z ∈ (frameAt word).closedPolygon, standardField word z = min (A z) (C z) := fun z hz =>
    standardField_eq_sheetMin_of_strong h hSE hz
  have hin1 : FLatticePaper.incomingNeg c ∈ (frameAt word).closedPolygon :=
    (frameAt word).black_input_mem hpk hc hb (Or.inl rfl)
  have hin2 : FLatticePaper.incomingPos c ∈ (frameAt word).closedPolygon :=
    (frameAt word).black_input_mem hpk hc hb (Or.inr rfl)
  have hiE : i ∈ (frameAt word).closedPolygon := (frameAt word).black_input_mem hpk hc hb hi
  have hjE : j ∈ (frameAt word).closedPolygon := (frameAt word).black_input_mem hpk hc hb hj
  -- the Laplacian of `A` is binary
  have hshiftLap : laplacian A c = laplacian Fp (c - (frameAt word).sheetShift) :=
    laplacian_sub_even Fp (frameAt word).sheetShift hlv c
  have hbinA : laplacian A c = -1 ∨ laplacian A c = 0 := by
    rw [hshiftLap]
    exact quarterTurnField_binary hSE.packet.binary _
  -- the min identity on the star of `c`
  have hMlap : laplacian (fun z => min (A z) (C z)) c = -1 := by
    unfold laplacian at hb ⊢
    simp only at ⊢
    rw [← hG c hc, ← hG _ hin1, ← hG _ hin2]
    exact hb
  have hMc : min (A c) (C c) = A c := by omega
  have hMj : min (A j) (C j) = C j := by omega
  unfold laplacian at hMlap hbinA ⊢
  simp only at hMlap
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact absurd rfl hij
  · constructor
    · omega
    · omega
  · constructor
    · omega
    · omega
  · exact absurd rfl hij

/-- **The A-policy retains the other input of a tied black centre.** -/
theorem sheetPolicyA_of_tie {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    {c i j : Site} (hc : c ∈ (frameAt word).closedPolygon) (hi : Edge i c) (hj : Edge j c) (hij : i ≠ j)
    (hb : laplacian (standardField word) c = -1) (hΨc : sheetDiffW word c = 0) (hΨj : sheetDiffW word j ≤ -1) :
    sheetPolicyA P (frameAt word).sheetShift c i := by
  have hlv : EvenSite (frameAt word).sheetShift := (frameAt word).evenSite_sheetShift
  obtain ⟨hwhite, -⟩ := tie_sheetA_white h hSE hpk hc hi hj hij hb hΨc hΨj
  have hshiftLap : laplacian ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word)))) c =
      laplacian (quarterTurnField (standardField (conjWord word))) (c - (frameAt word).sheetShift) :=
    laplacian_sub_even (quarterTurnField (standardField (conjWord word))) (frameAt word).sheetShift hlv c
  have hq : laplacian (quarterTurnField (standardField (conjWord word))) (c - (frameAt word).sheetShift) =
      laplacian (standardField (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) :=
    i3_laplacian_quarterTurn (standardField (conjWord word)) (c - (frameAt word).sheetShift)
  have hzero : laplacian (standardField (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) = 0 := by
    rw [← hq, ← hshiftLap]
    exact hwhite
  have hquota := P.quota.2 (zTurn (c - (frameAt word).sheetShift)) hzero
  have hEi : Edge (i - (frameAt word).sheetShift) (c - (frameAt word).sheetShift) := by
    unfold Edge at hi ⊢
    rcases hi with h1 | h1
    · left
      rw [h1, incomingNeg_sub_even' c _ hlv]
    · right
      rw [h1, incomingPos_sub_even' c _ hlv]
  have hEj : Edge (j - (frameAt word).sheetShift) (c - (frameAt word).sheetShift) := by
    unfold Edge at hj ⊢
    rcases hj with h1 | h1
    · left
      rw [h1, incomingNeg_sub_even' c _ hlv]
    · right
      rw [h1, incomingPos_sub_even' c _ hlv]
  have hpz : Edge (zTurn (i - (frameAt word).sheetShift)) (zTurn (c - (frameAt word).sheetShift)) :=
    i3_edge_Z hEi
  have hqz : Edge (zTurn (j - (frameAt word).sheetShift)) (zTurn (c - (frameAt word).sheetShift)) :=
    i3_edge_Z hEj
  have hne : zTurn (i - (frameAt word).sheetShift) ≠ zTurn (j - (frameAt word).sheetShift) := by
    intro he
    apply hij
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    simp only [zTurn, Prod.fst_sub, Prod.snd_sub] at h1 h2
    exact Prod.ext (by omega) (by omega)
  -- the other input is not retained: the monotone A-policy would give `Ψ c ≤ Ψ j = −1`
  have hnj : ¬ P.retained (zTurn (c - (frameAt word).sheetShift)) (zTurn (j - (frameAt word).sheetShift)) := by
    intro hr
    have hmono := sheetDiff_mono_A h hSE P (c := c) (i := j) (by
      dsimp only [sheetPolicyA, parentPolicy]
      exact hr)
    have hc' := hmono
    rw [hΨc] at hc'
    omega
  have hret := retained_of_quota hquota hpz hqz hne hnj
  dsimp only [sheetPolicyA, parentPolicy]
  exact hret

end FLatticePaper.Induction
