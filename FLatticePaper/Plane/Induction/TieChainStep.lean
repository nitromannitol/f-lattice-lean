import Mathlib.Tactic
import FLatticePaper.Plane.Induction.W1NonfreeHsq
import FLatticePaper.Plane.Induction.W1NonfreeHsqC
import FLatticePaper.Plane.Induction.SheetReflection
import FLatticePaper.Plane.Induction.TieDeficit
import FLatticePaper.Plane.Induction.W1HagreeNonfree
import FLatticePaper.Plane.Induction.StrongPriceValues

/-! # One step of an `A`-chain between tie sites (Q15, the reformulated chain step)

For a tie `b` (`Ψ b = 0`) and a tie `z` with the `A` edge `b → z`, the reflected `A` edge `K − b → K − z` is the `C` edge `b → z`
(`K` the centre). This step is obtained by cases on the minimum's colour at `b`:
* `M` white: the restricted tie agreement (`hagreeM`);
* `M` black, `C` black at `b`: the `C` policy keeps both inputs;
* `M` black, `C` white at `b`: the one-edge retention in the `C` orientation (`TieDeficit.one_edge_C`).

The `C` quota and the `C`-sheet colour come from the `A` quota of the parent (`lap_sheetA`) and the sheet exchange. -/

namespace FLatticePaper.TieChainStep

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet FLatticePaper.TieDeficit
open FLatticePaper.W1NonfreeHsq FLatticePaper.W1NonfreeHsqC FLatticePaper.W1Step

/-- The input offsets reflect through an even centre `K`: `in−(K − z) = K − in+ z` and `in+(K − z) = K − in− z`. -/
theorem incoming_reflect (K z : Site) (hK : EvenSite K) :
    incomingNeg (K - z) = K - incomingPos z ∧ incomingPos (K - z) = K - incomingNeg z := by
  have hpar : EvenSite (K - z) ↔ EvenSite z := by
    unfold EvenSite at hK ⊢
    simp only [Prod.fst_sub, Prod.snd_sub]
    omega
  constructor
  · unfold incomingNeg incomingPos
    by_cases hz : EvenSite z
    · rw [if_pos (hpar.2 hz), if_pos hz]
      ext <;> (simp only [Prod.fst_sub, Prod.snd_sub]; try ring)
    · rw [if_neg (fun h => hz (hpar.1 h)), if_neg hz]
      ext <;> (simp only [Prod.fst_sub, Prod.snd_sub]; try ring)
  · unfold incomingNeg incomingPos
    by_cases hz : EvenSite z
    · rw [if_pos (hpar.2 hz), if_pos hz]
      ext <;> (simp only [Prod.fst_sub, Prod.snd_sub]; try ring)
    · rw [if_neg (fun h => hz (hpar.1 h)), if_neg hz]
      ext <;> (simp only [Prod.fst_sub, Prod.snd_sub]; try ring)

/-- The `t`-grade is linear on the two inputs: `t(in−) + t(in+) = 2 t`. -/
theorem tGrade_inputs (frame : ChildFrame) (z : Site) :
    frame.tGrade (incomingNeg z) + frame.tGrade (incomingPos z) = 2 * frame.tGrade z := by
  unfold incomingNeg incomingPos ChildFrame.tGrade
  split_ifs <;> ring

/-- **The sheet-`C` colour is the `A` colour at the reflected point.** Under the sheet exchange and an even centre. -/
theorem lap_sheetC_eq (frame : ChildFrame) (Fp : Field) (hX : frame.SheetExchange Fp) (b : Site)
    (hK : EvenSite frame.centre) :
    laplacian (fun z => frame.sheetC Fp z) b = laplacian (fun z => frame.sheetA Fp z) (frame.centre - b) := by
  obtain ⟨hA, -⟩ := hX
  obtain ⟨h1, h2⟩ := incoming_reflect frame.centre b hK
  unfold laplacian
  simp only []
  rw [h1, h2, hA, hA, hA]
  have ht := tGrade_inputs frame b
  linarith


variable {word : Word} {seed : Site → Site → Prop}

/-- The `A`-sheet quota at a sheet point, from the parent quota and the parent neighbours. -/
theorem quota_sheetA (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (p : Site) :
    (laplacian (fun z => (frameAt word).sheetA (FqW word) z) p = -1 →
      sheetPolicyA P (frameAt word).sheetShift p (incomingNeg p) ∧
        sheetPolicyA P (frameAt word).sheetShift p (incomingPos p)) ∧
    (laplacian (fun z => (frameAt word).sheetA (FqW word) z) p = 0 →
      sheetPolicyA P (frameAt word).sheetShift p (incomingNeg p) ∨
        sheetPolicyA P (frameAt word).sheetShift p (incomingPos p)) := by
  have hz := lap_sheetA word p
  have hn := FLatticePaper.W1HagreeNonfree.zTurn_neighbors p (frameAt word).sheetShift
    (frameAt word).evenSite_sheetShift
  constructor
  · intro h
    rw [hz] at h
    obtain ⟨hq1, hq2⟩ := P.quota.1 _ h
    by_cases hp : EvenSite p
    · obtain ⟨e1, e2⟩ := hn.1 hp
      exact ⟨by
          show P.retained (zTurn (p - (frameAt word).sheetShift)) (zTurn (incomingNeg p - (frameAt word).sheetShift))
          rw [e1]; exact hq1,
        by
          show P.retained (zTurn (p - (frameAt word).sheetShift)) (zTurn (incomingPos p - (frameAt word).sheetShift))
          rw [e2]; exact hq2⟩
    · obtain ⟨e1, e2⟩ := hn.2 hp
      exact ⟨by
          show P.retained (zTurn (p - (frameAt word).sheetShift)) (zTurn (incomingNeg p - (frameAt word).sheetShift))
          rw [e1]; exact hq2,
        by
          show P.retained (zTurn (p - (frameAt word).sheetShift)) (zTurn (incomingPos p - (frameAt word).sheetShift))
          rw [e2]; exact hq1⟩
  · intro h
    rw [hz] at h
    have hq := P.quota.2 _ h
    by_cases hp : EvenSite p
    · obtain ⟨e1, e2⟩ := hn.1 hp
      rcases hq with hq | hq
      · exact Or.inl (by show P.retained _ _; rw [e1]; exact hq)
      · exact Or.inr (by show P.retained _ _; rw [e2]; exact hq)
    · obtain ⟨e1, e2⟩ := hn.2 hp
      rcases hq with hq | hq
      · exact Or.inr (by
          show P.retained (zTurn (p - (frameAt word).sheetShift)) (zTurn (incomingPos p - (frameAt word).sheetShift))
          rw [e2]; exact hq)
      · exact Or.inl (by
          show P.retained (zTurn (p - (frameAt word).sheetShift)) (zTurn (incomingNeg p - (frameAt word).sheetShift))
          rw [e1]; exact hq)

/-- The `C`-sheet quota at a tie-free site, from the `A` quota at the reflected point. -/
theorem quota_sheetC (hX : (frameAt word).SheetExchange (FqW word))
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (b : Site) (hK : EvenSite (frameAt word).centre) :
    (laplacian (fun z => (frameAt word).sheetC (FqW word) z) b = -1 →
      sheetPolicyC P (frameAt word).sheetShift (frameAt word).centre b (incomingNeg b) ∧
        sheetPolicyC P (frameAt word).sheetShift (frameAt word).centre b (incomingPos b)) ∧
    (laplacian (fun z => (frameAt word).sheetC (FqW word) z) b = 0 →
      sheetPolicyC P (frameAt word).sheetShift (frameAt word).centre b (incomingNeg b) ∨
        sheetPolicyC P (frameAt word).sheetShift (frameAt word).centre b (incomingPos b)) := by
  obtain ⟨h1, h2⟩ := incoming_reflect (frameAt word).centre b hK
  have hl := lap_sheetC_eq (frameAt word) (FqW word) hX b hK
  constructor
  · intro h
    obtain ⟨qa, qb⟩ := (quota_sheetA P ((frameAt word).centre - b)).1 (by rw [← hl]; exact h)
    exact ⟨by show sheetPolicyA P _ _ _; rw [← h2]; exact qb,
      by show sheetPolicyA P _ _ _; rw [← h1]; exact qa⟩
  · intro h
    rcases (quota_sheetA P ((frameAt word).centre - b)).2 (by rw [← hl]; exact h) with q | q
    · exact Or.inr (by show sheetPolicyA P _ _ _; rw [← h1]; exact q)
    · exact Or.inl (by show sheetPolicyA P _ _ _; rw [← h2]; exact q)

/-- The `A`-sheet and `C`-sheet colours are binary. -/
theorem binary_sheetA (hSE : StrongEstimates (conjWord word)) (p : Site) :
    laplacian (fun z => (frameAt word).sheetA (FqW word) z) p = -1 ∨
      laplacian (fun z => (frameAt word).sheetA (FqW word) z) p = 0 := by
  rw [lap_sheetA]
  exact hSE.packet.binary _

theorem binary_sheetC (hX : (frameAt word).SheetExchange (FqW word)) (hSE : StrongEstimates (conjWord word))
    (hK : EvenSite (frameAt word).centre) (b : Site) :
    laplacian (fun z => (frameAt word).sheetC (FqW word) z) b = -1 ∨
      laplacian (fun z => (frameAt word).sheetC (FqW word) z) b = 0 := by
  rw [lap_sheetC_eq (frameAt word) (FqW word) hX b hK]
  exact binary_sheetA hSE _

/-- **The black-minimum corner.** At a tie `b` whose minimum is black, the `C` policy keeps every input `z` of `b` that is a tie. -/
theorem keepC_of_black_tie (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hX : (frameAt word).SheetExchange (FqW word)) (hK : EvenSite (frameAt word).centre)
    {b z : Site} (hb : sheetPsi word b = 0) (hMb : laplacian (MW word) b = -1)
    (hz : sheetPsi word z = 0) (hzin : z = incomingNeg b ∨ z = incomingPos b) :
    sheetPolicyC P (frameAt word).sheetShift (frameAt word).centre b z := by
  refine one_edge_C (fun z => (frameAt word).sheetA (FqW word) z)
    (fun z => (frameAt word).sheetC (FqW word) z) (sheetPolicyC P (frameAt word).sheetShift
      (frameAt word).centre) b z (quota_sheetC hX P b hK).1 (quota_sheetC hX P b hK).2 ?_
    (binary_sheetC hX hSE hK b) ?_ ?_ hzin ?_
  · intro j hj
    have h1 := psi_mono hw hSE P hj
    have h2 := psi_reflect hw hSE b
    have h3 := psi_reflect hw hSE j
    show sheetPsi word j ≤ sheetPsi word b
    linarith
  · exact hMb
  · have hb' : (frameAt word).sheetC (FqW word) b - (frameAt word).sheetA (FqW word) b = 0 := hb
    show (frameAt word).sheetC (FqW word) b = (frameAt word).sheetA (FqW word) b
    linarith
  · show min ((frameAt word).sheetA (FqW word) z) ((frameAt word).sheetC (FqW word) z) = (frameAt word).sheetC (FqW word) z
    have hzt : (frameAt word).sheetC (FqW word) z = (frameAt word).sheetA (FqW word) z := by
      have : sheetPsi word z = 0 := hz
      unfold sheetPsi at this
      linarith
    rw [hzt, min_self]

/-- **One step of a tie chain.** For ties `b`, `z` with the `A` edge `b → z`, the `C` policy retains `b → z`, by the restricted
tie agreement at white minima and by the one-edge retention at black minima. -/
theorem tie_step_C (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hX : (frameAt word).SheetExchange (FqW word)) (hK : EvenSite (frameAt word).centre)
    (hEdgeS : ∀ c i, sheetPolicyA P (frameAt word).sheetShift c i → i = incomingNeg c ∨ i = incomingPos c)
    (hagreeM : ∀ x, sheetPsi word x = 0 → laplacian (MW word) x = 0 → ∀ y,
      sheetPolicyA P (frameAt word).sheetShift x y ↔
        sheetPolicyC P (frameAt word).sheetShift (frameAt word).centre x y)
    {b z : Site} (hb : sheetPsi word b = 0) (hz : sheetPsi word z = 0)
    (hA : sheetPolicyA P (frameAt word).sheetShift b z) :
    sheetPolicyC P (frameAt word).sheetShift (frameAt word).centre b z := by
  by_cases hMw : laplacian (MW word) b = 0
  · exact (hagreeM b hb hMw z).mp hA
  · have hMb : laplacian (MW word) b = -1 :=
      ((FLatticePaper.StrongPriceValues.sheetMin_binary_recurrent_of_strong hw hSE).1 b).resolve_right hMw
    refine one_edge_C (fun z => (frameAt word).sheetA (FqW word) z)
      (fun z => (frameAt word).sheetC (FqW word) z) (sheetPolicyC P (frameAt word).sheetShift
        (frameAt word).centre) b z (quota_sheetC hX P b hK).1 (quota_sheetC hX P b hK).2 ?_
      (binary_sheetC hX hSE hK b) ?_ ?_ (hEdgeS b z hA) ?_
    · intro j hj
      have h1 := psi_mono hw hSE P hj
      have h2 := psi_reflect hw hSE b
      have h3 := psi_reflect hw hSE j
      show sheetPsi word j ≤ sheetPsi word b
      linarith
    · exact hMb
    · have hb' : (frameAt word).sheetC (FqW word) b - (frameAt word).sheetA (FqW word) b = 0 := hb
      show (frameAt word).sheetC (FqW word) b = (frameAt word).sheetA (FqW word) b
      linarith
    · show min ((frameAt word).sheetA (FqW word) z) ((frameAt word).sheetC (FqW word) z) = (frameAt word).sheetC (FqW word) z
      have hzt : (frameAt word).sheetC (FqW word) z = (frameAt word).sheetA (FqW word) z := by
        have : sheetPsi word z = 0 := hz
        unfold sheetPsi at this
        linarith
      rw [hzt, min_self]


theorem zTurn_inj' {a b : Site} (h : zTurn a = zTurn b) : a = b := by
  unfold zTurn at h
  simp only [Prod.mk.injEq] at h
  ext <;> omega

/-- A retained sheet edge `c → i` of the `A` policy has `i` an input of `c`, from the parent edge property of the policy. -/
theorem sheetEdge_of_parent (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hPE : ∀ c i, P.retained c i → Edge i c) (c i : Site)
    (h : sheetPolicyA P (frameAt word).sheetShift c i) :
    i = incomingNeg c ∨ i = incomingPos c := by
  have hE : Edge (zTurn (i - (frameAt word).sheetShift)) (zTurn (c - (frameAt word).sheetShift)) := hPE _ _ h
  have hn := FLatticePaper.W1HagreeNonfree.zTurn_neighbors c (frameAt word).sheetShift
    (frameAt word).evenSite_sheetShift
  unfold Edge at hE
  by_cases hc : EvenSite c
  · obtain ⟨n1, n2⟩ := hn.1 hc
    rcases hE with e | e
    · rw [← n1] at e
      exact Or.inl (sub_left_inj.mp (zTurn_inj' e))
    · rw [← n2] at e
      exact Or.inr (sub_left_inj.mp (zTurn_inj' e))
  · obtain ⟨n1, n2⟩ := hn.2 hc
    rcases hE with e | e
    · rw [← n2] at e
      exact Or.inr (sub_left_inj.mp (zTurn_inj' e))
    · rw [← n1] at e
      exact Or.inl (sub_left_inj.mp (zTurn_inj' e))

end FLatticePaper.TieChainStep
