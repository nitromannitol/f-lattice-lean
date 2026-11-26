import FLatticePaper.Plane.Induction.NativeQ34
import FLatticePaper.Plane.Induction.PlusAdjacent
import FLatticePaper.Plane.Induction.AdjacentMinus
import FLatticePaper.Plane.Induction.PlusBoundary
import FLatticePaper.Plane.Induction.RoundedLocal
import FLatticePaper.Plane.Induction.ForcedInputE
import FLatticePaper.Plane.Induction.NonfreeReflect
import FLatticePaper.Plane.Induction.ForcedCentre
import FLatticePaper.Plane.Induction.SecondarySeamEq
import FLatticePaper.Plane.Induction.W1NonfreeHsq
import FLatticePaper.Plane.Induction.W1NonfreeHsqC
import FLatticePaper.Plane.Induction.W1HagreeNonfree
import FLatticePaper.Plane.Induction.CollarTop
import FLatticePaper.Plane.Induction.SlipReflect
import FLatticePaper.Plane.Induction.FreePolicy

/-! # The sign +1 raw-slip permit at a strictly interior nonfree forced white

Let `c` be strictly interior, nonfree, with `laplacian c = 0`, and `o` a forced input (`ForcedEdge c o`), so `o = sheetOut P c`.
Cases, with `ρ x = centre − x` and `Ψ = sheetPsi`:
* the native chart `c + σ, o + σ ∈ E`: `NativeQ34.native_sign_plus_of_sheetOut`;
* the boundary dichotomy (`PlusBoundary.plus_chart_or_two`): both ends have slip `2`;
* the adjacent chart `c − uq, o − uq ∈ E` with `Ψ c ≥ 0`, `Ψ o ≥ 1`: `PlusAdjacent.plus_adjacent_strictA`;
* otherwise `Ψ c ≤ 0` and `Ψ o ≤ 0` (from `psi_mono` on the A-edge at `c`, or at the reflected root `ρc`), and the reflected edge
  `ρc → ρo` is a strict nonfree forced edge with `Ψ(ρc), Ψ(ρo) ≥ 0`, so its adjacent sign −1 chart
  (`AdjacentMinus.slip_minus_forced_adjacent_rise_at`) gives the permit, and `D₊ = D₋ ∘ ρ + 2` converts it back. -/

namespace FLatticePaper.ForcedPlusStrict

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses

/-- A site with no free span translate is nonfree in the sense of `Nonfree`. -/
theorem nonfree_of_not_freeClosure {word : Word} (x : Site)
    (hx : ¬ FLatticePaper.FreeClosure.freeClosure (frameAt word) x) :
    FLatticePaper.Induction.Nonfree (frameAt word) x :=
  fun s hs hm => hx ⟨s, hs, hm⟩

/-- The A-edge `x → y` from the sheet pointer at a nonnegative centre. -/
theorem edgeA_of_out {word : Word} (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed
      (frameAt word).eps)
    {x y : Site} (hΨ : 0 ≤ FLatticePaper.W1Step.sheetPsi word x)
    (hout : y = FLatticePaper.W1Step.sheetOut P (frameAt word).sheetShift (frameAt word).centre
      (FLatticePaper.W1Step.sheetPsi word) x) :
    sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift x y := by
  have hret := FLatticePaper.W1HagreeNonfree.sheetPolicyA_pointer_retained P.toOldPolicyWitness.toOldPolicyData
    hSE.packet.binary (frameAt word).sheetShift (frameAt word).evenSite_sheetShift x
  unfold FLatticePaper.W1Step.sheetOut at hout
  rw [if_pos hΨ] at hout
  rw [hout]
  exact hret

/-- **The sign +1 raw-slip permit at a strictly interior nonfree forced white.** -/
theorem plus_forced_strict {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hW : StrongCore word) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed
      (frameAt word).eps)
    (hsheet : ∀ c : Site, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (standardField word) c = 0 → ∀ o : Site,
        ForcedEdge (standardField word) (fun _ _ => False) c o →
        o = FLatticePaper.W1Step.sheetOut P (frameAt word).sheetShift (frameAt word).centre
          (FLatticePaper.W1Step.sheetPsi word) c)
    (hsat : FLatticePaper.Induction.HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    (hrise : FLatticePaper.W4Reduction.NoRiseForced P.toOldPolicyWitness.toOldPolicyData)
    {c o : Site}
    (hSI : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hc : c ∈ (frameAt word).closedPolygon) (hlap : laplacian (standardField word) c = 0)
    (hnf : ¬ FLatticePaper.FreeClosure.freeClosure (frameAt word) c)
    (hf : ForcedEdge (standardField word) (fun _ _ => False) c o) :
    (frameAt word).slip (standardField word) 1 o ≤ (frameAt word).slip (standardField word) 1 c := by
  have hPk : (frameAt word).Packet (standardField word) := hW.packet
  have hn3 : 3 ≤ (frameAt word).child.num := FLatticePaper.Induction.child_num_ge_three h
  have hnd : (frameAt word).child.num + 2 ≤ (frameAt word).child.den := by
    obtain ⟨-, -, h3, -, -⟩ := (frameAt word).child_facts
    omega
  have hout : o = FLatticePaper.W1Step.sheetOut P (frameAt word).sheetShift (frameAt word).centre
      (FLatticePaper.W1Step.sheetPsi word) c := hsheet c hSI hlap o hf
  have hEo : o ∈ (frameAt word).closedPolygon := FLatticePaper.ForcedInputE.forced_input_mem_E (frameAt word) hSI hf
  have hEdge : FLatticePaper.Edge o c := FLatticePaper.FreePolicy.forcedEdge_input hf
  have sl : ∀ x : Site, (frameAt word).slip (standardField word) 1 x =
      standardField word x - standardField word (x + (frameAt word).shortShift) := by
    intro x
    unfold ChildFrame.slip
    simp
  rcases FLatticePaper.PlusBoundary.plus_chart_or_two (frameAt word) hPk hn3 hnd hSI hc hEo hEdge with hN | hA | hEq
  · exact FLatticePaper.NativeQ34.native_sign_plus_of_sheetOut h hSE P hc hN.1 hEo hN.2 hout.symm
  · obtain ⟨hcA, hoA⟩ := hA
    by_cases hpos : 0 ≤ FLatticePaper.W1Step.sheetPsi word c ∧ 1 ≤ FLatticePaper.W1Step.sheetPsi word o
    · exact FLatticePaper.PlusAdjacent.plus_adjacent_strictA h hW hSE P.toOldPolicyWitness.toOldPolicyData hc hEo hcA hoA
        hpos.1 hpos.2 (edgeA_of_out hSE P hpos.1 hout)
    · -- reflected edge
      have hc' : (frameAt word).centre - c ∈ (frameAt word).closedPolygon :=
        (frameAt word).reflect_mem_closedPolygon hc
      have ho' : (frameAt word).centre - o ∈ (frameAt word).closedPolygon :=
        (frameAt word).reflect_mem_closedPolygon hEo
      have hSI' : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
          ((frameAt word).centre - c) :=
        (FLatticePaper.CollarTop.strict_reflect_centre (frameAt word) c).mpr hSI
      have hlap' : laplacian (standardField word) ((frameAt word).centre - c) = 0 := by
        rw [(frameAt word).laplacian_reflect hPk c]
        exact hlap
      have hnf' : ¬ FLatticePaper.FreeClosure.freeClosure (frameAt word) ((frameAt word).centre - c) :=
        FLatticePaper.NonfreeReflect.not_freeClosure_centre h c hnf
      have hf' : ForcedEdge (standardField word) (fun _ _ => False) ((frameAt word).centre - c)
          ((frameAt word).centre - o) :=
        FLatticePaper.ForcedCentre.forced_reflect_centre (frameAt word) hPk hf
      have hout' : (frameAt word).centre - o = FLatticePaper.W1Step.sheetOut P (frameAt word).sheetShift
          (frameAt word).centre (FLatticePaper.W1Step.sheetPsi word) ((frameAt word).centre - c) :=
        hsheet _ hSI' hlap' _ hf'
      have hΨc' : FLatticePaper.W1Step.sheetPsi word ((frameAt word).centre - c) =
          -FLatticePaper.W1Step.sheetPsi word c :=
        FLatticePaper.W1NonfreeHsqC.psi_reflect h hSE c
      have hΨo' : FLatticePaper.W1Step.sheetPsi word ((frameAt word).centre - o) =
          -FLatticePaper.W1Step.sheetPsi word o :=
        FLatticePaper.W1NonfreeHsqC.psi_reflect h hSE o
      have hab : FLatticePaper.W1Step.sheetPsi word c ≤ 0 ∧ FLatticePaper.W1Step.sheetPsi word o ≤ 0 := by
        by_cases ha : 0 ≤ FLatticePaper.W1Step.sheetPsi word c
        · have h1 := FLatticePaper.W1NonfreeHsq.psi_mono h hSE P.toOldPolicyWitness.toOldPolicyData
            (edgeA_of_out hSE P ha hout)
          exact ⟨by omega, by omega⟩
        · have hpos' : 0 ≤ FLatticePaper.W1Step.sheetPsi word ((frameAt word).centre - c) := by
            rw [hΨc']
            omega
          have h2 := FLatticePaper.W1NonfreeHsq.psi_mono h hSE P.toOldPolicyWitness.toOldPolicyData
            (edgeA_of_out hSE P hpos' hout')
          rw [hΨc', hΨo'] at h2
          exact ⟨by omega, by omega⟩
      have hcu' : (frameAt word).centre - c + (frameAt word).uq ∈ (frameAt word).closedPolygon := by
        have e : (frameAt word).centre - c + (frameAt word).uq =
            (frameAt word).centre - (c - (frameAt word).uq) := by abel
        rw [e]
        exact (frameAt word).reflect_mem_closedPolygon hcA
      have hiu' : (frameAt word).centre - o + (frameAt word).uq ∈ (frameAt word).closedPolygon := by
        have e : (frameAt word).centre - o + (frameAt word).uq =
            (frameAt word).centre - (o - (frameAt word).uq) := by abel
        rw [e]
        exact (frameAt word).reflect_mem_closedPolygon hoA
      have hΨc0 : 0 ≤ FLatticePaper.W1Step.sheetPsi word ((frameAt word).centre - c) := by
        rw [hΨc']
        omega
      have hΨi0 : 0 ≤ FLatticePaper.W1Step.sheetPsi word ((frameAt word).centre - o) := by
        rw [hΨo']
        omega
      have hr := FLatticePaper.RoundedLocal.rounded_forced_SI h hW hSE hsat hW1 hSI' hlap' hc' hf' ho'
      have hkey := FLatticePaper.AdjacentMinus.slip_minus_forced_adjacent_rise_at h hW hSE hPk P hrise hr hSI' hc' ho'
        hcu' hiu' hΨc0 hΨi0 (FLatticePaper.FreePolicy.forcedEdge_input hf') hf' hlap'
        (nonfree_of_not_freeClosure _ hnf') hout'.symm
      have e1 := FLatticePaper.SecondarySeamEq.slipPlus_centre_eq (frameAt word) hPk ((frameAt word).centre - o)
      have e2 := FLatticePaper.SecondarySeamEq.slipPlus_centre_eq (frameAt word) hPk ((frameAt word).centre - c)
      rw [sub_sub_cancel] at e1 e2
      linarith
  · rw [sl, sl]
    linarith [hEq.1, hEq.2]

end FLatticePaper.ForcedPlusStrict
