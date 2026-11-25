import FLatticePaper.Plane.Induction.TraceStep
import FLatticePaper.Plane.Induction.ChainEnd
import FLatticePaper.Plane.Induction.ConjBase
import FLatticePaper.Plane.Induction.GamesPolicy
import FLatticePaper.Plane.Induction.PsiArc
import FLatticePaper.Plane.Induction.PureRow
import FLatticePaper.Plane.Induction.PureTrace
import FLatticePaper.Plane.Induction.TwosField
import FLatticePaper.Plane.Induction.ThreesGames
import FLatticePaper.Plane.Induction.EPolicyFinal

/-! Task w3, B: the trace at the two-power words `2^(k+1)`.

The trace step (`traceAt_step_row`) does not assume the word is not a two-power. The conjugate of `2^(k+1)` is `3^k`, whose estimates
(`pure_threes_inputs`), trace (`PureTrace.traceAt_threes`), minus row (`PureRow.rowThrees_of_conj`) and games (`gamesWithRank_threes`)
are proved. So the trace at `2^(k+1)` is the trace step at the two-power word. -/

namespace FLatticePaper.TwosTrace

open Farey FLatticePaper FLatticePaper.Induction

theorem traceAt_twos (k : ℕ) : TraceFromPsi.TraceAt (List.replicate (k + 1) Digit.two) := by
  have hc : conjWord (List.replicate (k + 1) Digit.two) = List.replicate k Digit.three :=
    conjWord_replicate_two k
  have hX : ∀ x ∈ conjWord (List.replicate (k + 1) Digit.two), x = Digit.three := by
    rw [hc]
    intro x hx
    exact (List.eq_of_mem_replicate hx)
  have h : ∃ x ∈ List.replicate (k + 1) Digit.two, x ≠ Digit.three := ⟨Digit.two, by simp, by decide⟩
  have hSE : StrongEstimates (conjWord (List.replicate (k + 1) Digit.two)) := by
    rw [hc]
    exact StrongEstimates.of_base_pure k (EPolicy.pure_threes_inputs.1 k) (EPolicy.pure_threes_inputs.2 k)
  have hTW : TraceFromPsi.TraceAt (conjWord (List.replicate (k + 1) Digit.two)) := by
    rw [hc]
    exact PureTrace.traceAt_threes k
  obtain ⟨base, hbase⟩ := PsiArc.conj_base_exists (List.replicate (k + 1) Digit.two)
  obtain ⟨H, N, hN2, hNd, hHmem, hHabs, hcover⟩ := ConjBase.freeH_enum_N (frameAt (List.replicate (k + 1) Digit.two))
  have hN : (N : ℤ) ≤ (frameAt (List.replicate (k + 1) Digit.two)).child.den := le_of_eq hNd
  have hrowM := PureRow.rowThrees_of_conj (conjWord (List.replicate (k + 1) Digit.two)) hX base hbase
  obtain ⟨P, R, cU, cV, hPres, -, hNon, -, -, -, -, -⟩ :=
    policy_of_gamesWithRank_prescribed (w := conjWord (List.replicate (k + 1) Digit.two))
      (by rw [hc]; exact gamesWithRank_threes k)
  have hEnd := fun (hη : (frameAt (List.replicate (k + 1) Digit.two)).eps = 1) =>
    ChainEnd.hEnd_of_chain_row h hSE hTW hη base hbase hrowM H N hHmem hHabs P hPres hNon
  exact TraceStep.traceAt_step_row h hSE hTW base hbase hrowM H N hHmem hHabs hcover hN2 hN hEnd

end FLatticePaper.TwosTrace
