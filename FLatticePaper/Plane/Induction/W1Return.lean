import FLatticePaper.Plane.Induction.W1Pointers
import FLatticePaper.Plane.Induction.W1Forcing

/-! Task 62 (3), revised in task 63: the acyclicity of a relation that decreases a lexicographic measure, and the sign-directed arrows
of the sheets. The phase ranks and the forcing with the square-level phase conditions are in `W1Phase`.

The earlier `lex_of_phase` and `forcing_of_phase` took the phase properties for ALL pairs of sites. As stated they are inconsistent
(the tie property `RA c' < RA c` for two distinct ties is contradictory), so that forcing was vacuous. They are removed here and
restated for square returns only, in `W1Phase`. -/

namespace FLatticePaper.W1Return

open FLatticePaper FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.Induction FLatticePaper.W1
open FLatticePaper.W1Forcing FLatticePaper.W1Pointers

/-- The return relation of an assignment with the lexicographic decrease is acyclic (in particular no four-cycle). -/
theorem acyclic_of_lex (r : Site → Site → Prop) (μ : Site → ℕ × ℕ)
    (hr : ∀ c' c, r c' c → Prod.Lex (· < ·) (· < ·) (μ c') (μ c)) : ∀ c, ¬ Relation.TransGen r c c := by
  have hwfr : WellFounded r :=
    Subrelation.wf (fun {a b} h => hr a b h)
      (InvImage.wf μ (WellFounded.prod_lex wellFounded_lt wellFounded_lt))
  exact fun c hc => (hwfr.transGen).irrefl.irrefl c hc

/-- The sign-directed arrows of a child frame are inputs, and each is retained by the policy of its phase. -/
theorem sheetArrow_props (frame : ChildFrame) (Fp : Field) (Q : Site → Site → Prop) (hq : RetainQuota Fp Q)
    (hX : frame.SheetExchange Fp) (c : Site)
    (hbA : laplacian (fun z => frame.sheetA Fp z) c = -1 ∨ laplacian (fun z => frame.sheetA Fp z) c = 0)
    (hbC : laplacian (fun z => frame.sheetC Fp z) c = -1 ∨ laplacian (fun z => frame.sheetC Fp z) c = 0) :
    (sheetArrow frame Fp Q c = incomingNeg c ∨ sheetArrow frame Fp Q c = incomingPos c) ∧
    (0 ≤ psiDiff frame Fp c →
      (fun c i => Q (c - frame.sheetShift) (i - frame.sheetShift)) c (sheetArrow frame Fp Q c)) ∧
    (¬ 0 ≤ psiDiff frame Fp c →
      (fun c i => Q (frame.centre - c - frame.sheetShift) (frame.centre - i - frame.sheetShift)) c
        (sheetArrow frame Fp Q c)) := by
  have hqA := sheetA_retainQuota frame Fp Q hq
  have hqC := sheetC_retainQuota frame Fp Q hq hX
  have hret := arrowOut_retained (psiDiff frame Fp) (fun z => frame.sheetA Fp z) (fun z => frame.sheetC Fp z)
    (fun c i => Q (c - frame.sheetShift) (i - frame.sheetShift))
    (fun c i => Q (frame.centre - c - frame.sheetShift) (frame.centre - i - frame.sheetShift)) hqA hqC c hbA hbC
  exact ⟨arrowOut_input _ _ _ c, hret.1, hret.2⟩

/-- The common arrow at a tie. The A pointer of a tie is retained by the A policy (the pointer lemma). It is also the C arrow exactly
when the C policy retains it, which is the agreement of the two arrows at ties. The agreement is NOT a consequence of the
monotonicity of the matched policies (both inputs of a tie are ties, so `Ψ(i) ≥ 0` and `Ψ(i) ≤ 0` already hold); it is the named
hypothesis `hagree` (the archive's §5 rank descent along the tie band). Left as a hypothesis until the fixer answers Q15. -/
theorem tie_common_arrow (F : Field) (QA QC : Site → Site → Prop) (psi : Site → ℤ) (hqA : RetainQuota F QA)
    (hagree : ∀ c, psi c = 0 → laplacian F c = 0 → QC c (pointerOf QA c)) (c : Site)
    (hbin : laplacian F c = -1 ∨ laplacian F c = 0) (htie : psi c = 0) (hwhite : laplacian F c = 0) :
    QA c (pointerOf QA c) ∧ QC c (pointerOf QA c) :=
  ⟨pointerOf_retained F QA hqA c hbin, hagree c htie hwhite⟩

end FLatticePaper.W1Return
