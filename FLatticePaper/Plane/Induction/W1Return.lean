import FLatticePaper.Plane.Induction.W1Pointers
import FLatticePaper.Plane.Induction.W1Forcing

/-! Task 62 (3): the phase ranks of §5–§6 and the acyclicity of the assigned return graph.

With `Ψ` the sheet difference, the leading component of a site is `0` on ties (`Ψ = 0`) and `1` on strict sites; the second component
is the rank of the active phase (`RA` on ties and on `Ψ ≥ 0`, `RC` on `Ψ < 0`). A unit square of a tie has only tie corners; a unit
square of a strict site has tie corners or corners of its own sign of `Ψ`. Numerically (every proper word of length ≤ 3) both kinds of
admissible squares exist at every white, and the phase-restricted least fixed point forces every white. The return relation is then
lexicographically decreasing:

* tie to tie: the A rank `RA` drops (`hRT`, the zero-pitch rank along the tie band);
* strict to tie: the leading component drops (no condition);
* strict to strict of the same sign: the phase rank drops (`hRS`), and no cross-phase return occurs (`hS`);
* tie to strict: excluded (`hT`).

The archive's order with the tie indicator as the *drop* (tie to strict decreasing) is not the one the numerics support: a strict
white at word `23`, `(2,1)`, has a single unit square in `E°`, which contains a tie white, so a strict-to-tie return occurs. -/

namespace FLatticePaper.W1Return

open FLatticePaper FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.Induction FLatticePaper.W1
open FLatticePaper.W1Forcing FLatticePaper.W1Pointers
open FLatticePaper.W1Forcing FLatticePaper.W1Pointers

/-- The leading component: `0` on ties, `1` on strict sites. -/
def phaseLeading (psi : Site → ℤ) (c : Site) : ℕ := if psi c = 0 then 0 else 1

/-- The phase rank: `RA` on ties and on `Ψ ≥ 0`, `RC` on `Ψ < 0`. -/
def phaseRank (psi : Site → ℤ) (RA RC : Site → ℕ) (c : Site) : ℕ := if 0 ≤ psi c then RA c else RC c

/-- The lexicographic measure of a site. -/
def phaseMeasure (psi : Site → ℤ) (RA RC : Site → ℕ) (c : Site) : ℕ × ℕ :=
  (phaseLeading psi c, phaseRank psi RA RC c)

/-- The return decreases the measure lexicographically in the four admissible cases. -/
theorem lex_of_phase (psi : Site → ℤ) (RA RC : Site → ℕ)
    (hT : ∀ c c', psi c = 0 → psi c' ≠ 0 → False)
    (hS : ∀ c c', psi c ≠ 0 → psi c' ≠ 0 → (0 ≤ psi c ↔ 0 ≤ psi c'))
    (hRT : ∀ c c', psi c = 0 → psi c' = 0 → RA c' < RA c)
    (hRS : ∀ c c', psi c ≠ 0 → psi c' ≠ 0 → (0 ≤ psi c ↔ 0 ≤ psi c') →
      phaseRank psi RA RC c' < phaseRank psi RA RC c)
    (c c' : Site) :
    Prod.Lex (· < ·) (· < ·) (phaseMeasure psi RA RC c') (phaseMeasure psi RA RC c) := by
  rw [Prod.lex_def]
  unfold phaseMeasure phaseLeading
  by_cases hc : psi c = 0
  · have hc' : psi c' = 0 := by
      by_contra h
      exact hT c c' hc h
    right
    refine ⟨by simp [hc, hc'], ?_⟩
    unfold phaseRank
    have h1 : 0 ≤ psi c := by rw [hc]
    have h2 : 0 ≤ psi c' := by rw [hc']
    simp only [h1, h2, if_true]
    exact hRT c c' hc hc'
  · by_cases hc' : psi c' = 0
    · left
      simp [hc, hc']
    · right
      refine ⟨by simp [hc, hc'], ?_⟩
      exact hRS c c' hc hc' (hS c c' hc hc')

/-- The return relation of an assignment with the lexicographic decrease is acyclic (in particular no four-cycle). -/
theorem acyclic_of_lex (r : Site → Site → Prop) (μ : Site → ℕ × ℕ)
    (hr : ∀ c' c, r c' c → Prod.Lex (· < ·) (· < ·) (μ c') (μ c)) : ∀ c, ¬ Relation.TransGen r c c := by
  have hwfr : WellFounded r :=
    Subrelation.wf (fun {a b} h => hr a b h)
      (InvImage.wf μ (WellFounded.prod_lex wellFounded_lt wellFounded_lt))
  exact fun c hc => (hwfr.transGen).irrefl.irrefl c hc

/-- The forcing assembly with the phase measure: the pointers `out` and the square data give the returns, and the four properties
of §5–§6 give the lexicographic decrease. -/
theorem forcing_of_phase (n d : ℤ) (F : Field) (out : Site → Site) (psi : Site → ℤ) (RA RC : Site → ℕ)
    (hT : ∀ c c', psi c = 0 → psi c' ≠ 0 → False)
    (hS : ∀ c c', psi c ≠ 0 → psi c' ≠ 0 → (0 ≤ psi c ↔ 0 ≤ psi c'))
    (hRT : ∀ c c', psi c = 0 → psi c' = 0 → RA c' < RA c)
    (hRS : ∀ c c', psi c ≠ 0 → psi c' ≠ 0 → (0 ≤ psi c ↔ 0 ≤ psi c') →
      phaseRank psi RA RC c' < phaseRank psi RA RC c)
    (hout : ∀ c, StrictInterior n d c → laplacian F c = 0 → (out c = incomingNeg c ∨ out c = incomingPos c))
    (hsq : ∀ c, StrictInterior n d c → laplacian F c = 0 → ∃ a b : ℤ,
      c ∈ squareCorners a b ∧ (∀ c' ∈ squareCorners a b, StrictInterior n d c') ∧ out c ∉ squareCorners a b ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = -1 ∨
        (laplacian F c' = 0 ∧ out c' ∈ squareCorners a b ∧ (out c' = incomingNeg c' ∨ out c' = incomingPos c')))) :
    ∀ c, StrictInterior n d c → laplacian F c = 0 →
      ForcedEdgeIn F (StrictInterior n d) (fun _ _ => False) c (out c) :=
  forcing_of_lex n d F out (phaseMeasure psi RA RC) hout
    (fun c hR hw => by
      obtain ⟨a, b, h1, h2, h3, h4⟩ := hsq c hR hw
      exact ⟨a, b, h1, h2, h3, h4, fun c' _ _ _ => lex_of_phase psi RA RC hT hS hRT hRS c c'⟩)

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
hypothesis `hagree` (the archive's §5 rank descent along the tie band). -/
theorem tie_common_arrow (F : Field) (QA QC : Site → Site → Prop) (psi : Site → ℤ) (hqA : RetainQuota F QA)
    (hagree : ∀ c, psi c = 0 → QC c (pointerOf QA c)) (c : Site) (hbin : laplacian F c = -1 ∨ laplacian F c = 0)
    (htie : psi c = 0) :
    QA c (pointerOf QA c) ∧ QC c (pointerOf QA c) :=
  ⟨pointerOf_retained F QA hqA c hbin, hagree c htie⟩


end FLatticePaper.W1Return
