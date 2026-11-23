import FLatticePaper.Plane.Induction.W1Forcing
import FLatticePaper.Plane.Induction.W1Witness
import FLatticePaper.Plane.Induction.MatchedPolicy

/-! Task 63: the phase ranks of §5–§6 transported from the conjugate's rank, and the square-level phase conditions.

The earlier canonical policy carries an integer rank that strictly decreases along its retained edges: the archive's F2F3 rank
(`StrongResidual`, `RankWithIncrements`). The A sheet carries the rank `c ↦ rank (zTurn (c − lv))`, and the C sheet the rank of the
reflected point `centre − c`. Both decrease along the transported policies (`sheetRankA_decr`, `sheetRankC_decr`).

A return of a strict white `c` through its unit square is a white corner `c'` with the phase condition `PhaseOK` (a tie returns only to
ties; a strict site returns to ties and to sites of its own sign of `Ψ`) and a chain of retained edges of the phase policy from `c` to
`c'`: the three-edge return of the square lies on the matched policy (a named square-level hypothesis, see `forcing_of_phase_policy`).
Along such a chain the phase rank decreases, so the lexicographic measure `(leading, rank)` decreases, and the forcing follows from
acyclicity on the finite strict interior (`forcing_of_finite_acyclic`).

The unit bound excludes adjacent cross-phase pairs (`no_adjacent_cross`). A diagonal cross-phase pair (`Ψ = +1`, `Ψ = −1` on a
diagonal of a unit square) forces both other corners to be ties; numerically this occurs (38 squares of words of length ≤ 3), so the
square-level condition `PhaseOK` is a property of the chosen squares, not of all squares. -/

namespace FLatticePaper.W1Phase

open Farey FLatticePaper FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.Induction FLatticePaper.W1
open FLatticePaper.W1Forcing

/-- The earlier canonical policy with its rank: an integer function strictly decreasing along the retained edges (the archive's F2F3
rank of the conjugate's policy). -/
structure OldPolicyRanked (frame : ChildFrame) (G : Field) (seed : Site → Site → Prop)
    extends OldPolicyData frame G seed where
  /-- The rank of the policy. -/
  rank : Site → ℤ
  /-- The rank strictly decreases along every retained edge. -/
  rank_decr : ∀ c i, retained c i → rank i < rank c

/-- The A-sheet rank: the rank of the policy at the parent point `zTurn (c − lv)`. -/
def sheetRankA {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} (P : OldPolicyRanked frame G seed)
    (lv c : Site) : ℤ :=
  P.rank (zTurn (c - lv))

/-- The C-sheet rank: the A-sheet rank of the reflected point `centre − c`. -/
def sheetRankC {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} (P : OldPolicyRanked frame G seed)
    (lv centre c : Site) : ℤ :=
  sheetRankA P lv (centre - c)

/-- The A-sheet rank decreases along the transported A policy. -/
theorem sheetRankA_decr {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : OldPolicyRanked frame G seed) (lv : Site) {c i : Site}
    (h : sheetPolicyA P.toOldPolicyData lv c i) : sheetRankA P lv i < sheetRankA P lv c :=
  P.rank_decr (zTurn (c - lv)) (zTurn (i - lv)) h

/-- The C-sheet rank decreases along the transported C policy (the reflection of the A policy). -/
theorem sheetRankC_decr {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : OldPolicyRanked frame G seed) (lv centre : Site) {c i : Site}
    (h : sheetPolicyC P.toOldPolicyData lv centre c i) :
    sheetRankC P lv centre i < sheetRankC P lv centre c :=
  sheetRankA_decr P lv (c := centre - c) (i := centre - i) h

/-- A rank that decreases along the edges of a relation decreases along its transitive closure. -/
theorem transGen_rank_lt {pol : Site → Site → Prop} {f : Site → ℤ} (hf : ∀ c i, pol c i → f i < f c) {c c' : Site}
    (h : Relation.TransGen pol c c') : f c' < f c := by
  induction h with
  | single h => exact hf _ _ h
  | tail _ h ih => exact (hf _ _ h).trans ih

/-- The phase policy of a site: the A policy on `Ψ ≥ 0` and the C policy on `Ψ < 0`. -/
def phasePolicy (psi : Site → ℤ) (PA PC : Site → Site → Prop) (c : Site) : Site → Site → Prop :=
  if 0 ≤ psi c then PA else PC

/-- The phase rank: `RA` on `Ψ ≥ 0` (ties included), `RC` on `Ψ < 0`. -/
def rankV (psi : Site → ℤ) (RA RC : Site → ℤ) (c : Site) : ℤ :=
  if 0 ≤ psi c then RA c else RC c

/-- The leading component: `0` on ties, `1` on strict sites. -/
def leadV (psi : Site → ℤ) (c : Site) : ℤ :=
  if psi c = 0 then 0 else 1

/-- The lexicographic order on (leading component, phase rank): `c'` is below `c`. -/
def lexV (psi : Site → ℤ) (RA RC : Site → ℤ) (c' c : Site) : Prop :=
  leadV psi c' < leadV psi c ∨ (leadV psi c' = leadV psi c ∧ rankV psi RA RC c' < rankV psi RA RC c)

/-- The phase condition of a return `c'` of `c` (a white corner of the square of `c`): a tie returns only to ties, and a strict site
returns to ties and to sites of its own sign of `Ψ`. -/
def PhaseOK (psi : Site → ℤ) (c c' : Site) : Prop :=
  (psi c = 0 → psi c' = 0) ∧ (psi c ≠ 0 → psi c' ≠ 0 → (0 ≤ psi c ↔ 0 ≤ psi c'))

theorem lexV_trans {psi : Site → ℤ} {RA RC : Site → ℤ} {a b c : Site} (h1 : lexV psi RA RC a b)
    (h2 : lexV psi RA RC b c) : lexV psi RA RC a c := by
  unfold lexV at *
  omega

theorem lexV_irrefl {psi : Site → ℤ} {RA RC : Site → ℤ} (c : Site) : ¬ lexV psi RA RC c c := by
  unfold lexV
  omega

/-- The unit bound excludes an adjacent cross-phase pair: on an edge `Ψ` changes by at most one. -/
theorem no_adjacent_cross {psi : Site → ℤ}
    (hunit : ∀ c i, Edge i c → -1 ≤ psi i - psi c ∧ psi i - psi c ≤ 1) {c i : Site} (hE : Edge i c)
    (h1 : psi c ≠ 0) (h2 : psi i ≠ 0) : (0 ≤ psi c ↔ 0 ≤ psi i) := by
  obtain ⟨u1, u2⟩ := hunit c i hE
  constructor <;> intro h <;> omega

/-- The one-step return decreases the lexicographic measure, in the three admissible cases. -/
theorem lexV_of_return (psi : Site → ℤ) (PA PC : Site → Site → Prop) (RA RC : Site → ℤ)
    (hPA : ∀ c i, PA c i → RA i < RA c) (hPC : ∀ c i, PC c i → RC i < RC c)
    {c c' : Site} (hph : PhaseOK psi c c') (hch : Relation.TransGen (phasePolicy psi PA PC c) c c') :
    lexV psi RA RC c' c := by
  unfold lexV
  by_cases h0 : psi c = 0
  · have hc' : psi c' = 0 := hph.1 h0
    have hle : 0 ≤ psi c := by omega
    have hle' : 0 ≤ psi c' := by omega
    have hA : Relation.TransGen PA c c' := by
      unfold phasePolicy at hch
      rw [if_pos hle] at hch
      exact hch
    have hdec := transGen_rank_lt hPA hA
    have e1 : leadV psi c' = leadV psi c := by simp [leadV, h0, hc']
    have e2 : rankV psi RA RC c' = RA c' := by simp [rankV, hle']
    have e3 : rankV psi RA RC c = RA c := by simp [rankV, hle]
    right
    refine ⟨e1, ?_⟩
    rw [e2, e3]
    exact hdec
  · by_cases h0' : psi c' = 0
    · left
      simp [leadV, h0, h0']
    · have hsame := hph.2 h0 h0'
      by_cases hs : 0 ≤ psi c
      · have hs' : 0 ≤ psi c' := hsame.mp hs
        have hA : Relation.TransGen PA c c' := by
          unfold phasePolicy at hch
          rw [if_pos hs] at hch
          exact hch
        have hdec := transGen_rank_lt hPA hA
        have e1 : leadV psi c' = leadV psi c := by simp [leadV, h0, h0']
        have e2 : rankV psi RA RC c' = RA c' := by simp [rankV, hs']
        have e3 : rankV psi RA RC c = RA c := by simp [rankV, hs]
        right
        refine ⟨e1, ?_⟩
        rw [e2, e3]
        exact hdec
      · have hs' : ¬ 0 ≤ psi c' := fun h => hs (hsame.mpr h)
        have hC : Relation.TransGen PC c c' := by
          unfold phasePolicy at hch
          rw [if_neg hs] at hch
          exact hch
        have hdec := transGen_rank_lt hPC hC
        have e1 : leadV psi c' = leadV psi c := by simp [leadV, h0, h0']
        have e2 : rankV psi RA RC c' = RC c' := by simp [rankV, hs']
        have e3 : rankV psi RA RC c = RC c := by simp [rankV, hs]
        right
        refine ⟨e1, ?_⟩
        rw [e2, e3]
        exact hdec

/-- A relation whose one-step edges decrease `lexV` has no cycle. -/
theorem lexV_transGen {psi : Site → ℤ} {RA RC : Site → ℤ} {r : Site → Site → Prop}
    (hr : ∀ a b, r a b → lexV psi RA RC a b) {a b : Site} (h : Relation.TransGen r a b) :
    lexV psi RA RC a b := by
  induction h with
  | single h => exact hr _ _ h
  | tail _ h ih => exact lexV_trans ih (hr _ _ h)

theorem not_transGen_lexV {psi : Site → ℤ} {RA RC : Site → ℤ} {r : Site → Site → Prop}
    (hr : ∀ a b, r a b → lexV psi RA RC a b) (c : Site) : ¬ Relation.TransGen r c c :=
  fun h => lexV_irrefl c (lexV_transGen hr h)

/-- The return relation of a phase on the strict interior: `c'` lies in the strict interior and is lexicographically below `c`. -/
def returnRel (n d : ℤ) (psi : Site → ℤ) (RA RC : Site → ℤ) (a b : Site) : Prop :=
  StrictInterior n d a ∧ StrictInterior n d b ∧ lexV psi RA RC a b

/-- **The forcing with the phase ranks.** At every strict white `c`, a unit square `Q ∋ c` in the strict interior with the rejected
pointer outside `Q`; every other white corner `c'` of `Q` points into `Q` and is returned to `c` with the phase condition `PhaseOK` and
a chain of retained edges of the phase policy from `c` (the three-edge return of the square). The ranks `RA`, `RC` decrease along the
phase policies. The conclusion is the forcing of every strict white at its pointer. -/
theorem forcing_of_phase_policy (n d : ℤ) (F : Field) (out : Site → Site) (psi : Site → ℤ)
    (PA PC : Site → Site → Prop) (RA RC : Site → ℤ)
    (hPA : ∀ c i, PA c i → RA i < RA c) (hPC : ∀ c i, PC c i → RC i < RC c)
    (hfin : {c : Site | StrictInterior n d c}.Finite)
    (hout : ∀ c, StrictInterior n d c → laplacian F c = 0 → (out c = incomingNeg c ∨ out c = incomingPos c))
    (hsq : ∀ c, StrictInterior n d c → laplacian F c = 0 → ∃ a b : ℤ,
      c ∈ squareCorners a b ∧ (∀ c' ∈ squareCorners a b, StrictInterior n d c') ∧ out c ∉ squareCorners a b ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = -1 ∨
        (laplacian F c' = 0 ∧ out c' ∈ squareCorners a b ∧ (out c' = incomingNeg c' ∨ out c' = incomingPos c'))) ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = 0 →
        PhaseOK psi c c' ∧ Relation.TransGen (phasePolicy psi PA PC c) c c')) :
    ∀ c, StrictInterior n d c → laplacian F c = 0 →
      ForcedEdgeIn F (StrictInterior n d) (fun _ _ => False) c (out c) := by
  refine forcing_of_finite_acyclic n d F out (returnRel n d psi RA RC) hfin
    (fun x y h => by unfold returnRel at h; exact ⟨h.1, h.2.1⟩)
    (not_transGen_lexV (fun a b h => by unfold returnRel at h; exact h.2.2)) hout ?_
  intro c hR hw
  obtain ⟨a, b, h1, h2, h3, h4, h5⟩ := hsq c hR hw
  refine ⟨a, b, h1, h2, h3, h4, fun c' hc' hne hw' => ?_⟩
  obtain ⟨hph, hch⟩ := h5 c' hc' hne hw'
  unfold returnRel
  exact ⟨h2 c' hc', hR, lexV_of_return psi PA PC RA RC hPA hPC hph hch⟩

/-- **The forcing with the transported sheet ranks.** The A and C phase policies are the sheet policies of the earlier policy, and their
ranks are `sheetRankA` and `sheetRankC`, which decrease along them. -/
theorem forcing_of_sheet {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : OldPolicyRanked frame G seed) (lv centre : Site) (n d : ℤ) (F : Field) (out : Site → Site) (psi : Site → ℤ)
    (hfin : {c : Site | StrictInterior n d c}.Finite)
    (hout : ∀ c, StrictInterior n d c → laplacian F c = 0 → (out c = incomingNeg c ∨ out c = incomingPos c))
    (hsq : ∀ c, StrictInterior n d c → laplacian F c = 0 → ∃ a b : ℤ,
      c ∈ squareCorners a b ∧ (∀ c' ∈ squareCorners a b, StrictInterior n d c') ∧ out c ∉ squareCorners a b ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = -1 ∨
        (laplacian F c' = 0 ∧ out c' ∈ squareCorners a b ∧ (out c' = incomingNeg c' ∨ out c' = incomingPos c'))) ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = 0 →
        PhaseOK psi c c' ∧
          Relation.TransGen (phasePolicy psi (sheetPolicyA P.toOldPolicyData lv)
            (sheetPolicyC P.toOldPolicyData lv centre) c) c c')) :
    ∀ c, StrictInterior n d c → laplacian F c = 0 →
      ForcedEdgeIn F (StrictInterior n d) (fun _ _ => False) c (out c) :=
  forcing_of_phase_policy n d F out psi (sheetPolicyA P.toOldPolicyData lv)
    (sheetPolicyC P.toOldPolicyData lv centre) (sheetRankA P lv) (sheetRankC P lv centre)
    (fun _ _ h => sheetRankA_decr P lv h) (fun _ _ h => sheetRankC_decr P lv centre h) hfin hout hsq

end FLatticePaper.W1Phase
