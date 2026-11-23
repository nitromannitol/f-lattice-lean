import FLatticePaper.Plane.Induction.W1Forcing
import FLatticePaper.Plane.Induction.W1Witness
import FLatticePaper.Plane.Induction.MatchedPolicy

/-! Task 63–64 (orientation corrected in task 65): the phase ranks of §5–§6 transported from the conjugate's rank, the square-level phase
conditions, and the private squares transported by the sheet map.

The earlier canonical policy carries an integer rank that strictly decreases along its retained edges (the archive's F2F3 rank). The A
sheet carries `c ↦ rank (zTurn (c − lv))`, the C sheet the rank of the reflected point `centre − c`.

Orientation (archive ALL_WHITE_THREE_STEP_RETURNS §A, AUDIT §1, ZERO_PITCH_RANK §2): the rejected input `u` of a forced white `c` is a
square corner with the three-edge directed return `u → v → w → c`: every corner keeps the next one, the last keeps the root. So every
corner `c'` of the square reaches `c` along retained edges, and the ranks satisfy `R c < R c'`: the corners lie ABOVE the root. The
forcing therefore runs in DECREASING rank: a corner is forced before its root. The forcing measure is `lexV` on the negated ranks.

A return of a strict white `c` through its unit square is a white corner `c'` with the phase condition `PhaseOK` (a tie returns only to
ties; a strict site returns to ties and to sites of its own sign of `Ψ`) and a chain of retained edges of the phase policy from `c'` to
`c`. -/

namespace FLatticePaper.W1Phase

open Farey FLatticePaper FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.Induction FLatticePaper.W1
open FLatticePaper.W1Forcing
open FLatticePaper.W1Witness

/-- The earlier canonical policy with its rank and its private squares: the archive's F2F3 rank, an integer function strictly decreasing
along the retained edges. -/
structure OldPolicyRanked (frame : ChildFrame) (G : Field) (seed : Site → Site → Prop)
    extends OldPolicyWitness frame G seed where
  /-- The rank of the policy. -/
  rank : Site → ℤ
  /-- The rank strictly decreases along every retained edge. -/
  rank_decr : ∀ c i, retained c i → rank i < rank c
  /-- The F2F3 rank has the increments `(−1, η)` on the child's generators, for `η = ±1` (the rank of the archive; `rank_decr` is its strict
  decrease). The increments `(−1, 2η)` of the same policy follow (`rankIncr_two_of_ranked`, `W1Inherited`). -/
  rankIncr : ∀ η : ℤ, (η = 1 ∨ η = -1) →
    RankWithIncrements retained frame.child.modifiedDeck.kernel frame.child.modifiedDeck.transverse (-1) η

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
    (h : sheetPolicyA P.toOldPolicyWitness.toOldPolicyData lv c i) : sheetRankA P lv i < sheetRankA P lv c :=
  P.rank_decr (zTurn (c - lv)) (zTurn (i - lv)) h

/-- The C-sheet rank decreases along the transported C policy (the reflection of the A policy). -/
theorem sheetRankC_decr {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : OldPolicyRanked frame G seed) (lv centre : Site) {c i : Site}
    (h : sheetPolicyC P.toOldPolicyWitness.toOldPolicyData lv centre c i) :
    sheetRankC P lv centre i < sheetRankC P lv centre c :=
  sheetRankA_decr P lv (c := centre - c) (i := centre - i) h

/-- A rank that decreases along the edges of a relation decreases along its transitive closure. -/
theorem transGen_rank_lt {pol : Site → Site → Prop} {f : Site → ℤ} (hf : ∀ c i, pol c i → f i < f c) {c c' : Site}
    (h : Relation.TransGen pol c c') : f c' < f c := by
  induction h with
  | single h => exact hf _ _ h
  | tail _ h ih => exact (hf _ _ h).trans ih

/-- A rank that increases along the edges (`f c < f i` on each edge `c → i`) is smaller at the start of a chain than at its end:
a chain from `c` to `c'` gives `f c < f c'`. -/
theorem transGen_rank_lt' {pol : Site → Site → Prop} {f : Site → ℤ} (hf : ∀ c i, pol c i → f c < f i) {c c' : Site}
    (h : Relation.TransGen pol c c') : f c < f c' := by
  induction h with
  | single h => exact hf _ _ h
  | tail _ h ih => exact ih.trans (hf _ _ h)

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

/-- The phase condition of a return `c'` of `c` (a corner of the square of `c`): a tie returns only to ties, and a strict site
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

/-- The one-step return decreases the lexicographic measure, in the three admissible cases. The corner `c'` reaches the root `c` by a
chain of the phase policy, and the ranks `NA`, `NC` increase along that policy, so the corner is below the root. -/
theorem lexV_of_return (psi : Site → ℤ) (PA PC : Site → Site → Prop) (NA NC : Site → ℤ)
    (hPA : ∀ c i, PA c i → NA c < NA i) (hPC : ∀ c i, PC c i → NC c < NC i)
    {c c' : Site} (hph : PhaseOK psi c c') (hch : Relation.TransGen (phasePolicy psi PA PC c) c' c) :
    lexV psi NA NC c' c := by
  unfold lexV
  by_cases h0 : psi c = 0
  · have hc' : psi c' = 0 := hph.1 h0
    have hle : 0 ≤ psi c := by omega
    have hle' : 0 ≤ psi c' := by omega
    have hA : Relation.TransGen PA c' c := by
      unfold phasePolicy at hch
      rw [if_pos hle] at hch
      exact hch
    have hdec := transGen_rank_lt' hPA hA
    have e1 : leadV psi c' = leadV psi c := by simp [leadV, h0, hc']
    have e2 : rankV psi NA NC c' = NA c' := by simp [rankV, hle']
    have e3 : rankV psi NA NC c = NA c := by simp [rankV, hle]
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
        have hA : Relation.TransGen PA c' c := by
          unfold phasePolicy at hch
          rw [if_pos hs] at hch
          exact hch
        have hdec := transGen_rank_lt' hPA hA
        have e1 : leadV psi c' = leadV psi c := by simp [leadV, h0, h0']
        have e2 : rankV psi NA NC c' = NA c' := by simp [rankV, hs']
        have e3 : rankV psi NA NC c = NA c := by simp [rankV, hs]
        right
        refine ⟨e1, ?_⟩
        rw [e2, e3]
        exact hdec
      · have hs' : ¬ 0 ≤ psi c' := fun h => hs (hsame.mpr h)
        have hC : Relation.TransGen PC c' c := by
          unfold phasePolicy at hch
          rw [if_neg hs] at hch
          exact hch
        have hdec := transGen_rank_lt' hPC hC
        have e1 : leadV psi c' = leadV psi c := by simp [leadV, h0, h0']
        have e2 : rankV psi NA NC c' = NC c' := by simp [rankV, hs']
        have e3 : rankV psi NA NC c = NC c := by simp [rankV, hs]
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

/-- The return relation of a phase on the strict interior: `c'` lies in the strict interior and is lexicographically below `c`, for the
forcing order in which the ranks are negated (corners above the root are forced first). -/
def returnRel (n d : ℤ) (psi : Site → ℤ) (NA NC : Site → ℤ) (a b : Site) : Prop :=
  StrictInterior n d a ∧ StrictInterior n d b ∧ lexV psi NA NC a b

/-- **The forcing with the phase ranks, corners above the root.** At every strict white `c`, a unit square `Q ∋ c` in the strict interior
with the rejected pointer outside `Q`; every other corner `c'` of `Q` points into `Q`, and reaches `c` along the phase policy with the
phase condition `PhaseOK` (the three-edge return of the square). The ranks `RA`, `RC` decrease along the phase policies, so the corners
are forced first in the decreasing order of the ranks. -/
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
        PhaseOK psi c c' ∧ Relation.TransGen (phasePolicy psi PA PC c) c' c)) :
    ∀ c, StrictInterior n d c → laplacian F c = 0 →
      ForcedEdgeIn F (StrictInterior n d) (fun _ _ => False) c (out c) := by
  have hPA' : ∀ c i, PA c i → (fun z => -RA z) c < (fun z => -RA z) i := fun c i h => by
    show -RA c < -RA i
    have := hPA c i h
    omega
  have hPC' : ∀ c i, PC c i → (fun z => -RC z) c < (fun z => -RC z) i := fun c i h => by
    show -RC c < -RC i
    have := hPC c i h
    omega
  refine forcing_of_finite_acyclic n d F out (returnRel n d psi (fun z => -RA z) (fun z => -RC z)) hfin
    (fun x y h => by unfold returnRel at h; exact ⟨h.1, h.2.1⟩)
    (not_transGen_lexV (fun a b h => by unfold returnRel at h; exact h.2.2)) hout ?_
  intro c hR hw
  obtain ⟨a, b, h1, h2, h3, h4, h5⟩ := hsq c hR hw
  refine ⟨a, b, h1, h2, h3, h4, fun c' hc' hne hw' => ?_⟩
  obtain ⟨hph, hch⟩ := h5 c' hc' hne hw'
  unfold returnRel
  exact ⟨h2 c' hc', hR, lexV_of_return psi PA PC (fun z => -RA z) (fun z => -RC z) hPA' hPC' hph hch⟩

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
          Relation.TransGen (phasePolicy psi (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData lv)
            (sheetPolicyC P.toOldPolicyWitness.toOldPolicyData lv centre) c) c' c)) :
    ∀ c, StrictInterior n d c → laplacian F c = 0 →
      ForcedEdgeIn F (StrictInterior n d) (fun _ _ => False) c (out c) :=
  forcing_of_phase_policy n d F out psi (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData lv)
    (sheetPolicyC P.toOldPolicyWitness.toOldPolicyData lv centre) (sheetRankA P lv) (sheetRankC P lv centre)
    (fun _ _ h => sheetRankA_decr P lv h) (fun _ _ h => sheetRankC_decr P lv centre h) hfin hout hsq

/-! The transport of the private squares by the sheet map `c ↦ zTurn (c − lv)`. -/

/-- The inverse of the parent transform `zTurn`. -/
def zTurnInv (q : Site) : Site := (q.2 + 1, -q.1)

theorem zTurn_zTurnInv (q : Site) : zTurn (zTurnInv q) = q := by
  ext <;> simp [zTurn, zTurnInv]

theorem zTurnInv_zTurn (x : Site) : zTurnInv (zTurn x) = x := by
  ext <;> simp [zTurn, zTurnInv]

/-- The child site over a parent site `q` under the sheet transform of shift `lv`. -/
def sheetImg (lv q : Site) : Site := zTurnInv q + lv

theorem zTurn_sheetImg_sub (lv q : Site) : zTurn (sheetImg lv q - lv) = q := by
  unfold sheetImg
  rw [add_sub_cancel_right]
  exact zTurn_zTurnInv q

theorem sheetImg_zTurn (lv c : Site) : sheetImg lv (zTurn (c - lv)) = c := by
  unfold sheetImg
  rw [zTurnInv_zTurn, sub_add_cancel]

/-- A chain of retained lattice edges of the parent from the corner `q` to the root `p` transports to an A sheet chain from the child
site over `q` to the child site over `p`. -/
theorem transGen_sheet_img {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} (P : OldPolicyRanked frame G seed)
    (lv : Site) {p q : Site} (h : Relation.TransGen (fun x y => P.retained x y ∧ Edge y x) q p) :
    Relation.TransGen (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData lv) (sheetImg lv q) (sheetImg lv p) := by
  induction h with
  | single h =>
    apply Relation.TransGen.single
    simp only [sheetPolicyA, parentPolicy]
    rw [zTurn_sheetImg_sub, zTurn_sheetImg_sub]
    exact h.1
  | tail _ h ih =>
    apply Relation.TransGen.tail ih
    simp only [sheetPolicyA, parentPolicy]
    rw [zTurn_sheetImg_sub, zTurn_sheetImg_sub]
    exact h.1

/-- The image of a parent square is a child square: the four corners go to the four corners of `squareCorners (b+1+lv₁) (−a−1+lv₂)`. -/
theorem sheetImg_mem (lv : Site) (a b : ℤ) {q : Site} (hq : q ∈ squareCorners a b) :
    sheetImg lv q ∈ squareCorners (b + 1 + lv.1) (-a - 1 + lv.2) := by
  obtain ⟨x, y⟩ := q
  simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at hq ⊢
  simp only [sheetImg, zTurnInv, Prod.fst_add, Prod.snd_add]
  omega

/-- Every corner of the child square is the image of a corner of the parent square. -/
theorem sheet_corner_of_mem (lv : Site) (a b : ℤ) {c' : Site}
    (hc' : c' ∈ squareCorners (b + 1 + lv.1) (-a - 1 + lv.2)) :
    ∃ q ∈ squareCorners a b, sheetImg lv q = c' := by
  obtain ⟨x, y⟩ := c'
  simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hc'
  rcases hc' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨(a + 1, b), by simp [squareCorners], ?_⟩
    simp only [sheetImg, zTurnInv, Prod.ext_iff, Prod.fst_add, Prod.snd_add]
    omega
  · refine ⟨(a + 1, b + 1), by simp [squareCorners], ?_⟩
    simp only [sheetImg, zTurnInv, Prod.ext_iff, Prod.fst_add, Prod.snd_add]
    omega
  · refine ⟨(a, b), by simp [squareCorners], ?_⟩
    simp only [sheetImg, zTurnInv, Prod.ext_iff, Prod.fst_add, Prod.snd_add]
    omega
  · refine ⟨(a, b + 1), by simp [squareCorners], ?_⟩
    simp only [sheetImg, zTurnInv, Prod.ext_iff, Prod.fst_add, Prod.snd_add]
    omega

/-- **The private square transported.** A parent square `squareCorners a b` through its root `p`, whose other corners reach `p` by retained
edges, transports to the child square `squareCorners (b+1+lv₁) (−a−1+lv₂)` through the child root `c` over `p`: the child root lies in it,
and every other corner reaches `c` along the A sheet policy. -/
theorem sheet_private_square {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} (P : OldPolicyRanked frame G seed)
    (lv : Site) (a b : ℤ) {p c : Site} (hp : p ∈ squareCorners a b) (hc : zTurn (c - lv) = p)
    (hchain : ∀ q ∈ squareCorners a b, q ≠ p → Relation.TransGen (fun x y => P.retained x y ∧ Edge y x) q p) :
    c ∈ squareCorners (b + 1 + lv.1) (-a - 1 + lv.2) ∧
      ∀ c' ∈ squareCorners (b + 1 + lv.1) (-a - 1 + lv.2), c' ≠ c →
        Relation.TransGen (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData lv) c' c := by
  have hcp : c = sheetImg lv p := by
    rw [← hc, sheetImg_zTurn]
  subst hcp
  refine ⟨sheetImg_mem lv a b hp, fun c' hc' hne => ?_⟩
  obtain ⟨q, hq, rfl⟩ := sheet_corner_of_mem lv a b hc'
  have hqp : q ≠ p := fun h => hne (by rw [h])
  exact transGen_sheet_img P lv (hchain q hq hqp)

/-- **The private witness transported.** At a child white `c` over a forced parent white `p` (the parent's witness square is private,
`OldPolicyWitness.privateSquare`), the transported child square contains `c`, and every other corner reaches `c` along the A sheet
policy: the chain required by the phase return on the transported square. -/
theorem sheet_private_of_forced {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} (P : OldPolicyRanked frame G seed)
    (lv : Site) {p c i : Site} (hc : zTurn (c - lv) = p) (hF : ForcedEdge G seed p i) (hns : ¬ seed p i)
    (hw : laplacian G p = 0) :
    ∃ a b : ℤ, p ∈ squareCorners a b ∧ c ∈ squareCorners (b + 1 + lv.1) (-a - 1 + lv.2) ∧
      ∀ c' ∈ squareCorners (b + 1 + lv.1) (-a - 1 + lv.2), c' ≠ c →
        Relation.TransGen (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData lv) c' c := by
  obtain ⟨a, b, hp, hchain⟩ := P.privateSquare p i hF hns hw
  obtain ⟨hcmem, hch⟩ := sheet_private_square P lv a b hp hc hchain
  exact ⟨a, b, hp, hcmem, hch⟩

/-! The core squares of §3 of the archive, in the parent's coordinates, with the three-edge returns of AUDIT §3 and ALL_WHITE §D. The
roots: `H0 = (1,0)` (grades `(N, Lp)`), `V0 = (0,0)` (`tp = 0`), `Vlast = (1,−1)` (the period `I`, `sp = 2N`). Each collar lemma takes the
parent's core claim as a hypothesis (the parent's three-edge chain from each corner to the root along the parent policy); it is the
archive's claim, not a field. `Hlast` is not identified in Lean. Note: the archive gives H0's square with a sign dependence (ALL_WHITE §D
η+: `squareCorners 0 0`; AUDIT §3 both signs: `squareCorners 1 0`), and V0's η+ square as `squareCorners 0 (−1)`, not `squareCorners (−1) (−1)`. -/

/-- The bottom H0 core square (archive AUDIT §3, both signs): the parent square `squareCorners 1 0` of the rejected input `(1,1)`. -/
theorem collar_H0_upperRight {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} (P : OldPolicyRanked frame G seed)
    (lv : Site) {c : Site} (hc : zTurn (c - lv) = (1, 0))
    (hchain : ∀ q ∈ squareCorners 1 0, q ≠ (1, 0) →
      Relation.TransGen (fun x y => P.retained x y ∧ Edge y x) q (1, 0)) :
    c ∈ squareCorners (0 + 1 + lv.1) (-1 - 1 + lv.2) ∧
      ∀ c' ∈ squareCorners (0 + 1 + lv.1) (-1 - 1 + lv.2), c' ≠ c →
        Relation.TransGen (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData lv) c' c :=
  sheet_private_square P lv 1 0 (by simp [squareCorners]) hc hchain

/-- The H0 η+ core square of ALL_WHITE §D: the parent square `squareCorners 0 0`, whose rejected input `(1,1)` returns through `(0,1)`,
`(0,0)`. -/
theorem collar_H0_upperLeft {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} (P : OldPolicyRanked frame G seed)
    (lv : Site) {c : Site} (hc : zTurn (c - lv) = (1, 0))
    (hchain : ∀ q ∈ squareCorners 0 0, q ≠ (1, 0) →
      Relation.TransGen (fun x y => P.retained x y ∧ Edge y x) q (1, 0)) :
    c ∈ squareCorners (0 + 1 + lv.1) (-0 - 1 + lv.2) ∧
      ∀ c' ∈ squareCorners (0 + 1 + lv.1) (-0 - 1 + lv.2), c' ≠ c →
        Relation.TransGen (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData lv) c' c :=
  sheet_private_square P lv 0 0 (by simp [squareCorners]) hc hchain

/-- The bottom V0 η− core square (AUDIT §3): the parent square `squareCorners (−1) 0`, rejected input `(−1,0)`. -/
theorem collar_V0_upperLeft {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} (P : OldPolicyRanked frame G seed)
    (lv : Site) {c : Site} (hc : zTurn (c - lv) = (0, 0))
    (hchain : ∀ q ∈ squareCorners (-1) 0, q ≠ (0, 0) →
      Relation.TransGen (fun x y => P.retained x y ∧ Edge y x) q (0, 0)) :
    c ∈ squareCorners (0 + 1 + lv.1) (-(-1) - 1 + lv.2) ∧
      ∀ c' ∈ squareCorners (0 + 1 + lv.1) (-(-1) - 1 + lv.2), c' ≠ c →
        Relation.TransGen (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData lv) c' c :=
  sheet_private_square P lv (-1) 0 (by simp [squareCorners]) hc hchain

/-- The bottom V0 η+ core square (AUDIT §3, ALL_WHITE §D): the parent square `squareCorners 0 (−1)`, rejected input `(1,0)`. -/
theorem collar_V0_etaPlus {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} (P : OldPolicyRanked frame G seed)
    (lv : Site) {c : Site} (hc : zTurn (c - lv) = (0, 0))
    (hchain : ∀ q ∈ squareCorners 0 (-1), q ≠ (0, 0) →
      Relation.TransGen (fun x y => P.retained x y ∧ Edge y x) q (0, 0)) :
    c ∈ squareCorners (-1 + 1 + lv.1) (-0 - 1 + lv.2) ∧
      ∀ c' ∈ squareCorners (-1 + 1 + lv.1) (-0 - 1 + lv.2), c' ≠ c →
        Relation.TransGen (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData lv) c' c :=
  sheet_private_square P lv 0 (-1) (by simp [squareCorners]) hc hchain

/-- The W1 left Vlast core square (AUDIT §3, both signs): the parent square `squareCorners 1 (−1)`, rejected input `(2,−1)` relative to the
root `(1,−1)` of the child square. -/
theorem collar_Vlast_upperRight {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} (P : OldPolicyRanked frame G seed)
    (lv : Site) {c : Site} (hc : zTurn (c - lv) = (1, -1))
    (hchain : ∀ q ∈ squareCorners 1 (-1), q ≠ (1, -1) →
      Relation.TransGen (fun x y => P.retained x y ∧ Edge y x) q (1, -1)) :
    c ∈ squareCorners (-1 + 1 + lv.1) (-1 - 1 + lv.2) ∧
      ∀ c' ∈ squareCorners (-1 + 1 + lv.1) (-1 - 1 + lv.2), c' ≠ c →
        Relation.TransGen (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData lv) c' c :=
  sheet_private_square P lv 1 (-1) (by simp [squareCorners]) hc hchain

end FLatticePaper.W1Phase
