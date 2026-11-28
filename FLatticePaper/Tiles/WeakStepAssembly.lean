import FLatticePaper.Tiles.WeakStepPaper
import FLatticePaper.Tiles.ClosedPathTriOdd
import FLatticePaper.Tiles.ClosedPathTriEven
import FLatticePaper.Tiles.MixedFromCells
import FLatticePaper.Tiles.TileTranslationStd

/-! # The weak step of the joint induction for the paper's data

`weakStep_paper` proves `JointInduction.WeakStepInput D` for joint data whose weak data are the paper's
(`WeakStepPaper.paperS`). At a base word the weak odometers are those of the base cases (`BaseWeakInput`). At any other word
the registers `u1`, `u2` are both present (`regsAt_nonbase`), and condition (C) holds for the placed tile odometers of the
registers:
* for the odd child, by `closedPathOdd_final`;
* for the even child, by `closedPathEven_final`.

The inputs (C) needs from the parents come from the family below `w`:
* the boundary strings come from the tile part of the slice;
* `SigmaZero` comes from the corner values (`stdCorners_odd`, `stdCorners_even`) and the zero slope of the normalisation;
* (c) of the doubled parent comes from (a) of the tile lemma (`TileTranslation`).

The glue of the existence step (`glue_kept_pieces`, with claim (d) from `mixedOdd_all`, `mixedEven_all`) then gives the weak
nodes (`oddNode_of_kept`, `evenNode_of_kept`).

The domains of the tile odometers of the registers are the domain clause of `TilePart`. The named inputs are listed as
definitions below; each is a statement of the text not yet proved here. -/

namespace FLatticePaper.Tiles.WeakStepAssembly

open FLatticePaper.Farey
open FLatticePaper.Construction (texV1Odd texV1Even texV2)
open FLatticePaper.Tiles
open FLatticePaper.Tiles.SurgicalWeak
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointInduction
open FLatticePaper.Tiles.WeakStepPaper
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.Standard (IsBase stateAt oddTile evenTile)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)
open FLatticePaper.Tiles.ChildGlue (keptSet dblOdd dblEven oddP oddQ evenP evenQ tOddSet tEvenSet pieceSet pieceFlag
  MarksAgreeOdd MarksAgreeEven DoubledAgreeOdd DoubledAgreeEven)
open FLatticePaper.Tiles.ClosedPathAssembly (placedOdd placedEven MixedCompatOdd MixedCompatEven)

/-! ### The registers of a word that is not a base word -/

theorem regsAt_fst_none (w : Word) : (regsAt w).1 = none ↔ ∀ d ∈ w, d = Digit.three := by
  induction w using List.reverseRecOn with
  | nil => simp [regsAt, regRun]
  | append_singleton v d ih =>
    rw [regsAt_snoc]
    cases d <;> simp [regStep, ih, or_imp, forall_and]

theorem regsAt_snd_none (w : Word) : (regsAt w).2 = none ↔ ∀ d ∈ w, d = Digit.two := by
  induction w using List.reverseRecOn with
  | nil => simp [regsAt, regRun]
  | append_singleton v d ih =>
    rw [regsAt_snoc]
    cases d <;> simp [regStep, ih, or_imp, forall_and]

/-- A word that is not a base word has both registers. -/
theorem regsAt_nonbase (w : Word) (hw : ¬ IsBase w) : ∃ u1 u2 : Word, regsAt w = (some u1, some u2) := by
  have h1 : (regsAt w).1 ≠ none := fun h => hw (Or.inr (Or.inl ((regsAt_fst_none w).1 h)))
  have h2 : (regsAt w).2 ≠ none := fun h => hw (Or.inr (Or.inr ((regsAt_snd_none w).1 h)))
  obtain ⟨u1, hu1⟩ := Option.ne_none_iff_exists'.mp h1
  obtain ⟨u2, hu2⟩ := Option.ne_none_iff_exists'.mp h2
  exact ⟨u1, u2, Prod.ext hu1 hu2⟩

/-- The parents of a word are the children of its registers. -/
theorem regsAt_parents (w : Word) :
    (∀ u, (regsAt w).1 = some u → (parentsAt w).odd = fracOdd u) ∧
    (∀ u, (regsAt w).2 = some u → (parentsAt w).even = fracEven u) := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨fun u h => by simp [regsAt, regRun] at h, fun u h => by simp [regsAt, regRun] at h⟩
  | append_singleton v d ih =>
    rw [regsAt_snoc, parentsAt_append_singleton]
    cases d
    · refine ⟨fun u h => ?_, fun u h => ?_⟩ <;> simp only [regStep, Option.some.injEq] at h <;> subst h <;> rfl
    · refine ⟨fun u h => ?_, fun u h => ih.2 u h⟩
      simp only [regStep, Option.some.injEq] at h; subst h; rfl
    · refine ⟨fun u h => ih.1 u h, fun u h => ?_⟩
      simp only [regStep, Option.some.injEq] at h; subst h; rfl

/-! ### The facts of the family the step reads -/

/-- The tile odometers of the slice are defined on the boundary tiles of the weak data (the domain clause of `TilePart`). -/
theorem slice_domains (D : JointData) (f : Word → JSlice) (u : Word) (h : IsJointSlice D f u) :
    (f u).tOdd.dom = D.S.bdry (some u) true ∧ (f u).tEven.dom = D.S.bdry (some u) false := by
  obtain ⟨-, -, ⟨-, -, -, -, -, -, -, -, h1, h2⟩, -⟩ := h
  exact ⟨h1, h2⟩

theorem slice_respects (D : JointData) (f : Word → JSlice) (u : Word) (h : IsJointSlice D f u) :
    RespectsAnchored (f u).tOdd.dom (hWordOf u false) (vWordOf u false) (f u).tOdd.val ∧
      RespectsAnchored (f u).tEven.dom (hWordOf u true) (vWordOf u true) (f u).tEven.val := by
  obtain ⟨-, -, ⟨-, -, -, -, h1, h2, -⟩, -⟩ := h
  exact ⟨h1, h2⟩

/-- (c) of a tile odometer for its first lattice vector, from (a) of the tile lemma. -/
theorem translation_v1 (o : PartialOdometer) (v1 v2 a2 : Site) (h : TileTranslation o v1 v2 a2) :
    ∃ k : ℤ, ∀ x, x ∈ o.dom → x + v1 ∈ o.dom → o.val (x + v1) - o.val x = k := by
  obtain ⟨α, β, -, h1, -⟩ := h
  refine ⟨dotS α v1, fun x hx hxv => ?_⟩
  have := h1 x hx hxv
  simp only [normed, dotS, Prod.fst_add, Prod.snd_add] at this ⊢
  linear_combination this

/-- (c) of a tile odometer for its second lattice vector, with its affine factor, from (a) of the tile lemma. -/
theorem translation_v2 (o : PartialOdometer) (v1 v2 a2 : Site) (h : TileTranslation o v1 v2 a2) :
    ∃ k : ℤ, ∀ x, x ∈ o.dom → x + v2 ∈ o.dom → o.val (x + v2) - o.val x - dotS a2 x = k := by
  obtain ⟨α, β, -, -, h2⟩ := h
  refine ⟨dotS α v2 - h0 v2, fun x hx hxv => ?_⟩
  have := h2 x hx hxv
  simp only [normed, dotS, Prod.fst_add, Prod.snd_add] at this ⊢
  linear_combination this

/-- The normalisation on the first tile determines the slope and the constant. -/
theorem normal_unique (o : PartialOdometer) (α α' : Site) (β β' : ℤ) (h : FirstTileNormal o α β)
    (h' : FirstTileNormal o α' β') : α = α' ∧ β = β' := by
  have m0 : ((0 : ℤ), (0 : ℤ)) ∈ tileShape ZTile.one := by simp [tileShape]
  have m1 : ((1 : ℤ), (0 : ℤ)) ∈ tileShape ZTile.one := by simp [tileShape]
  have m2 : ((0 : ℤ), (1 : ℤ)) ∈ tileShape ZTile.one := by simp [tileShape]
  have e0 := (h _ m0).2.trans (h' _ m0).2.symm
  have e1 := (h _ m1).2.trans (h' _ m1).2.symm
  have e2 := (h _ m2).2.trans (h' _ m2).2.symm
  simp only [normed, dotS, mul_zero, mul_one, add_zero, zero_add] at e0 e1 e2
  refine ⟨Prod.ext ?_ ?_, ?_⟩ <;> linarith

/-- `SigmaZero` of a parent normalised with zero slope, from its corner values. -/
theorem sigma_of_corners (o : PartialOdometer) (X Y e α : Site) (β β' : ℤ) (hz : FirstTileNormal o 0 β')
    (hN : FirstTileNormal o α β) (hV : TileTranslation.StdCornerValues o α β X Y e) :
    ClosedPathTriOdd.SigmaZero o.val X := by
  obtain ⟨hα, -⟩ := normal_unique o α 0 β β' hN hz
  subst hα
  obtain ⟨⟨-, h00⟩, ⟨-, h10⟩, ⟨-, hXm⟩, ⟨-, hX⟩, -⟩ := hV
  simp only [normed, dotS, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero, sub_zero] at h00 h10 hXm hX
  constructor <;> simp only [ClosedPathSum.e₁, ClosedPathSum.e₂] <;> linarith

/-! ### The named inputs -/

/-- (A), the base cases (`prop:base_cases`): at a base word, weak odometers on the standard tiles with the base condition, the
boundary strings and (c). -/
def BaseWeakInput : Prop :=
  ∀ w : Word, IsBase w → ∃ wo we : PartialOdometer, wo.dom = oddTile w ∧ we.dom = evenTile w ∧ PaperBaseCond w wo we ∧
    RespectsAnchored wo.dom (hWordOf w false) (vWordOf w false) wo.val ∧
    RespectsAnchored we.dom (hWordOf w true) (vWordOf w true) we.val ∧ WeakProps w wo we

/-- The tile odometers of the family are normalised on their first tile with zero slope. -/
def TileSlopeZero (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (n : ℕ), GoodBelow D f n → ∀ u : Word, u.length < n →
    (∃ β, FirstTileNormal (f u).tOdd 0 β) ∧ (∃ β, FirstTileNormal (f u).tEven 0 β)

/-- Local compatibility of the mixed copies on the marks (input of `closedPathOdd_final` and `closedPathEven_final`). -/
def MixedCompatInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w u1 u2 : Word), GoodBelow D f w.length → ¬ IsBase w → regsAt w = (some u1, some u2) →
    MixedCompatOdd w u1 u2 (placedOdd w (f u1).tOdd.val (f u2).tEven.val 0) ∧
      MixedCompatEven w u1 u2 (placedEven w (f u1).tOdd.val (f u2).tEven.val 0)

/-- The glued odometers of the two children: the placed subodometers plus the constants of condition (C) on the kept parts. The
hypotheses shared by `GlueRespectsInput` and `GlueLatticeInput`. -/
def GluedChildren (f : Word → JSlice) (w u1 u2 : Word) (κo κe : ℕ → ℤ) (go ge : Site → ℤ) : Prop :=
  MarksAgreeOdd w u1 u2 (fun i z => placedOdd w (f u1).tOdd.val (f u2).tEven.val 0 i z + κo i) ∧
    DoubledAgreeOdd w u1 u2 (dblOdd w) (fun i z => placedOdd w (f u1).tOdd.val (f u2).tEven.val 0 i z + κo i) ∧
    (∀ i < (oddP w).length + (oddQ w).length,
      ∀ z ∈ keptSet (pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2)) (pieceFlag (oddP w)) (dblOdd w) i,
        go z = placedOdd w (f u1).tOdd.val (f u2).tEven.val 0 i z + κo i) ∧
    MarksAgreeEven w u1 u2 (fun i z => placedEven w (f u1).tOdd.val (f u2).tEven.val 0 i z + κe i) ∧
    DoubledAgreeEven w u1 u2 dblEven (fun i z => placedEven w (f u1).tOdd.val (f u2).tEven.val 0 i z + κe i) ∧
    (∀ i < (evenP w).length + (evenQ w).length,
      ∀ z ∈ keptSet (pieceSet (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2)) (pieceFlag (evenP w)) dblEven i,
        ge z = placedEven w (f u1).tOdd.val (f u2).tEven.val 0 i z + κe i)

/-- (a) of `lemma:weak_standard_odometer_properties` for the glued children (end of Step 1 of its proof), at the children that are
not corrected: they respect the boundary words of the children, when the tile odometers of the shorter words are normalised with
zero slope (without it an affine change of one register keeps (C) but breaks the junction slopes of the child's strings). At a
corrected child the glue on the kept parts fails (a) at `w = 2 3^k` (odd child). -/
def GlueRespectsInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w u1 u2 : Word), GoodBelow D f w.length → ¬ IsBase w → regsAt w = (some u1, some u2) →
  (∀ u : Word, u.length < w.length → (∃ β, FirstTileNormal (f u).tOdd 0 β) ∧ (∃ β, FirstTileNormal (f u).tEven 0 β)) →
  ∀ (κo κe : ℕ → ℤ) (go ge : Site → ℤ), GluedChildren f w u1 u2 κo κe go ge →
    (¬ CorrectedAfterThree w → RespectsAnchored (oddTile w) (hWordOf w false) (vWordOf w false) go) ∧
      (¬ CorrectedAfterTwo w → RespectsAnchored (evenTile w) (hWordOf w true) (vWordOf w true) ge)

/-- (c) of `lemma:weak_standard_odometer_properties` for the glued children (Step 2 of its proof): each is compatible with its
lattice adjacent translates. -/
def GlueLatticeInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w u1 u2 : Word), GoodBelow D f w.length → ¬ IsBase w → regsAt w = (some u1, some u2) →
  ∀ (κo κe : ℕ → ℤ) (go ge : Site → ℤ), GluedChildren f w u1 u2 κo κe go ge →
    WeakProps w ⟨oddTile w, go⟩ ⟨evenTile w, ge⟩

/-! ### The weak step -/

/-- **The weak step of the joint induction for the paper's data**: `WeakStepInput D` when the weak data of `D` are `paperS`,
from the named inputs `BaseWeakInput`, `TileSlopeZero`, `MixedCompatInput`, `GlueRespectsInput` and `GlueLatticeInput`. -/
theorem weakStep_paper (D : JointData) (hS : D.S = paperS) (hB : BaseWeakInput) (hsl : TileSlopeZero D)
    (hmc : MixedCompatInput D) (hgr : GlueRespectsInput D) (hgl : GlueLatticeInput D) :
    WeakStepInput D := by
  intro f w hgood
  by_cases hw : IsBase w
  · obtain ⟨wo, we, hdo, hde, hbc, hro, hre, hwp⟩ := hB w hw
    refine ⟨wo, we, ⟨?_, ?_, fun _ => ?_, fun h => absurd hw h, fun _ => hro, fun _ => hre⟩, hwp⟩
    · rw [hS]; exact hdo
    · rw [hS]; exact hde
    · rw [hS]; exact hbc
  obtain ⟨u1, u2, hreg⟩ := regsAt_nonbase w hw
  have hl1 : u1.length < w.length := regsAt_lt w u1 (Or.inl (by rw [hreg]))
  have hl2 : u2.length < w.length := regsAt_lt w u2 (Or.inr (by rw [hreg]))
  have hb1 : below f w u1 = f u1 := by simp only [below, if_pos hl1]
  have hb2 : below f w u2 = f u2 := by simp only [below, if_pos hl2]
  have hp : (parentsAt w).odd = fracOdd u1 := (regsAt_parents w).1 u1 (by rw [hreg])
  have hq : (parentsAt w).even = fracEven u2 := (regsAt_parents w).2 u2 (by rw [hreg])
  obtain ⟨hS1, hJ1⟩ := hgood u1 hl1
  obtain ⟨hS2, hJ2⟩ := hgood u2 hl2
  have hdO : (f u1).tOdd.dom = oddTile u1 := by rw [(slice_domains D f u1 hS1).1, hS]; rfl
  have hdE : (f u2).tEven.dom = evenTile u2 := by rw [(slice_domains D f u2 hS2).2, hS]; rfl
  have hRP := (slice_respects D f u1 hS1).1
  have hRQ := (slice_respects D f u2 hS2).2
  obtain ⟨-, ⟨hTO, -⟩, -⟩ := hJ1
  obtain ⟨-, ⟨-, hTE, -⟩, -⟩ := hJ2
  obtain ⟨⟨βo, hzo⟩, -⟩ := hsl f w.length hgood u1 hl1
  obtain ⟨-, ⟨βe, hze⟩⟩ := hsl f w.length hgood u2 hl2
  obtain ⟨αo, β1, hNo, hVo⟩ := TileTranslationStd.stdCorners_odd u1 (f u1).tOdd hRP
  obtain ⟨αe, β2, hNe, hVe⟩ := TileTranslationStd.stdCorners_even u2 (f u2).tEven hRQ
  have hsP : ClosedPathTriOdd.SigmaZero (f u1).tOdd.val (texV1Odd (parentsAt w).odd) := by
    rw [hp]; exact sigma_of_corners _ _ _ _ _ _ _ hzo hNo hVo
  have hsQ : ClosedPathTriOdd.SigmaZero (f u2).tEven.val (texV1Even (parentsAt w).even) := by
    rw [hq]; exact sigma_of_corners _ _ _ _ _ _ _ hze hNe hVe
  have hdblO : ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + texV1Even (parentsAt w).even ∈ tEvenSet u2 →
      (f u2).tEven.val (x + texV1Even (parentsAt w).even) - (f u2).tEven.val x = k := by
    obtain ⟨k, hk⟩ := translation_v1 _ _ _ _ hTE
    refine ⟨k, fun x hx hxv => ?_⟩
    rw [hq] at hxv ⊢
    exact hk x (by rw [hdE]; exact hx) (by rw [hdE]; exact hxv)
  have hdblE : ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + texV2 (parentsAt w).odd ∈ tOddSet u1 →
      (f u1).tOdd.val (x + texV2 (parentsAt w).odd) - (f u1).tOdd.val x -
        ClosedPathSum.dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) x = k := by
    obtain ⟨k, hk⟩ := translation_v2 _ _ _ _ hTO
    refine ⟨k, fun x hx hxv => ?_⟩
    rw [hp] at hxv ⊢
    exact hk x (by rw [hdO]; exact hx) (by rw [hdO]; exact hxv)
  obtain ⟨hmO, hmE⟩ := hmc f w u1 u2 hgood hw hreg
  obtain ⟨κo, hMo, hDo⟩ := ClosedPathTriOdd.closedPathOdd_final w u1 u2 hp hq (f u1).tOdd.val (f u2).tEven.val
    (f u1).tOdd.dom (f u2).tEven.dom 0 hRP hRQ hsP hsQ hdblO hmO
  have hT1 : (stateAt w).tOdd = oddTile u1 := (regsAt_tiles w).1 u1 (by rw [hreg])
  have hT2 : (stateAt w).tEven = evenTile u2 := (regsAt_tiles w).2.2.1 u2 (by rw [hreg])
  obtain ⟨κe, hMe, hDe⟩ := ClosedPathTriEven.closedPathEven_final w u1 u2 hw hT1 hT2 hp hq (f u1).tOdd.val
    (f u2).tEven.val 0 (by rw [← hdO]; exact hRP) (by rw [← hdE]; exact hRQ) hsP hsQ hdblE hmE
  obtain ⟨go, hgo⟩ := ChildGlue.glue_kept_pieces (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) (SiteInduction.marksOdd u1)
    (SiteInduction.marksEven u2) (dblOdd w) (fun i z => placedOdd w (f u1).tOdd.val (f u2).tEven.val 0 i z + κo i)
    (fun a ha b hb z h1 h2 => MixedFromCells.mixedOdd_all w hw u1 u2 hT1 hT2 a ha b hb z h1 h2) hMo hDo
  obtain ⟨ge, hge⟩ := ChildGlue.glue_kept_pieces (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2)
    (SiteInduction.marksOdd u1) (SiteInduction.marksEven u2) dblEven
    (fun i z => placedEven w (f u1).tOdd.val (f u2).tEven.val 0 i z + κe i)
    (fun a ha b hb z h1 h2 => MixedFromCells.mixedEven_all w hw u1 u2 hT1 hT2 a ha b hb z h1 h2) hMe hDe
  have hglue : GluedChildren f w u1 u2 κo κe go ge := ⟨hMo, hDo, hgo, hMe, hDe, hge⟩
  obtain ⟨hRo, hRe⟩ := hgr f w u1 u2 hgood hw hreg (hsl f w.length hgood) κo κe go ge hglue
  have hWp := hgl f w u1 u2 hgood hw hreg κo κe go ge hglue
  refine ⟨⟨oddTile w, go⟩, ⟨evenTile w, ge⟩, ⟨?_, ?_, fun h => absurd h hw, fun _ => ⟨?_, ?_⟩, hRo, hRe⟩, hWp⟩
  · rw [hS]; rfl
  · rw [hS]; rfl
  · rw [hS]
    exact oddNode_of_kept w u1 u2 hw hreg _ _ (by simpa only [hb1] using hdO) (by simpa only [hb2] using hdE)
      (by simpa only [hb2] using hRQ) κo (by simpa only [hb1, hb2] using hDo) go (by simpa only [hb1, hb2] using hgo)
  · rw [hS]
    exact evenNode_of_kept w u1 u2 hw hreg _ _ (by simpa only [hb1] using hdO) (by simpa only [hb2] using hdE)
      (by simpa only [hb1] using hRP) κe (by simpa only [hb1, hb2] using hDe) ge (by simpa only [hb1, hb2] using hge)

end FLatticePaper.Tiles.WeakStepAssembly
