import FLatticePaper.Tiles.ConnectedL
import FLatticePaper.Tiles.TileCompatInputs
import FLatticePaper.Tiles.BaseTileAssembly
import FLatticePaper.Tiles.TileTranslationStd

/-!
# The tile step of the joint induction for the paper data

`tileStep_paper` proves `JointInduction.TileStepInput D` for the paper data from named inputs. At a base word the tile odometers
are the weak ones (`TilePart`), with (a), (b) from `BaseTileProps.base_tileProps`. At any other word the tile odometer of a child
that is not corrected is the weak one, and that of a corrected child is the glued odometer of its tile decomposition
(`JointGlue.gluedOdo`), with constants from `lemma:pairwise_compatibility` (`agree_of_pairs`: the connectivity of the overlap
graphs, `JointRot.std_connected` and `ConnectedAltL.connectedAlt_of`, the local compatibility of the pieces, and condition (C) on
the closed walks). (a) is `TileTranslationStd.tileTranslation_odd`/`_even` from the respects and (c).
-/

namespace FLatticePaper.Tiles.TileStepAssembly

open FLatticePaper.Farey
open FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointInduction (GoodBelow TileStepInput)
open FLatticePaper.Tiles.JointGlue (goodPart pieceVal PiecesAgree PiecesCovered gluedOdo agree_of_compatible)
open FLatticePaper.Tiles.TileCompatInputs (PairCompat oddLIdx evenLIdx altOddLIdx altEvenLIdx)
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.Standard (IsBase)
open FLatticePaper.Tiles.SurgicalWeak (RespectsAnchored)
open FLatticePaper.Tiles.SurgicalAlt (RespectsHalfH RespectsHalfV altFwdHAnchor altRevVAnchor altTypeOf altQ1Coeff altP1Coeff)
open FLatticePaper.Construction (texV1Odd texV1Even texV2)

/-! ### Constants from local compatibility and condition (C) -/

/-- Condition (C) for a decomposition: for any constants that are the differences of the pieces on their overlaps, the sum along
every closed walk of the overlap graph is zero. -/
def WalkZero (ps : List Piece) : Prop :=
  ∀ off : Fin ps.length → Fin ps.length → ℤ,
    (∀ i j, ∀ x ∈ goodPart ps i ∩ goodPart ps j, pieceVal (ps.get i) x.1 - pieceVal (ps.get j) x.1 = off i j) →
    ∀ (i : Fin ps.length) (walk : (overlapGraph (goodPart ps)).Walk i i), walkSum off walk = 0

/-- `lemma:pairwise_compatibility` from the local compatibility of every pair of pieces and condition (C). -/
theorem agree_of_pairs (ps : List Piece) (hcov : PiecesCovered ps) (hconn : (overlapGraph (goodPart ps)).Connected)
    (hpair : ∀ i j : ℕ, PairCompat ps i j) (hwz : WalkZero ps) : ∃ κ : ℕ → ℤ, PiecesAgree ps κ := by
  have h : ∀ i j : Fin ps.length, ∃ c : ℤ, ∀ x ∈ goodPart ps i ∩ goodPart ps j,
      pieceVal (ps.get i) x.1 - pieceVal (ps.get j) x.1 = c := by
    intro i j
    obtain ⟨c, hc⟩ := hpair i j (ps.get i) (ps.get j) (by simp) (by simp)
    exact ⟨c, fun x ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ => hc x.1 h1 h3 h2 h4⟩
  choose off hoff using h
  exact agree_of_compatible ps hcov off hconn hoff (hwz off hoff)

/-- A pair of pieces is compatible with itself. -/
theorem pairCompat_refl (ps : List Piece) (i : ℕ) : PairCompat ps i i := by
  intro p q hp hq
  rw [hp] at hq
  cases hq
  exact ⟨0, fun x _ _ _ _ => sub_self _⟩

theorem pairCompat_symm {ps : List Piece} {i j : ℕ} (h : PairCompat ps j i) : PairCompat ps i j := by
  intro p q hp hq
  obtain ⟨c, hc⟩ := h q p hq hp
  exact ⟨-c, fun x hxp hxq hep heq => by have := hc x hxq hxp heq hep; linarith⟩

theorem pairCompat_of_none_left {ps : List Piece} {i j : ℕ} (h : ps[i]? = none) : PairCompat ps i j := by
  intro p q hp _
  rw [h] at hp
  cases hp

theorem pairCompat_of_none_right {ps : List Piece} {i j : ℕ} (h : ps[j]? = none) : PairCompat ps i j := by
  intro p q _ hq
  rw [h] at hq
  cases hq

/-- Every pair of a six-piece decomposition is compatible when the pairs off the entries `L` are, and each entry of `L` is with
every other piece. -/
theorem pairCompat_all (ps : List Piece) (L : List ℕ) (hlen : ps.length = 6)
    (hstd : ∀ i j, i ∉ L → j ∉ L → PairCompat ps i j) (hL : ∀ i ∈ L, ∀ j < 6, j ≠ i → PairCompat ps i j) :
    ∀ i j, PairCompat ps i j := by
  intro i j
  by_cases hi : i ∈ L
  · by_cases hj6 : j < 6
    · by_cases hji : j = i
      · subst hji; exact pairCompat_refl ps j
      · exact hL i hi j hj6 hji
    · exact pairCompat_of_none_right (by rw [List.getElem?_eq_none_iff]; omega)
  · by_cases hj : j ∈ L
    · by_cases hi6 : i < 6
      · exact pairCompat_symm (hL j hj i hi6 (fun h => hi (h ▸ hj)))
      · exact pairCompat_of_none_left (by rw [List.getElem?_eq_none_iff]; omega)
    · exact hstd i j hi hj

/-! ### The decompositions of the children of `w`, over the family below `w` -/

/-- The decomposition of the odd standard tile odometer of `w`. -/
abbrev tOP (D : JointData) (f : Word → JSlice) (w : Word) : List Piece :=
  tileOddPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (fun u => (below f w u).lEven) w

/-- The decomposition of the even standard tile odometer of `w`. -/
abbrev tEP (D : JointData) (f : Word → JSlice) (w : Word) : List Piece :=
  tileEvenPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (fun u => (below f w u).lOdd) w

/-- The decomposition of the odd alternate tile odometer of `w`. -/
abbrev aOP (D : JointData) (f : Word → JSlice) (w : Word) : List Piece :=
  tileAltOddPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (fun u => (below f w u).aOdd)
    (fun u => (below f w u).aEven) (fun u => (below f w u).lOdd) w

/-- The decomposition of the even alternate tile odometer of `w`. -/
abbrev aEP (D : JointData) (f : Word → JSlice) (w : Word) : List Piece :=
  tileAltEvenPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (fun u => (below f w u).aOdd)
    (fun u => (below f w u).aEven) (fun u => (below f w u).lEven) w

/-! ### The named inputs

Each is a statement of the text not proved here; they are phrased like `WeakStepAssembly.GlueRespectsInput` and
`TileCompatInputs`, over the family below `w`. -/

/-- At the children that are not corrected, the weak odometers respect the tile decompositions (the tile odometer of such a
child is the weak one, `TilePart`): the copies of the weak nodes on the kept parts extend to the full copies of the tile
decompositions, the overlaps that `keptPart` removes being compatible. -/
def UncorrectedPiecesInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w : Word) (wo we wao wae : PartialOdometer), GoodBelow D f w.length → ¬ IsBase w →
    WeakPart D (below f w) w wo we → WeakAltPart D (below f w) w wao wae →
    (¬ CorrectedAfterThree w → RespectsPieces wo (tOP D f w) ∧ RespectsPieces wae (aEP D f w)) ∧
    (¬ CorrectedAfterTwo w → RespectsPieces we (tEP D f w) ∧ RespectsPieces wao (aOP D f w))

/-- Local compatibility of the full copies of a corrected tile decomposition (the pairs not involving an L-correction; those are
`TileCompatInputs.CorrectedCompatInput`). -/
def StdPairCompatInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w : Word), GoodBelow D f w.length → ¬ IsBase w →
    (CorrectedAfterThree w →
      (∀ i j, i ∉ oddLIdx w → j ∉ oddLIdx w → PairCompat (tOP D f w) i j) ∧
      (∀ i j, i ∉ altEvenLIdx → j ∉ altEvenLIdx → PairCompat (aEP D f w) i j)) ∧
    (CorrectedAfterTwo w →
      (∀ i j, i ∉ evenLIdx → j ∉ evenLIdx → PairCompat (tEP D f w) i j) ∧
      (∀ i j, i ∉ altOddLIdx → j ∉ altOddLIdx → PairCompat (aOP D f w) i j))

/-- Condition (C) for the corrected tile decompositions: the overlap constants sum to zero along every closed walk. -/
def TileWalkZeroInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w : Word), GoodBelow D f w.length → ¬ IsBase w →
    (CorrectedAfterThree w → WalkZero (tOP D f w) ∧ WalkZero (aEP D f w)) ∧
    (CorrectedAfterTwo w → WalkZero (tEP D f w) ∧ WalkZero (aOP D f w))

/-- The domains of the corrected tile decompositions are the printed tiles (`LCorrecProps.CorrectedCells` over the family). -/
def CorrectedDomainInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w : Word), GoodBelow D f w.length →
    (CorrectedAfterThree w → pieceUnion (tOP D f w) = Standard.oddTile w ∧
      pieceUnion (aEP D f w) = SurgicalAltTiles.altEvenTile PaperAltBase.paperAltBaseTiles w) ∧
    (CorrectedAfterTwo w → pieceUnion (tEP D f w) = Standard.evenTile w ∧
      pieceUnion (aOP D f w) = SurgicalAltTiles.altOddTile PaperAltBase.paperAltBaseTiles w)

/-- At a corrected child the glued tile odometers respect the boundary words of the child ((a) of the weak lemmas, from the
sides of the L-corrections). -/
def CorrectedRespectsInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w : Word), GoodBelow D f w.length →
    (CorrectedAfterThree w → ∀ κ κ' : ℕ → ℤ, PiecesAgree (tOP D f w) κ → PiecesAgree (aEP D f w) κ' →
      RespectsAnchored (gluedOdo (tOP D f w) κ).dom (hWordOf w false) (vWordOf w false) (gluedOdo (tOP D f w) κ).val ∧
      RespectsHalfH (altFwdHAnchor D.anc w) (hWordOf w true) (gluedOdo (aEP D f w) κ').val) ∧
    (CorrectedAfterTwo w → ∀ κ κ' : ℕ → ℤ, PiecesAgree (tEP D f w) κ → PiecesAgree (aOP D f w) κ' →
      RespectsAnchored (gluedOdo (tEP D f w) κ).dom (hWordOf w true) (vWordOf w true) (gluedOdo (tEP D f w) κ).val ∧
      RespectsHalfV (altRevVAnchor D.anc w) (vWordOf w false) (gluedOdo (aOP D f w) κ').val)

/-- (c) of `lemma:weak_standard_odometer_properties` for the tile odometers of the corrected standard children. -/
def CorrectedLatticeInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w : Word) (wo we wao wae tod tev aod aev : PartialOdometer), GoodBelow D f w.length →
    TilePart D (below f w) w wo we wao wae tod tev aod aev →
    (CorrectedAfterThree w →
      LatticeSelfCompatible tod (texV1Odd ((parentsAt w).current .odd)) 0 ∧
      LatticeSelfCompatible tod (texV2 ((parentsAt w).current .odd))
        (offsetA ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den true)) ∧
    (CorrectedAfterTwo w →
      LatticeSelfCompatible tev (texV1Even ((parentsAt w).current .even)) 0 ∧
      LatticeSelfCompatible tev (texV2 ((parentsAt w).current .even))
        (offsetA ((parentsAt w).current .even).num ((parentsAt w).current .even).den true))

/-- (b) of `lemma:tile-odometer-existence` at a word that is not a base word. -/
def HalfTurnInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w : Word) (wo we wao wae tod tev aod aev : PartialOdometer), GoodBelow D f w.length → ¬ IsBase w →
    WeakPart D (below f w) w wo we → WeakAltPart D (below f w) w wao wae →
    TilePart D (below f w) w wo we wao wae tod tev aod aev →
    TileHalfTurn tod (texV1Odd ((parentsAt w).current .odd)) (texV2 ((parentsAt w).current .odd))
        (offsetA ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den true) ∧
      TileHalfTurn tev (texV1Even ((parentsAt w).current .even)) (texV2 ((parentsAt w).current .even))
        (offsetA ((parentsAt w).current .even).num ((parentsAt w).current .even).den true) ∧
      AltHalfTurn aod (altD w true) (altE w) ∧ AltHalfTurn aev (altD w false) (altE w)

/-- (b) of `lemma:weak_alternate_odometer_properties` for the alternate tile odometers of the corrected alternate children. -/
def AltLatticeInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w : Word) (wo we wao wae tod tev aod aev : PartialOdometer), GoodBelow D f w.length →
    TilePart D (below f w) w wo we wao wae tod tev aod aev →
    (CorrectedAfterTwo w → AltLatticeOdd w aod) ∧ (CorrectedAfterThree w → AltLatticeEven w aev)

/-! ### From the tile part to the tile properties -/

/-- (a), (b) and (b) of the alternate weak lemma from the tile part: (a) from the respects and (c) (the weak (c) at the children
that are not corrected, `CorrectedLatticeInput` at the corrected ones), (b) given. -/
theorem props_of_part (D : JointData) (g : Word → JSlice) (w : Word) (wo we wao wae tod tev aod aev : PartialOdometer)
    (hP : TilePart D g w wo we wao wae tod tev aod aev) (hWU : WeakPropsU w wo we) (hWAU : WeakAltPropsU w wao wae)
    (hlat : (CorrectedAfterThree w →
      LatticeSelfCompatible tod (texV1Odd ((parentsAt w).current .odd)) 0 ∧
      LatticeSelfCompatible tod (texV2 ((parentsAt w).current .odd))
        (offsetA ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den true)) ∧
      (CorrectedAfterTwo w →
      LatticeSelfCompatible tev (texV1Even ((parentsAt w).current .even)) 0 ∧
      LatticeSelfCompatible tev (texV2 ((parentsAt w).current .even))
        (offsetA ((parentsAt w).current .even).num ((parentsAt w).current .even).den true)))
    (hht : TileHalfTurn tod (texV1Odd ((parentsAt w).current .odd)) (texV2 ((parentsAt w).current .odd))
        (offsetA ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den true) ∧
      TileHalfTurn tev (texV1Even ((parentsAt w).current .even)) (texV2 ((parentsAt w).current .even))
        (offsetA ((parentsAt w).current .even).num ((parentsAt w).current .even).den true) ∧
      AltHalfTurn aod (altD w true) (altE w) ∧ AltHalfTurn aev (altD w false) (altE w))
    (hal : (CorrectedAfterTwo w → AltLatticeOdd w aod) ∧ (CorrectedAfterThree w → AltLatticeEven w aev)) :
    TileProps w tod tev aod aev ∧ AltLatticeSelfCompat w aod aev := by
  obtain ⟨-, -, h3, h2, rO, rE, -⟩ := hP
  have lo : LatticeSelfCompatible tod (texV1Odd ((parentsAt w).current .odd)) 0 ∧
      LatticeSelfCompatible tod (texV2 ((parentsAt w).current .odd))
        (offsetA ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den true) := by
    by_cases hc : CorrectedAfterThree w
    · exact hlat.1 hc
    · rw [(h3 hc).1]; exact hWU.1 hc
  have le : LatticeSelfCompatible tev (texV1Even ((parentsAt w).current .even)) 0 ∧
      LatticeSelfCompatible tev (texV2 ((parentsAt w).current .even))
        (offsetA ((parentsAt w).current .even).num ((parentsAt w).current .even).den true) := by
    by_cases hc : CorrectedAfterTwo w
    · exact hlat.2 hc
    · rw [(h2 hc).1]; exact hWU.2 hc
  refine ⟨⟨TileTranslationStd.tileTranslation_odd w tod rO lo.1 lo.2,
    TileTranslationStd.tileTranslation_even w tev rE le.1 le.2, hht.1, hht.2.1, hht.2.2.1, hht.2.2.2⟩, ?_, ?_⟩
  · by_cases hc : CorrectedAfterTwo w
    · exact hal.1 hc
    · rw [(h2 hc).2]; exact hWAU.1 hc
  · by_cases hc : CorrectedAfterThree w
    · exact hal.2 hc
    · rw [(h3 hc).2]; exact hWAU.2 hc

/-! ### The tile step -/

/-- **The tile step of the joint induction for the paper data**: `TileStepInput D` from the named inputs. -/
theorem tileStep_paper (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hAB : PaperAltBdry D) (hlS : D.lSides = paperLSides) (hN1 : UncorrectedPiecesInput D)
    (hcc : TileCompatInputs.CorrectedCompatInput D) (hsp : StdPairCompatInput D) (hwz : TileWalkZeroInput D)
    (hdom : CorrectedDomainInput D) (hres : CorrectedRespectsInput D) (hlat : CorrectedLatticeInput D)
    (hht : HalfTurnInput D) (hal : AltLatticeInput D) : TileStepInput D := by
  intro f w wo we wao wae hG hWP hWU hWA hWAU
  have hJ : ∀ u : Word, u.length < w.length → IsJointSlice D f u := fun u hu => (hG u hu).1
  have hT : ∀ u : Word, u.length < w.length → TileProps u (f u).tOdd (f u).tEven (f u).aOdd (f u).aEven :=
    fun u hu => (hG u hu).2.2.1
  by_cases hb : IsBase w
  · have hP : TilePart D (below f w) w wo we wao wae wo we wao wae :=
      ⟨fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun h => absurd hb h, fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩,
        hWP.2.2.2.2.1 (fun h => h.1 hb), hWP.2.2.2.2.2.1 (fun h => h.1 hb), hWA.2.2.2.2.1, hWA.2.2.2.2.2.1,
        hWP.1, hWP.2.1, hWA.1, hWA.2.1⟩
    have hbc := hWP.2.2.1 hb
    rw [hS] at hbc
    have hac := hWA.2.2.1 hb
    rw [hA] at hac
    exact ⟨wo, we, wao, wae, hP, BaseTileProps.base_tileProps w hb wo we wao wae hbc hac,
      hWAU.1 (fun h => h.1 hb), hWAU.2 (fun h => h.1 hb)⟩
  have finish : ∀ tod tev aod aev : PartialOdometer, TilePart D (below f w) w wo we wao wae tod tev aod aev →
      ∃ tod tev aod aev : PartialOdometer, TilePart D (below f w) w wo we wao wae tod tev aod aev ∧
        TileProps w tod tev aod aev ∧ AltLatticeSelfCompat w aod aev := fun tod tev aod aev hP =>
    ⟨tod, tev, aod, aev, hP, props_of_part D (below f w) w wo we wao wae tod tev aod aev hP hWU hWAU
      (hlat f w wo we wao wae tod tev aod aev hG hP) (hht f w wo we wao wae tod tev aod aev hG hb hWP hWA hP)
      (hal f w wo we wao wae tod tev aod aev hG hP)⟩
  have n1 := hN1 f w wo we wao wae hG hb hWP hWA
  obtain ⟨cO, cE⟩ := JointRot.std_connected D hlS f w hb hJ
  obtain ⟨cAO, cAE⟩ := ConnectedAltL.connectedAlt_of D hlS f w hb hJ hT
  rcases w.eq_nil_or_concat with rfl | ⟨wd, d, hwd⟩
  · exact absurd (Or.inl rfl) hb
  rw [List.concat_eq_append] at hwd
  subst hwd
  have hl : (wd ++ [d]).getLast? = some d := by simp
  cases d
  · have nc3 : ¬ CorrectedAfterThree (wd ++ [Digit.one]) := fun h => by simp [CorrectedAfterThree] at h
    have nc2 : ¬ CorrectedAfterTwo (wd ++ [Digit.one]) := fun h => by simp [CorrectedAfterTwo] at h
    exact finish wo we wao wae ⟨fun h => absurd h hb, fun _ => ⟨(n1.1 nc3).1, (n1.2 nc2).1, (n1.2 nc2).2, (n1.1 nc3).2⟩,
      fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, hWP.2.2.2.2.1 nc3, hWP.2.2.2.2.2.1 nc2, hWA.2.2.2.2.1, hWA.2.2.2.2.2.1,
      hWP.1, hWP.2.1, hWA.1, hWA.2.1⟩
  · -- after a `2`: the even child and the odd alternate child are corrected
    have c2 : CorrectedAfterTwo (wd ++ [Digit.two]) := ⟨hb, hl⟩
    have nc3 : ¬ CorrectedAfterThree (wd ++ [Digit.two]) := fun h => by simp [CorrectedAfterThree] at h
    have lE : (tEP D f (wd ++ [Digit.two])).length = 6 := by simp [tileEvenPieces]
    have lA : (aOP D f (wd ++ [Digit.two])).length = 6 := by simp [tileAltOddPieces, altTypeOf, altQ1Coeff]
    have covE := JointGlue.tileEvenPieces_covered D.S (fun u => (below f (wd ++ [Digit.two]) u).tOdd)
      (fun u => (below f (wd ++ [Digit.two]) u).tEven) (fun u => (below f (wd ++ [Digit.two]) u).lOdd) (wd ++ [Digit.two])
    have covA := JointRot.tileAltOddPieces_covered' D.S (fun u => (below f (wd ++ [Digit.two]) u).tOdd)
      (fun u => (below f (wd ++ [Digit.two]) u).tEven) (fun u => (below f (wd ++ [Digit.two]) u).aOdd)
      (fun u => (below f (wd ++ [Digit.two]) u).aEven) (fun u => (below f (wd ++ [Digit.two]) u).lOdd) (wd ++ [Digit.two])
    obtain ⟨κ, hκ⟩ := agree_of_pairs _ covE cE
      (pairCompat_all _ evenLIdx lE ((hsp f _ hG hb).2 c2).1 ((hcc f _ hG hb).2.1 c2)) ((hwz f _ hG hb).2 c2).1
    obtain ⟨κ', hκ'⟩ := agree_of_pairs _ covA cAO
      (pairCompat_all _ altOddLIdx lA ((hsp f _ hG hb).2 c2).2 ((hcc f _ hG hb).2.2.1 c2)) ((hwz f _ hG hb).2 c2).2
    obtain ⟨rE, rA⟩ := (hres f _ hG).2 c2 κ κ' hκ hκ'
    obtain ⟨dE, dA⟩ := (hdom f _ hG).2 c2
    exact finish wo (gluedOdo _ κ) (gluedOdo _ κ') wae
      ⟨fun h => absurd h hb, fun _ => ⟨(n1.1 nc3).1, JointGlue.respectsPieces_glued _ κ covE hκ,
        JointGlue.respectsPieces_glued _ κ' covA hκ', (n1.1 nc3).2⟩,
        fun _ => ⟨rfl, rfl⟩, fun h => absurd c2 h, hWP.2.2.2.2.1 nc3, rE, rA, hWA.2.2.2.2.2.1,
        hWP.1, by show pieceUnion _ = _; rw [dE, hS]; rfl, by show pieceUnion _ = _; rw [dA, (hAB _).1], hWA.2.1⟩
  · -- after a `3`: the odd child and the even alternate child are corrected
    have c3 : CorrectedAfterThree (wd ++ [Digit.three]) := ⟨hb, hl⟩
    have nc2 : ¬ CorrectedAfterTwo (wd ++ [Digit.three]) := fun h => by simp [CorrectedAfterTwo] at h
    have lO : (tOP D f (wd ++ [Digit.three])).length = 6 := by simp [tileOddPieces]
    have lA : (aEP D f (wd ++ [Digit.three])).length = 6 := by
      cases h : W1Odd (wd ++ [Digit.three]) <;> simp [tileAltEvenPieces, altTypeOf, altP1Coeff, h]
    have covO := JointGlue.tileOddPieces_covered D.S (fun u => (below f (wd ++ [Digit.three]) u).tOdd)
      (fun u => (below f (wd ++ [Digit.three]) u).tEven) (fun u => (below f (wd ++ [Digit.three]) u).lEven) (wd ++ [Digit.three])
    have covA := JointRot.tileAltEvenPieces_covered' D.S (fun u => (below f (wd ++ [Digit.three]) u).tOdd)
      (fun u => (below f (wd ++ [Digit.three]) u).tEven) (fun u => (below f (wd ++ [Digit.three]) u).aOdd)
      (fun u => (below f (wd ++ [Digit.three]) u).aEven) (fun u => (below f (wd ++ [Digit.three]) u).lEven) (wd ++ [Digit.three])
    obtain ⟨κ, hκ⟩ := agree_of_pairs _ covO cO
      (pairCompat_all _ (oddLIdx _) lO ((hsp f _ hG hb).1 c3).1 ((hcc f _ hG hb).1 c3)) ((hwz f _ hG hb).1 c3).1
    obtain ⟨κ', hκ'⟩ := agree_of_pairs _ covA cAE
      (pairCompat_all _ altEvenLIdx lA ((hsp f _ hG hb).1 c3).2 ((hcc f _ hG hb).2.2.2 c3)) ((hwz f _ hG hb).1 c3).2
    obtain ⟨rO, rA⟩ := (hres f _ hG).1 c3 κ κ' hκ hκ'
    obtain ⟨dO, dA⟩ := (hdom f _ hG).1 c3
    exact finish (gluedOdo _ κ) we wao (gluedOdo _ κ')
      ⟨fun h => absurd h hb, fun _ => ⟨JointGlue.respectsPieces_glued _ κ covO hκ, (n1.2 nc2).1, (n1.2 nc2).2,
        JointGlue.respectsPieces_glued _ κ' covA hκ'⟩,
        fun h => absurd c3 h, fun _ => ⟨rfl, rfl⟩, rO, hWP.2.2.2.2.2.1 nc2, hWA.2.2.2.2.1, rA,
        by show pieceUnion _ = _; rw [dO, hS]; rfl, hWP.2.1, hWA.1, by show pieceUnion _ = _; rw [dA, (hAB _).2]⟩

end FLatticePaper.Tiles.TileStepAssembly
