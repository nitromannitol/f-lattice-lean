import FLatticePaper.Tiles.LSidesEvenK
import FLatticePaper.Tiles.GlueStringDecomp
import FLatticePaper.Tiles.GlueRespectsAll
import FLatticePaper.Tiles.AltItem3
import FLatticePaper.Tiles.DoubleTopBase

/-! # The top side of the `-` even L-correction in the double case `pre = 2^{j+1}`

For `w = 2^{j+1} 3^k` the top string of the even child of `w` is, through the second copies of the doubled odd register
(entry `3` of `tileEvenPieces`) and the second copies of the even register (entry `5`) of the nested decompositions of the even
children of `2^{j+1} 3^i`, covered by `k` copies of the odd register of `2^{j+1}` (the odd tile of `2^j`) and the top string of the
even base tile of `2^{j+1}` (`GlueStringDecomp.even_ef`). These copies carry the affine factor `a_{q,2} + (2k+1) a_{p,2}` of the
stems of the `-` even L-correction, and they sit at its stems. On the base tile the last stem and the enlarged piece are given by
the base fact `DoubleTopBaseInput`. -/

namespace FLatticePaper.Tiles.LSidesEvenTopD

open FLatticePaper.Farey
open FLatticePaper.Construction (texV1Odd texV1Even texV2)
open FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (IsBase stateAt oddTile evenTile shift)
open FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointGlue (PiecesAgree gluedOdo)
open FLatticePaper.Tiles.LSidesEvenK
open FLatticePaper.Tiles.SurgicalWeak (regsAt regOdo)
open FLatticePaper.Tiles.JointInduction (GoodBelow regsAt_lt)
open FLatticePaper.Tiles.WeakStepPaper (paperS regsAt_tiles)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)

/-! ### Copies placed with an affine factor -/

/-- `o` contains the copy of `q` placed at `s` with affine factor `a`, up to one constant. -/
def PlacedEqA (o q : PartialOdometer) (s a : Site) : Prop :=
  ∃ b : ℤ, ∀ y ∈ q.dom, y + s ∈ o.dom ∧ o.val (y + s) = q.val y + dotS a (y + s) + b

theorem placedEqA_trans {o q r : PartialOdometer} {s t a a' : Site} (h1 : PlacedEqA o q s a)
    (h2 : PlacedEqA q r t a') : PlacedEqA o r (t + s) (a + a') := by
  obtain ⟨b, hb⟩ := h1
  obtain ⟨b', hb'⟩ := h2
  refine ⟨b + b' - dotS a' s, fun y hy => ?_⟩
  obtain ⟨hq, hv⟩ := hb' y hy
  obtain ⟨ho, hv'⟩ := hb (y + t) hq
  rw [← add_assoc]
  refine ⟨ho, ?_⟩
  rw [hv', hv]
  simp only [dotS, Prod.fst_add, Prod.snd_add]
  ring

/-- A piece of a decomposition that `o` respects is placed in `o` with its affine factor. -/
theorem placedEqA_of_respects {o : PartialOdometer} {ps : List Piece} (h : RespectsPieces o ps) {i : ℕ}
    {q : PartialOdometer} {s a : Site} (hi : ps[i]? = some (stdPiece q s a)) : PlacedEqA o q s a := by
  obtain ⟨b, hb⟩ := h.2 _ (List.mem_of_getElem? hi)
  refine ⟨b, fun y hy => ?_⟩
  have hp : y + s ∈ (stdPiece q s a).placed := Finset.mem_image.2 ⟨y, hy, rfl⟩
  refine ⟨h.1 ▸ LSidesEven.mem_pieceUnion_of hi hp, ?_⟩
  rw [hb (y + s) hp (by simp [stdPiece])]
  simp [stdPiece]

/-! ### The vectors along trailing `3`s -/

theorem vP2_snoc_three (v : Word) : vP2 (v ++ [Digit.three]) = vP2 v := by
  simp [vP2, CeilWords.parentsAt_snoc_three]

theorem aP2_snoc_three (v : Word) : aP2 (v ++ [Digit.three]) = aP2 v := by
  simp [aP2, CeilWords.parentsAt_snoc_three]

theorem vQ2_snoc_three (v : Word) : vQ2 (v ++ [Digit.three]) = vQ2 v + vP2 v + vP2 v := by
  simp only [vQ2, vP2, CeilWords.parentsAt_snoc_three, Parents.current, Parents.combine]
  ext <;> simp [texV2] <;> ring

theorem aQ2_snoc_three (v : Word) : aQ2 (v ++ [Digit.three]) = aQ2 v + aP2 v + aP2 v := by
  simp only [aQ2, aP2, CeilWords.parentsAt_snoc_three, Parents.current, Parents.combine]
  ext <;> simp [offsetA] <;> ring

theorem wkT (pre : Word) (k : ℕ) :
    W1Odd (wk pre k) = W1Odd pre ∧ vP1 (wk pre k) = vP1 pre ∧ vP2 (wk pre k) = vP2 pre ∧
      vQ2 (wk pre k) = vQ2 pre + (2 * (k : ℤ)) • vP2 pre ∧ aP2 (wk pre k) = aP2 pre ∧
      aQ2 (wk pre k) = aQ2 pre + (2 * (k : ℤ)) • aP2 pre := by
  induction k with
  | zero => simp [wk]
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih
    rw [wk_succ]
    refine ⟨by rw [W1Odd_snoc_three, h1], by rw [vP1_snoc_three, h2], by rw [vP2_snoc_three, h3], ?_,
      by rw [aP2_snoc_three, h5], ?_⟩
    · rw [vQ2_snoc_three, h4, h3]
      ext <;> simp <;> ring
    · rw [aQ2_snoc_three, h6, h5]
      ext <;> simp <;> ring

/-! ### The nested copies along the top string -/

/-- The offset of the stem `m` of the `-` even L-correction of `pre 3^k` (`W_1` even). -/
def nestT (pre : Word) (k m : ℕ) : Site := vQ2 pre + (2 * (k : ℤ) + 1) • vP2 pre + (m : ℤ) • vP1 pre

/-- The affine factor of the stems. -/
def affT (pre : Word) (k : ℕ) : Site := aQ2 pre + (2 * (k : ℤ) + 1) • aP2 pre

/-- The offset of the copy of the even register of `pre` (the base tile in the double case). -/
def baseT (pre : Word) (k : ℕ) : Site := (k : ℤ) • (vP1 pre + vP2 pre + vP2 pre)

/-- Its affine factor. -/
def affB (pre : Word) (k : ℕ) : Site := (2 * (k : ℤ)) • aP2 pre

theorem tEP_entry3 (S : SurgicalWeak.WeakData) (pO pE : Word → PartialOdometer) (lO : Word → Bool → Bool → PartialOdometer)
    (v : Word) (hc : v.getLast? ≠ some Digit.two) : (tileEvenPieces S pO pE lO v)[3]? =
      some (stdPiece (regOdo S pO pE (regsAt v).1 true) (q0Off v .p1DMinus + vP2 v) (q0Aff v .p1DMinus + aP2 v)) := by
  simp [tileEvenPieces, hc]

theorem tEP_entry5 (S : SurgicalWeak.WeakData) (pO pE : Word → PartialOdometer) (lO : Word → Bool → Bool → PartialOdometer)
    (v : Word) : (tileEvenPieces S pO pE lO v)[5]? =
      some (stdPiece (regOdo S pO pE (regsAt v).2 false) (q0Off v .q1Minus) (q0Aff v .q1Minus)) := by
  simp [tileEvenPieces]

theorem offs (pre : Word) (hph : W1Odd pre = false) (K : ℕ) :
    q0Off (wk pre K) .p1DMinus + vP2 (wk pre K) = nestT pre K 0 ∧
      q0Aff (wk pre K) .p1DMinus + aP2 (wk pre K) = affT pre K ∧
      q0Off (wk pre K) .q1Minus = vP1 pre + vP2 pre + vP2 pre ∧ q0Aff (wk pre K) .q1Minus = aP2 pre + aP2 pre := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := wkT pre K
  have hq : q0Aff (wk pre K) .p1DMinus = aQ2 (wk pre K) := by
    ext <;> simp [q0Aff, h1, hph, pairAffine, offsetA, aQ2]
  have hq' : q0Aff (wk pre K) .q1Minus = aP2 (wk pre K) + aP2 (wk pre K) := by
    ext <;> simp [q0Aff, h1, hph, pairAffine, offsetA, aP2] <;> ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [q0Off, SurgicalDict.offsetQ0, h1, hph, Bool.false_eq_true, if_false, h3, h4, nestT]
    ext <;> simp <;> ring
  · rw [hq, h5, h6, affT]
    ext <;> simp <;> ring
  · simp only [q0Off, SurgicalDict.offsetQ0, h1, hph, Bool.false_eq_true, if_false, h2, h3]
  · rw [hq', h5]

/-- The top string of a tile lies in the tile. -/
theorem top_inside (T : Finset Site) (wh wv : BinaryWord) (S : GInt → ℤ) (hR : SurgicalWeak.RespectsAnchored T wh wv S)
    (x : GInt) (hx : x ∈ placedSites (sideString wh wv 0 .hMinus)) : x ∈ T := by
  apply hR.1
  simp only [GlueRespectsAll.ps_append, List.mem_append]
  exact Or.inl (Or.inl (Or.inr hx))

/-- **The top string of the even child splits into the strings of its copies** (`W_1` even): each point lies, after the offset
of its copy, on the top string of the odd register (the second copy of `p_1^-`) or on that of the even register (`q_1^-`). -/
theorem top_even_split (w u1 u2 : Word) (hreg : regsAt w = (some u1, some u2)) (hph : W1Odd w = false) (z : GInt)
    (hz : z ∈ placedSites (sideString (hWordOf w true) (vWordOf w true) 0 .hMinus)) :
    z - (q0Off w .p1DMinus + vP2 w) ∈ placedSites (sideString (hWordOf u1 false) (vWordOf u1 false) 0 .hMinus) ∨
      z - q0Off w .q1Minus ∈ placedSites (sideString (hWordOf u2 true) (vWordOf u2 true) 0 .hMinus) := by
  have hph' : phase w ≠ 1 := by intro h; simp [W1Odd, h] at hph
  have hp : (parentsAt w).odd = fracOdd u1 := (WeakStepAssembly.regsAt_parents w).1 u1 (by rw [hreg])
  have hq : (parentsAt w).even = fracEven u2 := (WeakStepAssembly.regsAt_parents w).2 u2 (by rw [hreg])
  obtain ⟨-, -, -, htop⟩ := GlueStringDecomp.even_ef w u1 u2 hreg hph'
  simp only [sideString] at hz ⊢
  rw [htop, GlueRespectsAll.ps_append, List.mem_append] at hz
  rw [StdCornerAnchors.stdAnchorY_odd, StdCornerAnchors.stdAnchorY_even]
  have e1 : q0Off w .p1DMinus + vP2 w = texV2 (fracEven u2) + texV2 (fracOdd u1) := by
    simp [q0Off, SurgicalDict.offsetQ0, hph, vQ2, vP2, hp, hq]
  have e2 : q0Off w .q1Minus = texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1) := by
    simp [q0Off, SurgicalDict.offsetQ0, hph, vP1, vP2, hp]
  rw [e1, e2]
  rcases hz with h | h
  · left
    rw [add_comm (texV2 (fracEven u2) + texV2 (fracOdd u1)), ← GlueChain.hRevStringAt_shift,
      AltItem3.mem_placedSites_map] at h
    exact h
  · right
    rw [add_comm (texV1Odd (fracOdd u1) + texV2 (fracOdd u1) + texV2 (fracOdd u1)), ← GlueChain.hRevStringAt_shift,
      AltItem3.mem_placedSites_map] at h
    exact h

/-- **The nested copies of `2^{j+1} 3^{k+1}` along the top string**: an odometer respecting the even decomposition contains the
odd register of `2^{j+1}` at the stems `nestT pre (k+1) m` (`m ≤ k`) with the affine factor `affT`, and the even base tile odometer
of `2^{j+1}` at `baseT pre (k+1)` with the affine factor `affB`, and these copies cover the top string. -/
theorem nestedT (D : JointData) (f : Word → JSlice) (j : ℕ) :
    ∀ (k : ℕ) (o : PartialOdometer), GoodBelow D f (wk (List.replicate (j + 1) Digit.two) (k + 1)).length →
      RespectsPieces o (tileEvenPieces D.S (fun u => (below f (wk (List.replicate (j + 1) Digit.two) (k + 1)) u).tOdd)
        (fun u => (below f (wk (List.replicate (j + 1) Digit.two) (k + 1)) u).tEven)
        (fun u => (below f (wk (List.replicate (j + 1) Digit.two) (k + 1)) u).lOdd)
        (wk (List.replicate (j + 1) Digit.two) (k + 1))) →
      (∀ m ≤ k, PlacedEqA o (f (List.replicate j Digit.two)).tOdd (nestT (List.replicate (j + 1) Digit.two) (k + 1) m)
          (affT (List.replicate (j + 1) Digit.two) (k + 1))) ∧
        PlacedEqA o (f (List.replicate (j + 1) Digit.two)).tEven (baseT (List.replicate (j + 1) Digit.two) (k + 1))
          (affB (List.replicate (j + 1) Digit.two) (k + 1)) ∧
        ∀ z ∈ placedSites (sideString (hWordOf (wk (List.replicate (j + 1) Digit.two) (k + 1)) true)
            (vWordOf (wk (List.replicate (j + 1) Digit.two) (k + 1)) true) 0 .hMinus),
          (∃ m ≤ k, z - nestT (List.replicate (j + 1) Digit.two) (k + 1) m ∈ (f (List.replicate j Digit.two)).tOdd.dom) ∨
            z - baseT (List.replicate (j + 1) Digit.two) (k + 1) ∈ placedSites (sideString
              (hWordOf (List.replicate (j + 1) Digit.two) true) (vWordOf (List.replicate (j + 1) Digit.two) true) 0 .hMinus) := by
  set pre := List.replicate (j + 1) Digit.two with hpre_def
  obtain ⟨hreg, hph0, -⟩ := twos_facts j
  have hph : W1Odd pre = false := hph0
  have hl1p : (List.replicate j Digit.two).length < pre.length := by simp [pre]
  intro k
  induction k with
  | zero =>
    intro o hgood hR
    obtain ⟨hr1, -, -, -⟩ := wk_regs pre 1
    have hws : wk pre 1 = pre ++ [Digit.three] := by simp [wk]
    have hlt : pre.length < (wk pre 1).length := by rw [hws]; simp
    have hl1 : (List.replicate j Digit.two).length < (wk pre 1).length := lt_trans hl1p hlt
    have hr1' : (regsAt (wk pre 1)).1 = some (List.replicate j Digit.two) := by rw [hr1, hreg]
    have hr2 : (regsAt (wk pre 1)).2 = some pre := by rw [hws, regsAt_snoc_three]
    have hregw : regsAt (wk pre 1) = (some (List.replicate j Digit.two), some pre) := Prod.ext hr1' hr2
    have hb1 : below f (wk pre 1) (List.replicate j Digit.two) = f (List.replicate j Digit.two) := by
      simp only [below, if_pos hl1]
    have hbp : below f (wk pre 1) pre = f pre := by simp only [below, if_pos hlt]
    have hc : (wk pre 1).getLast? ≠ some Digit.two := by rw [hws]; simp
    have e3 := tEP_entry3 D.S (fun u => (below f (wk pre 1) u).tOdd) (fun u => (below f (wk pre 1) u).tEven)
      (fun u => (below f (wk pre 1) u).lOdd) (wk pre 1) hc
    have e5 := tEP_entry5 D.S (fun u => (below f (wk pre 1) u).tOdd) (fun u => (below f (wk pre 1) u).tEven)
      (fun u => (below f (wk pre 1) u).lOdd) (wk pre 1)
    rw [hr1'] at e3
    rw [hr2] at e5
    simp only [regOdo, hb1, hbp] at e3 e5
    obtain ⟨o3, a3, o5, a5⟩ := offs pre hph 1
    rw [o3, a3] at e3
    rw [o5, a5] at e5
    obtain ⟨hS1, -⟩ := hgood _ hl1
    have hRP := (WeakStepAssembly.slice_respects D f _ hS1).1
    have eb : vP1 pre + vP2 pre + vP2 pre = baseT pre 1 := by simp [baseT]
    have ea : aP2 pre + aP2 pre = affB pre 1 := by ext <;> simp [affB] <;> ring
    refine ⟨fun m hm => ?_, ?_, fun z hz => ?_⟩
    · obtain rfl : m = 0 := by omega
      exact placedEqA_of_respects hR e3
    · have h := placedEqA_of_respects hR e5
      rwa [eb, ea] at h
    · rcases top_even_split (wk pre 1) _ _ hregw (by rw [(wkT pre 1).1, hph]) z hz with h | h
      · left
        refine ⟨0, le_rfl, ?_⟩
        rw [← o3]
        exact top_inside _ _ _ _ hRP _ h
      · right
        rw [o5, eb] at h
        exact h
  | succ k ih =>
    intro o hgood hR
    obtain ⟨hr1, -, -, -⟩ := wk_regs pre (k + 2)
    have hws := wk_succ pre (k + 1)
    have hlt : (wk pre (k + 1)).length < (wk pre (k + 2)).length := by rw [hws]; simp
    have hr2 : (regsAt (wk pre (k + 2))).2 = some (wk pre (k + 1)) := by rw [hws, regsAt_snoc_three]
    have hr1' : (regsAt (wk pre (k + 2))).1 = some (List.replicate j Digit.two) := by rw [hr1, hreg]
    have hregw : regsAt (wk pre (k + 2)) = (some (List.replicate j Digit.two), some (wk pre (k + 1))) :=
      Prod.ext hr1' hr2
    have hl1 : (List.replicate j Digit.two).length < (wk pre (k + 2)).length :=
      lt_of_lt_of_le hl1p (by simp [wk])
    have hb1 : below f (wk pre (k + 2)) (List.replicate j Digit.two) = f (List.replicate j Digit.two) := by
      simp only [below, if_pos hl1]
    have hbk : below f (wk pre (k + 2)) (wk pre (k + 1)) = f (wk pre (k + 1)) := by simp only [below, if_pos hlt]
    have hc : (wk pre (k + 2)).getLast? ≠ some Digit.two := by rw [hws]; simp
    have e3 := tEP_entry3 D.S (fun u => (below f (wk pre (k + 2)) u).tOdd) (fun u => (below f (wk pre (k + 2)) u).tEven)
      (fun u => (below f (wk pre (k + 2)) u).lOdd) (wk pre (k + 2)) hc
    have e5 := tEP_entry5 D.S (fun u => (below f (wk pre (k + 2)) u).tOdd) (fun u => (below f (wk pre (k + 2)) u).tEven)
      (fun u => (below f (wk pre (k + 2)) u).lOdd) (wk pre (k + 2))
    rw [hr1'] at e3
    rw [hr2] at e5
    simp only [regOdo, hb1, hbk] at e3 e5
    obtain ⟨o3, a3, o5, a5⟩ := offs pre hph (k + 2)
    rw [o3, a3] at e3
    rw [o5, a5] at e5
    have hP0 := placedEqA_of_respects hR e3
    have hQ := placedEqA_of_respects hR e5
    have hgood' : GoodBelow D f (wk pre (k + 1)).length := fun u hu => hgood u (lt_trans hu hlt)
    have hRk : RespectsPieces (f (wk pre (k + 1))).tEven (tileEvenPieces D.S (fun u => (below f (wk pre (k + 1)) u).tOdd)
        (fun u => (below f (wk pre (k + 1)) u).tEven) (fun u => (below f (wk pre (k + 1)) u).lOdd) (wk pre (k + 1))) :=
      (((hgood (wk pre (k + 1)) hlt).1.2.2.1).2.1 (twos_wk_notBase j k)).2.1
    obtain ⟨hn, hbr, hcov⟩ := ih (f (wk pre (k + 1))).tEven hgood' hRk
    obtain ⟨hS1, -⟩ := hgood _ hl1
    have hRP := (WeakStepAssembly.slice_respects D f _ hS1).1
    have eN : ∀ m : ℕ, nestT pre (k + 1) m + (vP1 pre + vP2 pre + vP2 pre) = nestT pre (k + 2) (m + 1) := by
      intro m; ext <;> simp [nestT] <;> ring
    have eA : aP2 pre + aP2 pre + affT pre (k + 1) = affT pre (k + 2) := by ext <;> simp [affT] <;> ring
    have eB : baseT pre (k + 1) + (vP1 pre + vP2 pre + vP2 pre) = baseT pre (k + 2) := by
      ext <;> simp [baseT] <;> ring
    have eAB : aP2 pre + aP2 pre + affB pre (k + 1) = affB pre (k + 2) := by ext <;> simp [affB] <;> ring
    refine ⟨fun m hm => ?_, ?_, fun z hz => ?_⟩
    · rcases m with _ | m
      · exact hP0
      · have := placedEqA_trans hQ (hn m (by omega))
        rwa [eN, eA] at this
    · have := placedEqA_trans hQ hbr
      rwa [eB, eAB] at this
    · rcases top_even_split (wk pre (k + 2)) _ _ hregw (by rw [(wkT pre (k + 2)).1, hph]) z hz with h | h
      · left
        refine ⟨0, by omega, ?_⟩
        rw [← o3]
        exact top_inside _ _ _ _ hRP _ h
      · rw [o5] at h
        rcases hcov _ h with ⟨m, hm, hm'⟩ | hb
        · left
          refine ⟨m + 1, by omega, ?_⟩
          rw [← eN m]
          rwa [sub_sub, add_comm (vP1 pre + vP2 pre + vP2 pre)] at hm'
        · right
          rw [← eB]
          rwa [sub_sub, add_comm (vP1 pre + vP2 pre + vP2 pre)] at hb

/-- The first `k + 2` entries of the `-` even L-correction of `2^{j+1} 3^k`: the stems at `nestT` with the affine factor `affT`,
and the enlarged piece (no bridge: `W_1` is even and the sign is `-`). -/
theorem evenL_stems_minus (S : SurgicalWeak.WeakData) (pO pE aO aE : Word → PartialOdometer) (j k : ℕ) (elong : Bool) :
    (∀ m ≤ k, (evenLPieces S pO pE aO aE (wk (List.replicate (j + 1) Digit.two) k) false elong)[m]? =
        some (stdPiece (regOdo S pO pE (regsAt (List.replicate (j + 1) Digit.two)).1 true)
          (nestT (List.replicate (j + 1) Digit.two) k m) (affT (List.replicate (j + 1) Digit.two) k))) ∧
      (evenLPieces S pO pE aO aE (wk (List.replicate (j + 1) Digit.two) k) false elong)[k + 1]? =
        some (stdPiece enlOdo
          (baseT (List.replicate (j + 1) Digit.two) k + (vP1 (List.replicate (j + 1) Digit.two) +
            vP2 (List.replicate (j + 1) Digit.two) + vP2 (List.replicate (j + 1) Digit.two)) + ((1 : ℤ), (1 : ℤ)))
          (affB (List.replicate (j + 1) Digit.two) k + (aP2 (List.replicate (j + 1) Digit.two) +
            aP2 (List.replicate (j + 1) Digit.two)))) := by
  set pre := List.replicate (j + 1) Digit.two with hpre_def
  obtain ⟨htc, hst⟩ := wk_trailing pre (twos_trailing j) k
  obtain ⟨hph, -, -, -, -, -⟩ := wkT pre k
  obtain ⟨-, hph0, -⟩ := twos_facts j
  have hphp : W1Odd pre = false := hph0
  have hd : (!pre.isEmpty && pre.all (fun d => decide (d = Digit.two))) = true := by simp [pre]
  have hs2 : decide (pre.getLast? = some Digit.two) = true := by
    simp only [pre, decide_eq_true_eq, List.getLast?_replicate]; simp
  obtain ⟨o3, a3, -, -⟩ := offs pre hphp k
  have hI : evenLInitOff (wk pre k) false = nestT pre k 0 := by simp only [evenLInitOff, if_false, Bool.false_eq_true]; exact o3
  have hIa : evenLInitAff (wk pre k) false = affT pre k := by
    simp only [evenLInitAff, if_false, Bool.false_eq_true]; exact a3
  have hoff : ∀ m : ℕ, evenLInitOff (wk pre k) false +
      altOff pre ((m : ℤ) • (evenKCoeff (W1Odd (wk pre k)) false (decide (pre.getLast? = some Digit.two))).1) =
        nestT pre k m := by
    intro m
    rw [hph, hphp, hs2, hI]
    simp only [evenKCoeff, altOff, SurgicalAlt.coeffOff, nestT]
    ext <;> simp
  have haff : ∀ m : ℕ, evenLInitAff (wk pre k) false +
      altAff pre ((m : ℤ) • (evenKCoeff (W1Odd (wk pre k)) false (decide (pre.getLast? = some Digit.two))).1) =
        affT pre k := by
    intro m
    rw [hph, hphp, hs2, hIa]
    simp only [evenKCoeff, altAff, SurgicalAlt.coeffAffine]
    ext <;> simp
  have hboff : evenLInitOff (wk pre k) false + altOff pre ((k : ℤ) •
      (evenKCoeff (W1Odd (wk pre k)) false (decide (pre.getLast? = some Digit.two))).1 +
      (evenKCoeff (W1Odd (wk pre k)) false (decide (pre.getLast? = some Digit.two))).2.1) + ((1 : ℤ), (1 : ℤ)) =
        baseT pre k + (vP1 pre + vP2 pre + vP2 pre) + ((1 : ℤ), (1 : ℤ)) := by
    rw [hph, hphp, hs2, hI]
    simp only [evenKCoeff, altOff, SurgicalAlt.coeffOff, nestT, baseT]
    ext <;> simp <;> ring
  have hbaff : evenLInitAff (wk pre k) false + altAff pre ((k : ℤ) •
      (evenKCoeff (W1Odd (wk pre k)) false (decide (pre.getLast? = some Digit.two))).1 +
      (evenKCoeff (W1Odd (wk pre k)) false (decide (pre.getLast? = some Digit.two))).2.1) =
        affB pre k + (aP2 pre + aP2 pre) := by
    rw [hph, hphp, hs2, hIa]
    simp only [evenKCoeff, altAff, SurgicalAlt.coeffAffine, affT, affB, aP2, aQ2, offsetA]
    ext <;> simp <;> ring
  have hc01 : (!W1Odd (wk pre k) && !false) = true := by simp [hph, hphp]
  refine ⟨fun m hm => ?_, ?_⟩
  · simp only [evenLPieces, htc, hst, hd, hc01, Bool.and_true, Bool.true_and, if_true]
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_append_left (by simp; omega)]
    simp only [List.getElem?_map, List.getElem?_range (by omega : m < k + 1), Option.map_some]
    rw [hoff m, haff m]
  · simp only [evenLPieces, htc, hst, hd, hc01, Bool.and_true, Bool.true_and, if_true]
    rw [List.getElem?_append_left (by simp)]
    rw [List.getElem?_append_right (by simp)]
    simp only [List.length_append, List.length_map, List.length_range, List.length_nil, add_zero, Nat.sub_self,
      List.getElem?_cons_zero]
    rw [hboff, hbaff]

/-! ### The double case: one constant on the top string -/

theorem dotS_add_l (a b x : Site) : dotS (a + b) x = dotS a x + dotS b x := by simp only [dotS, Prod.fst_add, Prod.snd_add]; ring

theorem dotS_sub_r (a x y : Site) : dotS a (x - y) = dotS a x - dotS a y := by simp only [dotS, Prod.fst_sub, Prod.snd_sub]; ring

theorem dotS_add_r (a x y : Site) : dotS a (x + y) = dotS a x + dotS a y := by simp only [dotS, Prod.fst_add, Prod.snd_add]; ring

/-- The parent vectors of `2^{j+1}`: `p = (j+1)/(j+2)`, `q = 1/1`. -/
theorem pre_vecs (j : ℕ) :
    vP1 (List.replicate (j + 1) Digit.two) = (2 * (j : ℤ) + 4, 2 * (j : ℤ) + 2) ∧
      vP2 (List.replicate (j + 1) Digit.two) = (-1, 2 * (j : ℤ) + 3) ∧ vQ2 (List.replicate (j + 1) Digit.two) = (0, 2) ∧
      aP2 (List.replicate (j + 1) Digit.two) = ((j : ℤ) + 1, -((j : ℤ) + 2)) ∧
      aQ2 (List.replicate (j + 1) Digit.two) = (1, -1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    ext <;> simp [vP1, vP2, vQ2, aP2, aQ2, SpecialCells.parents_twos, texV1Odd, texV2, offsetA] <;> ring

/-- The odd base tile of `2^j` is the near stair `nstairN (2j + 3)`. -/
theorem oddBase_dom (j : ℕ) (O E : PartialOdometer) (h : SurgicalWeak.PaperBaseCond (List.replicate j Digit.two) O E) :
    O.dom = Standard.nstairN (2 * (j : ℤ) + 3) := by
  rcases j with _ | j
  · simpa using (h.1 rfl).1
  · exact (h.2.2 (j + 1) (by omega) rfl).1

/-- Three points of the odd base tile of `2^j`: the junctions of the stems of the top string. -/
theorem mem_O (j : ℕ) (O E : PartialOdometer) (h : SurgicalWeak.PaperBaseCond (List.replicate j Digit.two) O E) :
    ((0 : ℤ), 2 * (j : ℤ)) ∈ O.dom ∧ (2 * (j : ℤ) + 4, 4 * (j : ℤ) + 2) ∈ O.dom ∧
      (2 * (j : ℤ) + 4, 4 * (j : ℤ) + 4) ∈ O.dom := by
  rw [oddBase_dom j O E h]
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [BaseTileProps.mem_nstairN_ab, BaseTileProps.mem_nstairF_ab _ (by omega)] <;> left <;> omega

/-- **The top side of the `-` even L-correction in the double case** `w = 2^{j+1} 3^k`: from the base fact
`DoubleTopBaseInput`, the glued L-corrected odometer and the tile odometer of the even child differ by one constant on the top
string. -/
theorem evenL_top_double (D : JointData) (hS : D.S = paperS) (hDT : DoubleTopBaseInput) (f : Word → JSlice)
    (j k : ℕ) (pre u1 : Word) (hpre : pre = List.replicate (j + 1) Digit.two) (hu1 : u1 = List.replicate j Digit.two)
    (hgood : GoodBelow D f (wk pre k).length) (wo we wao wae tod tev aod aev : PartialOdometer)
    (hW : WeakPart D (below f (wk pre k)) (wk pre k) wo we)
    (hT : TilePart D (below f (wk pre k)) (wk pre k) wo we wao wae tod tev aod aev) (elong : Bool) (κ : ℕ → ℤ)
    (hag : PiecesAgree (LStepAssembly.evenPs D f (wk pre k) false elong) κ) :
    ∃ c : ℤ, ∀ x ∈ placedSites (sideString (hWordOf (wk pre k) true) (vWordOf (wk pre k) true) 0 .hMinus),
      x ∈ (gluedOdo (LStepAssembly.evenPs D f (wk pre k) false elong) κ).dom ∧ x ∈ tev.dom ∧
        (gluedOdo (LStepAssembly.evenPs D f (wk pre k) false elong) κ).val x = tev.val x + c := by
  obtain ⟨hreg, -, -⟩ := twos_facts j
  rw [← hpre, ← hu1] at hreg
  obtain ⟨v1, v2, vq2, a2, aq2⟩ := pre_vecs j
  rw [← hpre] at v1 v2 vq2 a2 aq2
  have hl1 : u1.length < (wk pre k).length := by rw [hpre, hu1]; simp [wk]; omega
  have hb1 : below f (wk pre k) u1 = f u1 := by simp only [below, if_pos hl1]
  have hP := base_cond_slice D hS f u1 (by
    rw [hu1]
    rcases j with _ | j
    · exact Or.inl rfl
    · exact Or.inr (Or.inr fun d hd => List.eq_of_mem_replicate hd)) (hgood u1 hl1).1
  rw [hu1] at hP
  obtain ⟨m0, m1, m2⟩ := mem_O j _ _ hP
  rw [← hu1] at hP m0 m1 m2
  have hPu : SurgicalWeak.PaperBaseCond (List.replicate (j + 1 - 1) Digit.two) (f u1).tOdd (f u1).tEven := by
    rw [Nat.add_sub_cancel, ← hu1]; exact hP
  have hst := evenL_stems_minus D.S (fun u => (below f (wk pre k) u).tOdd) (fun u => (below f (wk pre k) u).tEven)
    (fun u => (below f (wk pre k) u).aOdd) (fun u => (below f (wk pre k) u).aEven) j k elong
  rw [← hpre] at hst
  obtain ⟨hLm, hLe⟩ := hst
  rw [hreg] at hLm
  simp only [regOdo, hb1] at hLm
  have gpiece : ∀ (i : ℕ) (R : PartialOdometer) (s a : Site),
      (LStepAssembly.evenPs D f (wk pre k) false elong)[i]? = some (stdPiece R s a) →
      ∀ y ∈ R.dom, y + s ∈ (gluedOdo (LStepAssembly.evenPs D f (wk pre k) false elong) κ).dom ∧
        (gluedOdo (LStepAssembly.evenPs D f (wk pre k) false elong) κ).val (y + s) = R.val y + dotS a (y + s) + κ i := by
    intro i R s a hi y hy
    have hp : y + s ∈ (stdPiece R s a).placed := Finset.mem_image.2 ⟨y, hy, rfl⟩
    refine ⟨LSidesEven.mem_pieceUnion_of hi hp, ?_⟩
    rw [LSidesEven.glued_val _ κ hag i _ hi _ hp (by simp [stdPiece])]
    simp [JointGlue.pieceVal, stdPiece]
  have henl0 : (0 : Site) ∈ enlOdo.dom := by show (0 : Site) ∈ (tileShape ZTile.oneD).toFinset; decide
  -- the base frame
  have eS : ∀ K : ℕ, nestT pre K K = baseT pre K + ((-1 : ℤ), 2 * ((j + 1 : ℕ) : ℤ) + 3) := by
    intro K; simp only [nestT, baseT, v1, v2, vq2]; ext <;> simp <;> ring
  have eAT : ∀ K : ℕ, affT pre K = affB pre K + (((j + 1 : ℕ) : ℤ) + 1, -(((j + 1 : ℕ) : ℤ) + 2)) := by
    intro K; simp only [affT, affB, a2, aq2]; ext <;> simp <;> ring
  have eE : ∀ K : ℕ, baseT pre K + (vP1 pre + vP2 pre + vP2 pre) + ((1 : ℤ), (1 : ℤ)) =
      baseT pre K + (2 * ((j + 1 : ℕ) : ℤ) + 1, 6 * ((j + 1 : ℕ) : ℤ) + 3) := by
    intro K; rw [v1, v2]; ext <;> simp <;> ring
  have eAE : ∀ K : ℕ, affB pre K + (aP2 pre + aP2 pre) = affB pre K + (2 * ((j + 1 : ℕ) : ℤ), -(2 * ((j + 1 : ℕ) : ℤ) + 2)) := by
    intro K; rw [a2]; ext <;> simp <;> ring
  have eTE : (2 * ((j + 1 : ℕ) : ℤ) + 1, 6 * ((j + 1 : ℕ) : ℤ) + 3) - ((-1 : ℤ), 2 * ((j + 1 : ℕ) : ℤ) + 3) =
      (2 * (j : ℤ) + 4, 4 * (j : ℤ) + 4) := by ext <;> simp <;> ring
  have eJ : ((-1 : ℤ), 4 * ((j + 1 : ℕ) : ℤ) + 1) - ((-1 : ℤ), 2 * ((j + 1 : ℕ) : ℤ) + 3) = ((0 : ℤ), 2 * (j : ℤ)) := by
    ext <;> (simp; try ring)
  have eJ' : ((0 : ℤ), 2 * (j : ℤ)) + ((-1 : ℤ), 2 * ((j + 1 : ℕ) : ℤ) + 3) = ((-1 : ℤ), 4 * ((j + 1 : ℕ) : ℤ) + 1) := by
    ext <;> (simp; try ring)
  have eY : ((0 : ℤ), 2 * (j : ℤ)) + vP1 pre = (2 * (j : ℤ) + 4, 4 * (j : ℤ) + 2) := by
    rw [v1]; ext <;> (simp; try ring)
  rcases k with _ | k
  · -- `w = 2^{j+1}` is a base word: the tile odometer is the base odometer
    have hw0 : wk pre 0 = pre := by simp [wk]
    have hbase : IsBase (wk pre 0) := by
      rw [hw0, hpre]; exact Or.inr (Or.inr fun d hd => List.eq_of_mem_replicate hd)
    obtain ⟨-, -, hWb, -⟩ := hW
    have hBC : SurgicalWeak.PaperBaseCond (List.replicate (j + 1) Digit.two) wo we := by
      have := hWb hbase; rw [hS, hw0, hpre] at this; exact this
    obtain ⟨-, htev, -, -⟩ := (hT.1 hbase)
    obtain ⟨hcov, hsE, c1, c3, hval, -, -⟩ := hDT (j + 1) (by omega) wo we (f u1).tOdd (f u1).tEven hBC hPu
    rw [← hpre] at hcov hsE hval
    have h0 := hLm 0 le_rfl
    have hb0 : baseT pre 0 = 0 := by simp [baseT]
    have hfB : affB pre 0 = 0 := by simp [affB]
    rw [eS 0, eAT 0, hb0, hfB] at h0
    simp only [zero_add] at h0
    have hE := hLe
    rw [eE 0, eAE 0, hb0, hfB] at hE
    simp only [zero_add] at hE
    have gS := gpiece 0 _ _ _ h0
    have gE := gpiece 1 _ _ _ hE
    -- the junction at `s_E`
    have j1 := gS _ (eTE ▸ m2)
    rw [sub_add_cancel] at j1
    have j3 := gE 0 henl0
    rw [zero_add] at j3
    obtain ⟨-, f1, f3⟩ := hval _ hsE
    have e1 := f1 (eTE ▸ m2)
    have e3 := f3 (by rw [sub_self]; exact henl0)
    rw [sub_self] at e3
    refine ⟨κ 0 - c1, fun x hx => ?_⟩
    rw [htev]
    have hx' : x ∈ placedSites (sideString (hWordOf pre true) (vWordOf pre true) 0 .hMinus) := by rwa [hw0] at hx
    obtain ⟨hxE, g1, g3⟩ := hval x hx'
    rcases hcov x hx' with h | h
    · have g := gS _ h
      rw [sub_add_cancel] at g
      exact ⟨g.1, hxE, by rw [g.2, g1 h]; ring⟩
    · have g := gE _ h
      rw [sub_add_cancel] at g
      refine ⟨g.1, hxE, ?_⟩
      rw [g.2, g3 h]
      linarith [j1.2, j3.2]
  · -- `w = 2^{j+1} 3^{k+1}`: the nested copies down to the base tile
    have hnb : ¬ IsBase (wk pre (k + 1)) := by rw [hpre]; exact twos_wk_notBase j k
    have hRt := (hT.2.1 hnb).2.1
    have hnd := nestedT D f j k tev (by rw [← hpre]; exact hgood) (by rw [← hpre]; exact hRt)
    rw [← hpre, ← hu1] at hnd
    obtain ⟨hn, hE0, hcov⟩ := hnd
    have hlp : pre.length < (wk pre (k + 1)).length := by simp [wk]
    have hEb := base_cond_slice D hS f pre (by rw [hpre]; exact Or.inr (Or.inr fun d hd => List.eq_of_mem_replicate hd))
      (hgood pre hlp).1
    rw [hpre] at hEb
    obtain ⟨hcovB, hsE, c1, c3, hval, hJd, hJv⟩ := hDT (j + 1) (by omega) _ _ (f u1).tOdd (f u1).tEven hEb hPu
    rw [← hpre] at hcovB hsE hval hJd hJv
    obtain ⟨bE, hbE⟩ := hE0
    choose! b hb using hn
    have gs : ∀ m ≤ k + 1, ∀ y ∈ (f u1).tOdd.dom, y + nestT pre (k + 1) m ∈
        (gluedOdo (LStepAssembly.evenPs D f (wk pre (k + 1)) false elong) κ).dom ∧
        (gluedOdo (LStepAssembly.evenPs D f (wk pre (k + 1)) false elong) κ).val (y + nestT pre (k + 1) m) =
          (f u1).tOdd.val y + dotS (affT pre (k + 1)) (y + nestT pre (k + 1) m) + κ m :=
      fun m hm => gpiece m _ _ _ (hLm m hm)
    have hE := hLe
    rw [eE (k + 1), eAE (k + 1)] at hE
    have gE := gpiece (k + 2) _ _ _ hE
    have eN : ∀ m : ℕ, ((0 : ℤ), 2 * (j : ℤ)) + nestT pre (k + 1) (m + 1) =
        (2 * (j : ℤ) + 4, 4 * (j : ℤ) + 2) + nestT pre (k + 1) m := by
      intro m; rw [← eY]; simp only [nestT]; ext <;> simp <;> ring
    -- consecutive stems in the copies
    have step : ∀ m < k, κ (m + 1) - b (m + 1) = κ m - b m := by
      intro m hm
      have g1 := gs (m + 1) (by omega) _ m0
      have g2 := gs m (by omega) _ m1
      have t1 := hb (m + 1) (by omega) _ m0
      have t2 := hb m (by omega) _ m1
      rw [← eN m] at g2 t2
      linarith [g1.2, g2.2, t1.2, t2.2]
    have hall : ∀ m ≤ k, κ m - b m = κ 0 - b 0 := by
      intro m hm
      induction m with
      | zero => rfl
      | succ m ih => rw [step m (by omega), ih (by omega)]
    -- the last stem of the copies and the last stem of the base tile
    have lk : κ (k + 1) - c1 - bE + dotS (((j + 1 : ℕ) : ℤ) + 1, -(((j + 1 : ℕ) : ℤ) + 2)) (baseT pre (k + 1)) =
        κ k - b k := by
      have g1 := gs (k + 1) le_rfl _ m0
      have g2 := gs k (by omega) _ m1
      have t2 := hb k le_rfl _ m1
      rw [← eN k] at g2 t2
      have ex : ((0 : ℤ), 2 * (j : ℤ)) + nestT pre (k + 1) (k + 1) =
          ((-1 : ℤ), 4 * ((j + 1 : ℕ) : ℤ) + 1) + baseT pre (k + 1) := by
        rw [eS (k + 1), ← eJ']; abel
      have tE := hbE _ hJd
      have e1 := hJv
      rw [eJ] at e1
      rw [ex] at g1 g2 t2
      rw [eAT (k + 1), dotS_add_l, dotS_add_r (((j + 1 : ℕ) : ℤ) + 1, -(((j + 1 : ℕ) : ℤ) + 2))] at g1
      linarith [g1.2, g2.2, t2.2, tE.2]
    -- the enlarged piece and the last stem of the base tile
    have le : κ (k + 2) - c3 + dotS (2 * ((j + 1 : ℕ) : ℤ), -(2 * ((j + 1 : ℕ) : ℤ) + 2)) (baseT pre (k + 1)) =
        κ (k + 1) - c1 + dotS (((j + 1 : ℕ) : ℤ) + 1, -(((j + 1 : ℕ) : ℤ) + 2)) (baseT pre (k + 1)) := by
      have g1 := gs (k + 1) le_rfl _ (eTE ▸ m2)
      have ex : (2 * ((j + 1 : ℕ) : ℤ) + 1, 6 * ((j + 1 : ℕ) : ℤ) + 3) - ((-1 : ℤ), 2 * ((j + 1 : ℕ) : ℤ) + 3) +
          nestT pre (k + 1) (k + 1) = baseT pre (k + 1) + (2 * ((j + 1 : ℕ) : ℤ) + 1, 6 * ((j + 1 : ℕ) : ℤ) + 3) := by
        rw [eS (k + 1)]; abel
      rw [ex] at g1
      have g3 := gE 0 henl0
      obtain ⟨-, f1, f3⟩ := hval _ hsE
      have e1 := f1 (eTE ▸ m2)
      have e3 := f3 (by rw [sub_self]; exact henl0)
      rw [sub_self] at e3
      rw [eAT (k + 1), dotS_add_l, dotS_add_r (((j + 1 : ℕ) : ℤ) + 1, -(((j + 1 : ℕ) : ℤ) + 2))] at g1
      rw [zero_add, dotS_add_l, dotS_add_r (2 * ((j + 1 : ℕ) : ℤ), -(2 * ((j + 1 : ℕ) : ℤ) + 2))] at g3
      linarith [g1.2, g3.2]
    refine ⟨κ 0 - b 0, fun x hx => ?_⟩
    rcases hcov x hx with ⟨m, hm, hxm⟩ | hxB
    · have g := gs m (by omega) _ hxm
      have t := hb m hm _ hxm
      rw [sub_add_cancel] at g t
      exact ⟨g.1, t.1, by rw [g.2, t.2, ← hall m hm]; ring⟩
    · obtain ⟨hxE, f1, f3⟩ := hval _ hxB
      have tE := hbE _ hxE
      rw [sub_add_cancel] at tE
      refine ⟨?_, tE.1, ?_⟩
      · rcases hcovB _ hxB with h | h
        · have g := gs (k + 1) le_rfl _ h
          rw [show x - baseT pre (k + 1) - ((-1 : ℤ), 2 * ((j + 1 : ℕ) : ℤ) + 3) + nestT pre (k + 1) (k + 1) = x by
            rw [eS (k + 1)]; abel] at g
          exact g.1
        · have g := gE _ h
          rw [show x - baseT pre (k + 1) - (2 * ((j + 1 : ℕ) : ℤ) + 1, 6 * ((j + 1 : ℕ) : ℤ) + 3) +
            (baseT pre (k + 1) + (2 * ((j + 1 : ℕ) : ℤ) + 1, 6 * ((j + 1 : ℕ) : ℤ) + 3)) = x by abel] at g
          exact g.1
      · rw [tE.2]
        rcases hcovB _ hxB with h | h
        · have g := gs (k + 1) le_rfl _ h
          rw [show x - baseT pre (k + 1) - ((-1 : ℤ), 2 * ((j + 1 : ℕ) : ℤ) + 3) + nestT pre (k + 1) (k + 1) = x by
            rw [eS (k + 1)]; abel] at g
          rw [g.2, f1 h, ← hall k le_rfl, ← lk, eAT (k + 1), dotS_add_l,
            dotS_sub_r (((j + 1 : ℕ) : ℤ) + 1, -(((j + 1 : ℕ) : ℤ) + 2))]
          ring
        · have g := gE _ h
          rw [show x - baseT pre (k + 1) - (2 * ((j + 1 : ℕ) : ℤ) + 1, 6 * ((j + 1 : ℕ) : ℤ) + 3) +
            (baseT pre (k + 1) + (2 * ((j + 1 : ℕ) : ℤ) + 1, 6 * ((j + 1 : ℕ) : ℤ) + 3)) = x by abel] at g
          rw [g.2, f3 h, ← hall k le_rfl, ← lk, dotS_add_l,
            dotS_sub_r (2 * ((j + 1 : ℕ) : ℤ), -(2 * ((j + 1 : ℕ) : ℤ) + 2))]
          linarith [le]

/-- **The top side of the `-` even L-correction in the double case**, both parts of `LSidesAgree` for the top string, with the
base fact `DoubleTopBase.double_top_base`. -/
theorem evenL_top_side_double (D : JointData) (hS : D.S = paperS) (f : Word → JSlice)
    (j k : ℕ) (pre u1 : Word) (hpre : pre = List.replicate (j + 1) Digit.two) (hu1 : u1 = List.replicate j Digit.two)
    (hgood : GoodBelow D f (wk pre k).length) (wo we wao wae tod tev aod aev : PartialOdometer)
    (hW : WeakPart D (below f (wk pre k)) (wk pre k) wo we)
    (hT : TilePart D (below f (wk pre k)) (wk pre k) wo we wao wae tod tev aod aev) (elong : Bool) (κ : ℕ → ℤ)
    (hag : PiecesAgree (LStepAssembly.evenPs D f (wk pre k) false elong) κ) :
    RespectsTiles (sideOrient .hMinus).1 (sideOrient .hMinus).2
        (sideString (hWordOf (wk pre k) true) (vWordOf (wk pre k) true) 0 .hMinus)
        (gluedOdo (LStepAssembly.evenPs D f (wk pre k) false elong) κ).val ∧
      ∃ c : ℤ, ∀ x ∈ placedSites (sideString (hWordOf (wk pre k) true) (vWordOf (wk pre k) true) 0 .hMinus),
        x ∈ (gluedOdo (LStepAssembly.evenPs D f (wk pre k) false elong) κ).dom ∧ x ∈ tev.dom ∧
          (gluedOdo (LStepAssembly.evenPs D f (wk pre k) false elong) κ).val x = tev.val x + c := by
  obtain ⟨c, hc⟩ := evenL_top_double D hS DoubleTopBase.double_top_base f j k pre u1 hpre hu1 hgood wo we wao wae tod tev
    aod aev hW hT elong κ hag
  obtain ⟨-, -, -, -, -, hR, -⟩ := hT
  exact ⟨LSidesEven.respectsTiles_add_const _ _ _ _ _ c hR.2.2.1 (fun x hx => (hc x hx).2.2), c, hc⟩

end FLatticePaper.Tiles.LSidesEvenTopD
