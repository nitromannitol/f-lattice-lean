import FLatticePaper.Tiles.JointInduction
import FLatticePaper.Tiles.Gluing

/-! # Gluing a decomposition (the existence part of the tile and L steps)

A tile odometer and an L-corrected odometer are their decompositions (`RespectsPieces`): on each piece they are the placed
odometer of the piece plus its affine factor and a constant. In the proofs of `lemma:l_correct_existence` and
`lemma:tile-odometer-existence` such an odometer exists once there are constants for the pieces making every two overlapping
pieces equal on their intersection (outside the exceptional points of the first head of a base ancestor). This file proves that
reduction (`respectsPieces_glued`), and derives the constants from `lemma:pairwise_compatibility`
(`Gluing.exists_compatible_iff_walkSum_eq_zero`): local compatibility of the pieces and the offset constants summing to zero around
every closed path of the overlap graph (`agree_of_compatible`). Every point of an L-correction lies in a piece where it is not
exceptional (`oddLPieces_covered`, `evenLPieces_covered`): the exceptional points lie in the last stem. -/

namespace FLatticePaper.Tiles.JointGlue

open FLatticePaper.Farey
open FLatticePaper.Tiles
open FLatticePaper.Tiles.SurgicalWeak
open FLatticePaper.Tiles.JointFamily

/-- The value of the placed piece at `x`: the piece's odometer at `x - off` plus the affine factor. -/
def pieceVal (p : Piece) (x : Site) : ℤ := p.odo.val (x - p.off) + dotS p.aff x

theorem mem_pieceUnion {ps : List Piece} {x : Site} : x ∈ pieceUnion ps ↔ ∃ p ∈ ps, x ∈ p.placed := by
  induction ps with
  | nil => simp [pieceUnion]
  | cons p ps ih =>
    have h : pieceUnion (p :: ps) = p.placed ∪ pieceUnion ps := rfl
    rw [h, Finset.mem_union, ih]
    simp

/-- The pieces, with constants `κ`, agree on every intersection outside the exceptional points. -/
def PiecesAgree (ps : List Piece) (κ : ℕ → ℤ) : Prop :=
  ∀ (i j : ℕ) (p q : Piece), ps[i]? = some p → ps[j]? = some q →
    ∀ x ∈ p.placed, x ∈ q.placed → x ∉ p.exc → x ∉ q.exc → pieceVal p x + κ i = pieceVal q x + κ j

/-- Every point of the decomposition lies in a piece where it is not exceptional. -/
def PiecesCovered (ps : List Piece) : Prop :=
  ∀ x ∈ pieceUnion ps, ∃ (i : ℕ) (p : Piece), ps[i]? = some p ∧ x ∈ p.placed ∧ x ∉ p.exc

open Classical in
/-- The glued odometer: on the union of the pieces, the value of a covering piece plus its constant. -/
noncomputable def gluedOdo (ps : List Piece) (κ : ℕ → ℤ) : PartialOdometer :=
  ⟨pieceUnion ps, fun x =>
    if h : ∃ (i : ℕ) (p : Piece), ps[i]? = some p ∧ x ∈ p.placed ∧ x ∉ p.exc then
      pieceVal (Classical.choose (Classical.choose_spec h)) x + κ (Classical.choose h)
    else 0⟩

/-- A decomposition whose pieces agree (with constants) glues to an odometer respecting it. -/
theorem respectsPieces_glued (ps : List Piece) (κ : ℕ → ℤ) (hcov : PiecesCovered ps) (hag : PiecesAgree ps κ) :
    RespectsPieces (gluedOdo ps κ) ps := by
  refine ⟨rfl, fun p hp => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i : ℕ, ps[i]? = some p := List.mem_iff_getElem?.mp hp
  refine ⟨κ i, fun x hx hxe => ?_⟩
  have h := hcov x (mem_pieceUnion.mpr ⟨p, hp, hx⟩)
  obtain ⟨hq, hxq, hxqe⟩ := Classical.choose_spec (Classical.choose_spec h)
  have key := hag _ i _ p hq hi x hxq hx hxqe hxe
  have hv : (gluedOdo ps κ).val x =
      pieceVal (Classical.choose (Classical.choose_spec h)) x + κ (Classical.choose h) := by
    simp only [gluedOdo]
    rw [dif_pos h]
  rw [hv, key]
  rfl

/-- Conversely, an odometer respecting the decomposition gives constants with which the pieces agree. -/
theorem agree_of_respectsPieces (o : PartialOdometer) (ps : List Piece) (h : RespectsPieces o ps) :
    ∃ κ : ℕ → ℤ, PiecesAgree ps κ := by
  choose b hb using h.2
  refine ⟨fun i => if hi : i < ps.length then b ps[i] (List.getElem_mem hi) else 0, ?_⟩
  intro i j p q hp hq x hxp hxq hxpe hxqe
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hp
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hq
  simp only [dif_pos hi, dif_pos hj]
  have h1 := hb ps[i] (List.getElem_mem hi) x hxp hxpe
  have h2 := hb ps[j] (List.getElem_mem hj) x hxq hxqe
  unfold pieceVal
  linarith

/-! ### The constants from `lemma:pairwise_compatibility` -/

/-- The points of the decomposition. -/
abbrev UnionPt (ps : List Piece) := {x : Site // x ∈ pieceUnion ps}

/-- The non-exceptional part of the piece `i`, as a set of points of the decomposition. -/
def goodPart (ps : List Piece) (i : Fin ps.length) : Set (UnionPt ps) :=
  {x | x.1 ∈ (ps.get i).placed ∧ x.1 ∉ (ps.get i).exc}

/-- `lemma:pairwise_compatibility` for a decomposition: if the overlap graph of the non-exceptional parts is connected, the
difference of two overlapping pieces is a constant `off i j` there (local compatibility), and these constants sum to zero along every
closed walk of the overlap graph, then there are constants with which the pieces agree. -/
theorem agree_of_compatible (ps : List Piece) (hcov : PiecesCovered ps)
    (off : Fin ps.length → Fin ps.length → ℤ)
    (hconn : (overlapGraph (goodPart ps)).Connected)
    (hoff : ∀ i j, ∀ x ∈ goodPart ps i ∩ goodPart ps j,
      pieceVal (ps.get i) x.1 - pieceVal (ps.get j) x.1 = off i j)
    (hzero : ∀ (i : Fin ps.length) (walk : (overlapGraph (goodPart ps)).Walk i i), walkSum off walk = 0) :
    ∃ κ : ℕ → ℤ, PiecesAgree ps κ := by
  have hcover : ∀ x : UnionPt ps, ∃ i, x ∈ goodPart ps i := by
    intro x
    obtain ⟨i, p, hi, hx, hxe⟩ := hcov x.1 x.2
    have hlt : i < ps.length := (List.getElem?_eq_some_iff.mp hi).1
    have hget : ps.get ⟨i, hlt⟩ = p := by
      have := (List.getElem?_eq_some_iff.mp hi).2
      simpa using this
    exact ⟨⟨i, hlt⟩, by simp only [goodPart, Set.mem_setOf_eq, hget]; exact ⟨hx, hxe⟩⟩
  obtain ⟨f, hf⟩ := (exists_compatible_iff_walkSum_eq_zero (goodPart ps)
    (fun i (x : UnionPt ps) => pieceVal (ps.get i) x.1) off hcover hconn hoff).mpr hzero
  choose c hc using hf
  refine ⟨fun i => if hi : i < ps.length then c ⟨i, hi⟩ else 0, ?_⟩
  intro i j p q hp hq x hxp hxq hxpe hxqe
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hp
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hq
  have hxu : x ∈ pieceUnion ps := mem_pieceUnion.mpr ⟨ps[i], List.getElem_mem hi, hxp⟩
  have h1 : f ⟨x, hxu⟩ - pieceVal ps[i] x = c ⟨i, hi⟩ := by
    have := hc ⟨i, hi⟩ ⟨x, hxu⟩ (by simp only [goodPart, Set.mem_setOf_eq, List.get_eq_getElem]; exact ⟨hxp, hxpe⟩)
    simpa using this
  have h2 : f ⟨x, hxu⟩ - pieceVal ps[j] x = c ⟨j, hj⟩ := by
    have := hc ⟨j, hj⟩ ⟨x, hxu⟩ (by simp only [goodPart, Set.mem_setOf_eq, List.get_eq_getElem]; exact ⟨hxq, hxqe⟩)
    simpa using this
  simp only [dif_pos hi, dif_pos hj]
  linarith

/-! ### Covering: the exceptional points lie in a piece without exceptions -/

/-- A decomposition is covered when one of its pieces has no exceptional point and contains the exceptional points of all. -/
theorem covered_of_exc_subset (ps : List Piece) (s : Piece) (hs : s ∈ ps) (hse : s.exc = ∅)
    (hsub : ∀ p ∈ ps, ∀ x ∈ p.exc, x ∈ s.placed) : PiecesCovered ps := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := mem_pieceUnion.mp hx
  by_cases hxe : x ∈ p.exc
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hs
    exact ⟨j, s, hj, hsub p hp x hxe, by rw [hse]; simp⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
    exact ⟨i, p, hi, hxp, hxe⟩

/-- A decomposition without exceptional points is covered. -/
theorem covered_of_no_exc (ps : List Piece) (h : ∀ p ∈ ps, p.exc = ∅) : PiecesCovered ps := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := mem_pieceUnion.mp hx
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  exact ⟨i, p, hi, hxp, by rw [h p hp]; simp⟩

theorem tileOddPieces_covered (S : WeakData) (pOdd pEven : Word → PartialOdometer)
    (lEven : Word → Bool → Bool → PartialOdometer) (w : Word) : PiecesCovered (tileOddPieces S pOdd pEven lEven w) := by
  refine covered_of_no_exc _ (fun p hp => ?_)
  simp only [tileOddPieces, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem tileEvenPieces_covered (S : WeakData) (pOdd pEven : Word → PartialOdometer)
    (lOdd : Word → Bool → Bool → PartialOdometer) (w : Word) : PiecesCovered (tileEvenPieces S pOdd pEven lOdd w) := by
  refine covered_of_no_exc _ (fun p hp => ?_)
  simp only [tileEvenPieces, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem oddLPieces_covered (S : WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer) (w : Word) (plus elong : Bool) :
    PiecesCovered (oddLPieces S pOdd pEven aOdd aEven w plus elong) := by
  refine covered_of_exc_subset _ (stdPiece (regOdo S pOdd pEven (regsAt (stripTrailing Digit.two w)).2 false)
      (oddLInitOff w plus + altOff (stripTrailing Digit.two w)
        (((trailingCount Digit.two w : ℕ) : ℤ) • (oddKCoeff (W1Odd w) plus).1))
      (oddLInitAff w plus + altAff (stripTrailing Digit.two w)
        (((trailingCount Digit.two w : ℕ) : ℤ) • (oddKCoeff (W1Odd w) plus).1))) ?_ rfl ?_
  · simp only [oddLPieces]
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_map_of_mem (List.mem_range.mpr (Nat.lt_succ_self _))))
  · intro p hp x hx
    simp only [oddLPieces] at hp
    rcases List.mem_append.mp hp with h | h
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨j, -, rfl⟩ := List.mem_map.mp h
        simp [stdPiece] at hx
      · rw [List.mem_singleton] at h
        subst h
        simp [stdPiece] at hx
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp h
      simp only at hx
      split_ifs at hx with hc
      · exact hx.2
      · simp at hx

theorem evenLPieces_covered (S : WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer) (w : Word)
    (plus elong : Bool) : PiecesCovered (evenLPieces S pOdd pEven aOdd aEven w plus elong) := by
  refine covered_of_exc_subset _ (stdPiece (regOdo S pOdd pEven (regsAt (stripTrailing Digit.three w)).1 true)
      (evenLInitOff w plus + altOff (stripTrailing Digit.three w)
        (((trailingCount Digit.three w : ℕ) : ℤ) •
          (evenKCoeff (W1Odd w) plus (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))).1))
      (evenLInitAff w plus + altAff (stripTrailing Digit.three w)
        (((trailingCount Digit.three w : ℕ) : ℤ) •
          (evenKCoeff (W1Odd w) plus (decide ((stripTrailing Digit.three w).getLast? = some Digit.two))).1))) ?_ rfl ?_
  · simp only [evenLPieces]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map_of_mem (List.mem_range.mpr (Nat.lt_succ_self _)))))
  · intro p hp x hx
    simp only [evenLPieces] at hp
    rcases List.mem_append.mp hp with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · obtain ⟨j, -, rfl⟩ := List.mem_map.mp h
          simp [stdPiece] at hx
        · split_ifs at h with hc
          · simp at h
          · rw [List.mem_singleton] at h
            subst h
            simp [stdPiece] at hx
      · split_ifs at h with hc
        · rw [List.mem_singleton] at h
          subst h
          simp [stdPiece] at hx
        · simp at h
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp h
      simp only at hx
      split_ifs at hx with hc
      · exact hx.2
      · simp at hx

end FLatticePaper.Tiles.JointGlue
