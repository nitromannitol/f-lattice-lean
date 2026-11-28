import FLatticePaper.Tiles.TileCompatInputs
import FLatticePaper.Tiles.BaseTileProps
import FLatticePaper.Tiles.WeakStepPaper

/-! The seventh piece against the six standard pieces at the first non-base word. -/

namespace FLatticePaper.Tiles.AltParentBase

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard SurgicalWeak SurgicalAlt JointFamily JointInduction JointGlue TileCompatInputs

private def tile (odd : Bool) := if odd then nstairN 3 else stairF 3

private def val (odd : Bool) (z : Site) : ℤ :=
  if odd then paperNearStairValue 3 (z + (0,1)) else paperStairValue 3 z

private def inAlt (odd : Bool) (z : Site) : Prop :=
  let x := z.1
  let y := if odd then z.2 + 1 else z.2
  if odd then
    (((-1 ≤ x ∧ x ≤ 0 ∧ y = 6) ∨ (3 ≤ x ∧ x ≤ 4 ∧ y = 1) ∨ (y-x = 2 ∧ 0 < x ∧ x < 3)) ∨
      ((x = -1 ∧ 4 ≤ y ∧ y ≤ 6) ∨ (x = 4 ∧ 1 ≤ y ∧ y ≤ 3))) ∨
      (0 ≤ x ∧ x ≤ 3 ∧ 1 ≤ y ∧ y ≤ 6 ∧ -1 ≤ y-x ∧ y-x ≤ 5)
  else
    (((x = -2 ∧ -1 ≤ y ∧ y ≤ 0) ∨ (x = 3 ∧ 3 ≤ y ∧ y ≤ 4)) ∨ (x+y = 2 ∧ 0 < y ∧ y < 3)) ∨
      ((-2 ≤ x ∧ x ≤ 0 ∧ y = -1) ∨ (1 ≤ x ∧ x ≤ 3 ∧ y = 4)) ∨
      (-2 ≤ x ∧ x ≤ 3 ∧ 0 ≤ y ∧ y ≤ 3 ∧ -1 ≤ x+y ∧ x+y ≤ 5)

private instance (odd : Bool) (z : Site) : Decidable (inAlt odd z) := by
  unfold inAlt
  dsimp only
  split <;> infer_instance

private def altVal (odd : Bool) (z : Site) : ℤ :=
  let x := z.1
  let y := if odd then z.2 + 1 else z.2
  if odd then
    -((y-x)^2 / 4) + min (3-y-1) 0 + min (5-y) 0 + max (y-x-3+1) 0 +
      if (-1 ≤ x ∧ x ≤ 0 ∧ y = 6) ∨ (3 ≤ x ∧ x ≤ 4 ∧ y = 1) ∨ (y-x = 2 ∧ 0 < x ∧ x < 3) then 1 else 0
  else
    -(y*(y+1)/2) + min 0 (2-x) + min 0 (1+x) + max (x+y-2) 0 +
      if ((x = -2 ∧ -1 ≤ y ∧ y ≤ 0) ∨ (x = 3 ∧ 3 ≤ y ∧ y ≤ 4)) ∨ (x+y = 2 ∧ 0 < y ∧ y < 3) then 1 else 0

private def isStd (T : PartialOdometer) (o : Bool) : Prop :=
  T.dom = tile o ∧ ∀ z ∈ T.dom, T.val z = val o z

private def isAlt (H : PartialOdometer) (o : Bool) : Prop :=
  ∀ z ∈ H.dom, inAlt o z ∧ H.val z = altVal o z

private theorem descriptions (P Q H J : PartialOdometer) (h : PaperBaseCond [] P Q) (ha : PaperAltBaseCond [] H J) :
    isStd P true ∧ isStd Q false ∧ isAlt H true ∧ isAlt J false := by
  obtain ⟨hp, hP, hq, hQ⟩ := h.1 rfl
  obtain ⟨hh, hH, hj, hJ⟩ := ha.1 rfl
  refine ⟨⟨hp,hP⟩, ⟨hq,hQ⟩, ?_, ?_⟩
  · rintro ⟨x,y⟩ hz
    have hm := (hh _).1 hz
    have ez : (x,y) + ((0,1) : Site) = (x,y+1) := by ext <;> simp
    rw [ez] at hm
    rw [BaseTileProps.mem_nsAlt] at hm
    have hv := hH _ hz
    rw [ez] at hv
    rw [BaseTileProps.pnsA] at hv
    exact ⟨by simpa [inAlt, or_assoc] using hm, by
      simp [altVal] at hv ⊢
      split_ifs at * <;> simp_all⟩
  · rintro ⟨x,y⟩ hz
    have hm := (hj _).1 hz
    rw [BaseTileProps.mem_stAlt] at hm
    have hv := hJ _ hz
    rw [BaseTileProps.pstA] at hv
    exact ⟨by simpa [inAlt] using hm, by
      simp [altVal] at hv ⊢
      split_ifs at * <;> simp_all⟩

private def row (h o : Bool) (a s b t : Site) (K : ℤ) : Prop :=
  ∀ x ∈ tile o, inAlt h (x+b-a) → altVal h (x+b-a) + dotS s (x+b) - (val o x + dotS t (x+b)) = K

private instance (h o : Bool) (a s b t : Site) (K : ℤ) : Decidable (row h o a s b t K) := by
  unfold row
  infer_instance

private theorem pair (ps : List Piece) (i j : ℕ) (H T : PartialOdometer) (h o : Bool) (a s b t : Site) (K : ℤ)
    (hH : isAlt H h) (hT : isStd T o)
    (hi : ps[i]? = some (stdPiece H a s)) (hj : ps[j]? = some (stdPiece T b t))
    (cert : row h o a s b t K) : PairCompat ps i j := by
  intro p q ep eq
  rw [hi, Option.some.injEq] at ep
  rw [hj, Option.some.injEq] at eq
  subst p
  subst q
  refine ⟨K, fun x hp hq _ _ => ?_⟩
  have toDom (O : PartialOdometer) (b t : Site) (hz : x ∈ (stdPiece O b t).placed) : x-b ∈ O.dom := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    simpa [stdPiece] using hy
  obtain ⟨hm, hv⟩ := hH _ (toDom H a s hp)
  have hx := toDom T b t hq
  have v := hT.2 _ hx
  rw [hT.1] at hx
  have hc := cert (x-b) hx (by simpa using hm)
  simp only [sub_add_cancel] at hc
  change H.val (x-a) + dotS s x - (T.val (x-b) + dotS t x) = K
  rwa [hv, v]

/-- The two comparisons of entry six with any standard entry at the word consisting of one. -/
theorem one (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = PaperAltBaseCond)
    (f : Word → JSlice) (hg : GoodBelow D f 1) (j : ℕ) (hj : j < 6) :
    PairCompat (tileAltOddPieces D.S (fun u => (below f [.one] u).tOdd) (fun u => (below f [.one] u).tEven)
        (fun u => (below f [.one] u).aOdd) (fun u => (below f [.one] u).aEven) (fun u => (below f [.one] u).lOdd) [.one]) 6 j ∧
      PairCompat (tileAltEvenPieces D.S (fun u => (below f [.one] u).tOdd) (fun u => (below f [.one] u).tEven)
        (fun u => (below f [.one] u).aOdd) (fun u => (below f [.one] u).aEven) (fun u => (below f [.one] u).lEven) [.one]) 6 j := by
  have H := (hg [] (by decide)).1
  obtain ⟨hO, hE, hAO, hAE⟩ := H.2.2.1.1 (Or.inl rfl)
  have p := H.1.2.2.1 (Or.inl rfl)
  have a := H.2.1.2.2.1 (Or.inl rfl)
  rw [hS] at p
  rw [hA] at a
  have pp : PaperBaseCond [] (f []).tOdd (f []).tEven := by rwa [hO,hE]
  have aa : PaperAltBaseCond [] (f []).aOdd (f []).aEven := by rwa [hAO,hAE]
  obtain ⟨P,Q,AH,AJ⟩ := descriptions _ _ _ _ pp aa
  constructor
  · obtain _ | _ | _ | _ | _ | _ | j := j
    rotate_left 6
    · omega
    · exact pair _ _ _ _ _ _ _ (0, 4) (1,-2) (0, 0) (0, 0) (-2) AJ P rfl rfl (by decide)
    · exact pair _ _ _ _ _ _ _ (0, 4) (1,-2) (-4, 2) (1, -2) (0) AJ P rfl rfl (by decide)
    · exact pair _ _ _ _ _ _ _ (0, 4) (1,-2) (1, 5) (1, -3) (5) AJ P rfl rfl (by decide)
    · exact pair _ _ _ _ _ _ _ (0, 4) (1,-2) (-3, 7) (2, -5) (16) AJ P rfl rfl (by decide)
    · exact pair _ _ _ _ _ _ _ (0, 4) (1,-2) (4, 2) (0, 0) (-2) AJ Q rfl rfl (by decide)
    · exact pair _ _ _ _ _ _ _ (0, 4) (1,-2) (-5, 5) (2, -4) (10) AJ Q rfl rfl (by decide)
  · obtain _ | _ | _ | _ | _ | _ | j := j
    rotate_left 6
    · omega
    · exact pair _ _ _ _ _ _ _ (2, 4) (1,-2) (4, 2) (0, 0) (-2) AH Q rfl rfl (by decide)
    · exact pair _ _ _ _ _ _ _ (2, 4) (1,-2) (6, 6) (1, -2) (-1) AH Q rfl rfl (by decide)
    · exact pair _ _ _ _ _ _ _ (2, 4) (1,-2) (-1, 3) (1, -2) (0) AH Q rfl rfl (by decide)
    · exact pair _ _ _ _ _ _ _ (2, 4) (1,-2) (1, 7) (2, -4) (8) AH Q rfl rfl (by decide)
    · exact pair _ _ _ _ _ _ _ (2, 4) (1,-2) (0, 0) (0, 0) (-2) AH P rfl rfl (by decide)
    · exact pair _ _ _ _ _ _ _ (2, 4) (1,-2) (3, 9) (2, -5) (16) AH P rfl rfl (by decide)

/-- At a type-two odd alternate child the seventh entry is absent. -/
theorem odd_after_two (S : WeakData) (P Q H J : Word → PartialOdometer)
    (L : Word → Bool → Bool → PartialOdometer) (w : Word) (hw : w.getLast? = some .two) (j : ℕ) :
    PairCompat (tileAltOddPieces S P Q H J L w) 6 j := by
  intro p q hp
  simp [tileAltOddPieces, altTypeOf, hw, altQ1Coeff] at hp

/-- At a type-three even alternate child the seventh entry is absent. -/
theorem even_after_three (S : WeakData) (P Q H J : Word → PartialOdometer)
    (L : Word → Bool → Bool → PartialOdometer) (w : Word) (hw : w.getLast? = some .three) (j : ℕ) :
    PairCompat (tileAltEvenPieces S P Q H J L w) 6 j := by
  intro p q hp
  cases he : W1Odd w <;> simp [tileAltEvenPieces, altTypeOf, hw, altP1Coeff, he] at hp

end FLatticePaper.Tiles.AltParentBase
