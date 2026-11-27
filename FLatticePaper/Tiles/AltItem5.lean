import FLatticePaper.Tiles.AltPieces
import FLatticePaper.Tiles.MixedFromCells
import FLatticePaper.Tiles.MixedOverlapStrings
import FLatticePaper.Tiles.TilingGreen

/-! # Item (5) of `lemma:alternate_tile_properties`: the interfaces between copies of different parents

Surgical edition 3243bef, `lemma:alternate_tile_properties` (5) and its proof (Step 2): when `T̂(n/d)` has an alternate
decomposition, the shared boundary between neighbouring standard subtiles of different parents is part of, or is, a stacked
horizontal or vertical zero-one boundary string.

The proof of the text: each pair of a copy `J` of `T(p₁)` and a copy `K` of `T(q₁)` among the standard subtiles of the alternate
decomposition either does not meet, or sits at the relative offset `c(J) - c(K)` of a pair of copies of different parents in a
standard decomposition, where item (d) of `lemma:standard_tile_properties` applies. Here:

* `pairs_odd`, `pairs_even`: for both children and both orientations, each pair `(J, K)` either has no common point, or
  `c(J) - c(K) = a' - b'` for a copy of `T(p₁)` at `a'` and a copy of `T(q₁)` at `b'` in the standard decomposition of the
  STANDARD ODD child of the same word (`MixedPieces.pOffsetsOdd`, `qOffsetsOdd`). The pairs that do not meet are separated by
  one of the coordinates `x`, `y`, `x + y`, `x - y`, through the box of the closed sets of the parents (`AltPieces.inH_box`).
  The text separates the same pairs by coordinates and by the monotone comparison of Step 3 of
  `lemma:standard_tile_properties`; for `n/d = p₀` it uses the rotation, here the odd child is treated directly. -/

namespace FLatticePaper.Tiles.AltItem5

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile)
open FLatticePaper.Tiles.SurgicalDict (altShifts)
open FLatticePaper.Tiles.SurgicalAlt (coeffOff altP0Coeff altQ0Coeff)
open FLatticePaper.Tiles.AltRotStep (offP0 offQ0 shP shQ)
open FLatticePaper.Tiles.AltPieces
open FLatticePaper.Tiles.SiteInduction (InH)

/-- The box of the two parents at a common point of a copy of each, in coordinates. -/
theorem boxes (p q : Fraction) (hp : 0 < p.num ∧ p.num < p.den) (hq : 0 < q.num ∧ q.num < q.den)
    (hmp : SiteInduction.muOf p = 2) (hmq : SiteInduction.muOf q = 1) (a b z : Site)
    (h1 : InH p (z - a)) (h2 : InH q (z - b)) :
    p.num - p.den ≤ z.1 - a.1 ∧ z.1 - a.1 ≤ 2 * p.den + 1 ∧
      -1 ≤ z.2 - a.2 ∧ z.2 - a.2 ≤ 2 * p.num + p.num + p.den ∧
      -1 ≤ z.1 - a.1 + (z.2 - a.2) ∧ z.1 - a.1 + (z.2 - a.2) ≤ 2 * (p.den + p.num) + 2 * p.num + 1 ∧
      -2 * p.den ≤ z.1 - a.1 - (z.2 - a.2) ∧ z.1 - a.1 - (z.2 - a.2) ≤ 2 * (p.den - p.num) + 2 ∧
    q.num - q.den ≤ z.1 - b.1 ∧ z.1 - b.1 ≤ q.den + 1 ∧
      -1 ≤ z.2 - b.2 ∧ z.2 - b.2 ≤ q.num + q.num + q.den ∧
      -1 ≤ z.1 - b.1 + (z.2 - b.2) ∧ z.1 - b.1 + (z.2 - b.2) ≤ (q.den + q.num) + 2 * q.num + 1 ∧
      -2 * q.den ≤ z.1 - b.1 - (z.2 - b.2) ∧ z.1 - b.1 - (z.2 - b.2) ≤ (q.den - q.num) + 2 := by
  have b1 := inH_box p hp.1 hp.2 _ h1
  have b2 := inH_box q hq.1 hq.2 _ h2
  rw [hmp] at b1
  rw [hmq] at b2
  simp only [Prod.fst_sub, Prod.snd_sub, one_mul] at b1 b2
  exact ⟨b1.1, b1.2.1, b1.2.2.1, b1.2.2.2.1, b1.2.2.2.2.1, b1.2.2.2.2.2.1, b1.2.2.2.2.2.2.1, b1.2.2.2.2.2.2.2,
    b2.1, b2.2.1, b2.2.2.1, b2.2.2.2.1, b2.2.2.2.2.1, b2.2.2.2.2.2.1, b2.2.2.2.2.2.2.1, b2.2.2.2.2.2.2.2⟩

/-! ### The pairs, one by one -/

theorem odd_false_0_0 (p q : Fraction) :
    ∃ a' ∈ MixedPieces.pOffsetsOdd false p q, ∃ b' ∈ MixedPieces.qOffsetsOdd false p q,
      (offP0 false p q .dsP1Plus) - (offP0 false p q .q1Plus) = a' - b' := by
  refine ⟨(MixedPieces.pOffsetsOdd false p q)[0]'(by simp [MixedPieces.pOffsetsOdd]),
    List.getElem_mem _, (MixedPieces.qOffsetsOdd false p q)[1]'(by simp [MixedPieces.qOffsetsOdd]),
    List.getElem_mem _, ?_⟩
  simp only [MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, offP0, coeffOff, altP0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true, List.getElem_cons_zero,
    List.getElem_cons_succ]
  ext <;> simp

theorem odd_false_0_1 (p q : Fraction) (hp : 0 < p.num ∧ p.num < p.den) (hq : 0 < q.num ∧ q.num < q.den)
    (hmp : SiteInduction.muOf p = 2) (hmq : SiteInduction.muOf q = 1) (z : Site) :
    ¬ (InH p (z - (offP0 false p q .dsP1Plus)) ∧ InH q (z - (offP0 false p q .q1Minus))) := by
  rintro ⟨h1, h2⟩
  have hb := boxes p q hp hq hmp hmq _ _ z h1 h2
  simp only [offP0, coeffOff, altP0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true] at hb
  omega

theorem odd_false_1_0 (p q : Fraction) (hp : 0 < p.num ∧ p.num < p.den) (hq : 0 < q.num ∧ q.num < q.den)
    (hmp : SiteInduction.muOf p = 2) (hmq : SiteInduction.muOf q = 1) (z : Site) :
    ¬ (InH p (z - (shP false p q + offP0 false p q .dsP1Plus)) ∧ InH q (z - (offP0 false p q .q1Plus))) := by
  rintro ⟨h1, h2⟩
  have hb := boxes p q hp hq hmp hmq _ _ z h1 h2
  simp only [offP0, shP, coeffOff, altP0Coeff, altShifts, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true, Prod.fst_add, Prod.snd_add] at hb
  omega

theorem odd_false_1_1 (p q : Fraction) :
    ∃ a' ∈ MixedPieces.pOffsetsOdd false p q, ∃ b' ∈ MixedPieces.qOffsetsOdd false p q,
      (shP false p q + offP0 false p q .dsP1Plus) - (offP0 false p q .q1Minus) = a' - b' := by
  refine ⟨(MixedPieces.pOffsetsOdd false p q)[0]'(by simp [MixedPieces.pOffsetsOdd]),
    List.getElem_mem _, (MixedPieces.qOffsetsOdd false p q)[3]'(by simp [MixedPieces.qOffsetsOdd]),
    List.getElem_mem _, ?_⟩
  simp only [MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, offP0, shP, coeffOff, altP0Coeff, altShifts, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true, List.getElem_cons_zero,
    List.getElem_cons_succ]
  ext <;> simp <;> ring

theorem odd_false_2_0 (p q : Fraction) :
    ∃ a' ∈ MixedPieces.pOffsetsOdd false p q, ∃ b' ∈ MixedPieces.qOffsetsOdd false p q,
      (offP0 false p q .dsP1Minus) - (offP0 false p q .q1Plus) = a' - b' := by
  refine ⟨(MixedPieces.pOffsetsOdd false p q)[1]'(by simp [MixedPieces.pOffsetsOdd]),
    List.getElem_mem _, (MixedPieces.qOffsetsOdd false p q)[0]'(by simp [MixedPieces.qOffsetsOdd]),
    List.getElem_mem _, ?_⟩
  simp only [MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, offP0, coeffOff, altP0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true, List.getElem_cons_zero,
    List.getElem_cons_succ]
  ext <;> simp

theorem odd_false_2_1 (p q : Fraction) (hp : 0 < p.num ∧ p.num < p.den) (hq : 0 < q.num ∧ q.num < q.den)
    (hmp : SiteInduction.muOf p = 2) (hmq : SiteInduction.muOf q = 1) (z : Site) :
    ¬ (InH p (z - (offP0 false p q .dsP1Minus)) ∧ InH q (z - (offP0 false p q .q1Minus))) := by
  rintro ⟨h1, h2⟩
  have hb := boxes p q hp hq hmp hmq _ _ z h1 h2
  simp only [offP0, coeffOff, altP0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true] at hb
  omega

theorem odd_false_3_0 (p q : Fraction) (hp : 0 < p.num ∧ p.num < p.den) (hq : 0 < q.num ∧ q.num < q.den)
    (hmp : SiteInduction.muOf p = 2) (hmq : SiteInduction.muOf q = 1) (z : Site) :
    ¬ (InH p (z - (shP false p q + offP0 false p q .dsP1Minus)) ∧ InH q (z - (offP0 false p q .q1Plus))) := by
  rintro ⟨h1, h2⟩
  have hb := boxes p q hp hq hmp hmq _ _ z h1 h2
  simp only [offP0, shP, coeffOff, altP0Coeff, altShifts, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true, Prod.fst_add, Prod.snd_add] at hb
  omega

theorem odd_false_3_1 (p q : Fraction) :
    ∃ a' ∈ MixedPieces.pOffsetsOdd false p q, ∃ b' ∈ MixedPieces.qOffsetsOdd false p q,
      (shP false p q + offP0 false p q .dsP1Minus) - (offP0 false p q .q1Minus) = a' - b' := by
  refine ⟨(MixedPieces.pOffsetsOdd false p q)[1]'(by simp [MixedPieces.pOffsetsOdd]),
    List.getElem_mem _, (MixedPieces.qOffsetsOdd false p q)[2]'(by simp [MixedPieces.qOffsetsOdd]),
    List.getElem_mem _, ?_⟩
  simp only [MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, offP0, shP, coeffOff, altP0Coeff, altShifts, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true, List.getElem_cons_zero,
    List.getElem_cons_succ]
  ext <;> simp <;> ring

theorem odd_true_0_0 (p q : Fraction) :
    ∃ a' ∈ MixedPieces.pOffsetsOdd true p q, ∃ b' ∈ MixedPieces.qOffsetsOdd true p q,
      (offP0 true p q .dsP1Plus) - (offP0 true p q .q1Plus) = a' - b' := by
  refine ⟨(MixedPieces.pOffsetsOdd true p q)[0]'(by simp [MixedPieces.pOffsetsOdd]),
    List.getElem_mem _, (MixedPieces.qOffsetsOdd true p q)[0]'(by simp [MixedPieces.qOffsetsOdd]),
    List.getElem_mem _, ?_⟩
  simp only [MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, offP0, coeffOff, altP0Coeff, texV1Odd, texV1Even, texV2, ite_true, List.getElem_cons_zero,
    ]
  ext <;> simp

theorem odd_true_0_1 (p q : Fraction) (hp : 0 < p.num ∧ p.num < p.den) (hq : 0 < q.num ∧ q.num < q.den)
    (hmp : SiteInduction.muOf p = 2) (hmq : SiteInduction.muOf q = 1) (z : Site) :
    ¬ (InH p (z - (offP0 true p q .dsP1Plus)) ∧ InH q (z - (offP0 true p q .q1Minus))) := by
  rintro ⟨h1, h2⟩
  have hb := boxes p q hp hq hmp hmq _ _ z h1 h2
  simp only [offP0, coeffOff, altP0Coeff, texV1Odd, texV1Even, texV2, ite_true] at hb
  omega

theorem odd_true_1_0 (p q : Fraction) (hp : 0 < p.num ∧ p.num < p.den) (hq : 0 < q.num ∧ q.num < q.den)
    (hmp : SiteInduction.muOf p = 2) (hmq : SiteInduction.muOf q = 1) (z : Site) :
    ¬ (InH p (z - (shP true p q + offP0 true p q .dsP1Plus)) ∧ InH q (z - (offP0 true p q .q1Plus))) := by
  rintro ⟨h1, h2⟩
  have hb := boxes p q hp hq hmp hmq _ _ z h1 h2
  simp only [offP0, shP, coeffOff, altP0Coeff, altShifts, texV1Odd, texV1Even, texV2, ite_true, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] at hb
  omega

theorem odd_true_1_1 (p q : Fraction) :
    ∃ a' ∈ MixedPieces.pOffsetsOdd true p q, ∃ b' ∈ MixedPieces.qOffsetsOdd true p q,
      (shP true p q + offP0 true p q .dsP1Plus) - (offP0 true p q .q1Minus) = a' - b' := by
  refine ⟨(MixedPieces.pOffsetsOdd true p q)[0]'(by simp [MixedPieces.pOffsetsOdd]),
    List.getElem_mem _, (MixedPieces.qOffsetsOdd true p q)[2]'(by simp [MixedPieces.qOffsetsOdd]),
    List.getElem_mem _, ?_⟩
  simp only [MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, offP0, shP, coeffOff, altP0Coeff, altShifts, texV1Odd, texV1Even, texV2, ite_true, List.getElem_cons_zero,
    List.getElem_cons_succ]
  ext <;> simp <;> ring

theorem odd_true_2_0 (p q : Fraction) :
    ∃ a' ∈ MixedPieces.pOffsetsOdd true p q, ∃ b' ∈ MixedPieces.qOffsetsOdd true p q,
      (offP0 true p q .dsP1Minus) - (offP0 true p q .q1Plus) = a' - b' := by
  refine ⟨(MixedPieces.pOffsetsOdd true p q)[1]'(by simp [MixedPieces.pOffsetsOdd]),
    List.getElem_mem _, (MixedPieces.qOffsetsOdd true p q)[1]'(by simp [MixedPieces.qOffsetsOdd]),
    List.getElem_mem _, ?_⟩
  simp only [MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, offP0, coeffOff, altP0Coeff, texV1Odd, texV1Even, texV2, ite_true, List.getElem_cons_zero,
    List.getElem_cons_succ]
  ext <;> simp <;> ring

theorem odd_true_2_1 (p q : Fraction) (hp : 0 < p.num ∧ p.num < p.den) (hq : 0 < q.num ∧ q.num < q.den)
    (hmp : SiteInduction.muOf p = 2) (hmq : SiteInduction.muOf q = 1) (z : Site) :
    ¬ (InH p (z - (offP0 true p q .dsP1Minus)) ∧ InH q (z - (offP0 true p q .q1Minus))) := by
  rintro ⟨h1, h2⟩
  have hb := boxes p q hp hq hmp hmq _ _ z h1 h2
  simp only [offP0, coeffOff, altP0Coeff, texV1Odd, texV1Even, texV2, ite_true] at hb
  omega

theorem odd_true_3_0 (p q : Fraction) (hp : 0 < p.num ∧ p.num < p.den) (hq : 0 < q.num ∧ q.num < q.den)
    (hmp : SiteInduction.muOf p = 2) (hmq : SiteInduction.muOf q = 1) (z : Site) :
    ¬ (InH p (z - (shP true p q + offP0 true p q .dsP1Minus)) ∧ InH q (z - (offP0 true p q .q1Plus))) := by
  rintro ⟨h1, h2⟩
  have hb := boxes p q hp hq hmp hmq _ _ z h1 h2
  simp only [offP0, shP, coeffOff, altP0Coeff, altShifts, texV1Odd, texV1Even, texV2, ite_true, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] at hb
  omega

theorem odd_true_3_1 (p q : Fraction) :
    ∃ a' ∈ MixedPieces.pOffsetsOdd true p q, ∃ b' ∈ MixedPieces.qOffsetsOdd true p q,
      (shP true p q + offP0 true p q .dsP1Minus) - (offP0 true p q .q1Minus) = a' - b' := by
  refine ⟨(MixedPieces.pOffsetsOdd true p q)[1]'(by simp [MixedPieces.pOffsetsOdd]),
    List.getElem_mem _, (MixedPieces.qOffsetsOdd true p q)[3]'(by simp [MixedPieces.qOffsetsOdd]),
    List.getElem_mem _, ?_⟩
  simp only [MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, offP0, shP, coeffOff, altP0Coeff, altShifts, texV1Odd, texV1Even, texV2, ite_true, List.getElem_cons_zero,
    List.getElem_cons_succ]
  ext <;> simp <;> ring

theorem even_false_0_0 (p q : Fraction) :
    ∃ a' ∈ MixedPieces.pOffsetsOdd false p q, ∃ b' ∈ MixedPieces.qOffsetsOdd false p q,
      (offQ0 false p q .p1Plus) - (offQ0 false p q .dsQ1Plus) = a' - b' := by
  refine ⟨(MixedPieces.pOffsetsOdd false p q)[0]'(by simp [MixedPieces.pOffsetsOdd]),
    List.getElem_mem _, (MixedPieces.qOffsetsOdd false p q)[1]'(by simp [MixedPieces.qOffsetsOdd]),
    List.getElem_mem _, ?_⟩
  simp only [MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, offQ0, coeffOff, altQ0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true, List.getElem_cons_zero,
    List.getElem_cons_succ]
  ext <;> simp

theorem even_false_0_1 (p q : Fraction) (hp : 0 < p.num ∧ p.num < p.den) (hq : 0 < q.num ∧ q.num < q.den)
    (hmp : SiteInduction.muOf p = 2) (hmq : SiteInduction.muOf q = 1) (z : Site) :
    ¬ (InH p (z - (offQ0 false p q .p1Plus)) ∧ InH q (z - (shQ false p q + offQ0 false p q .dsQ1Plus))) := by
  rintro ⟨h1, h2⟩
  have hb := boxes p q hp hq hmp hmq _ _ z h1 h2
  simp only [offQ0, shQ, coeffOff, altQ0Coeff, altShifts, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] at hb
  omega

theorem even_false_0_2 (p q : Fraction) :
    ∃ a' ∈ MixedPieces.pOffsetsOdd false p q, ∃ b' ∈ MixedPieces.qOffsetsOdd false p q,
      (offQ0 false p q .p1Plus) - (offQ0 false p q .dsQ1Minus) = a' - b' := by
  refine ⟨(MixedPieces.pOffsetsOdd false p q)[0]'(by simp [MixedPieces.pOffsetsOdd]),
    List.getElem_mem _, (MixedPieces.qOffsetsOdd false p q)[3]'(by simp [MixedPieces.qOffsetsOdd]),
    List.getElem_mem _, ?_⟩
  simp only [MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, offQ0, coeffOff, altQ0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true, List.getElem_cons_zero,
    List.getElem_cons_succ]
  ext <;> simp

theorem even_false_0_3 (p q : Fraction) (hp : 0 < p.num ∧ p.num < p.den) (hq : 0 < q.num ∧ q.num < q.den)
    (hmp : SiteInduction.muOf p = 2) (hmq : SiteInduction.muOf q = 1) (z : Site) :
    ¬ (InH p (z - (offQ0 false p q .p1Plus)) ∧ InH q (z - (shQ false p q + offQ0 false p q .dsQ1Minus))) := by
  rintro ⟨h1, h2⟩
  have hb := boxes p q hp hq hmp hmq _ _ z h1 h2
  simp only [offQ0, shQ, coeffOff, altQ0Coeff, altShifts, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] at hb
  omega

theorem even_false_1_0 (p q : Fraction) (hp : 0 < p.num ∧ p.num < p.den) (hq : 0 < q.num ∧ q.num < q.den)
    (hmp : SiteInduction.muOf p = 2) (hmq : SiteInduction.muOf q = 1) (z : Site) :
    ¬ (InH p (z - (offQ0 false p q .p1Minus)) ∧ InH q (z - (offQ0 false p q .dsQ1Plus))) := by
  rintro ⟨h1, h2⟩
  have hb := boxes p q hp hq hmp hmq _ _ z h1 h2
  simp only [offQ0, coeffOff, altQ0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true] at hb
  omega

theorem even_false_1_1 (p q : Fraction) :
    ∃ a' ∈ MixedPieces.pOffsetsOdd false p q, ∃ b' ∈ MixedPieces.qOffsetsOdd false p q,
      (offQ0 false p q .p1Minus) - (shQ false p q + offQ0 false p q .dsQ1Plus) = a' - b' := by
  refine ⟨(MixedPieces.pOffsetsOdd false p q)[1]'(by simp [MixedPieces.pOffsetsOdd]),
    List.getElem_mem _, (MixedPieces.qOffsetsOdd false p q)[0]'(by simp [MixedPieces.qOffsetsOdd]),
    List.getElem_mem _, ?_⟩
  simp only [MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, offQ0, shQ, coeffOff, altQ0Coeff, altShifts, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true, List.getElem_cons_zero,
    List.getElem_cons_succ]
  ext <;> simp <;> ring

theorem even_false_1_2 (p q : Fraction) (hp : 0 < p.num ∧ p.num < p.den) (hq : 0 < q.num ∧ q.num < q.den)
    (hmp : SiteInduction.muOf p = 2) (hmq : SiteInduction.muOf q = 1) (z : Site) :
    ¬ (InH p (z - (offQ0 false p q .p1Minus)) ∧ InH q (z - (offQ0 false p q .dsQ1Minus))) := by
  rintro ⟨h1, h2⟩
  have hb := boxes p q hp hq hmp hmq _ _ z h1 h2
  simp only [offQ0, coeffOff, altQ0Coeff, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true] at hb
  omega

theorem even_false_1_3 (p q : Fraction) :
    ∃ a' ∈ MixedPieces.pOffsetsOdd false p q, ∃ b' ∈ MixedPieces.qOffsetsOdd false p q,
      (offQ0 false p q .p1Minus) - (shQ false p q + offQ0 false p q .dsQ1Minus) = a' - b' := by
  refine ⟨(MixedPieces.pOffsetsOdd false p q)[1]'(by simp [MixedPieces.pOffsetsOdd]),
    List.getElem_mem _, (MixedPieces.qOffsetsOdd false p q)[2]'(by simp [MixedPieces.qOffsetsOdd]),
    List.getElem_mem _, ?_⟩
  simp only [MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, offQ0, shQ, coeffOff, altQ0Coeff, altShifts, texV1Odd, texV1Even, texV2, ite_false, Bool.false_eq_true, List.getElem_cons_zero,
    List.getElem_cons_succ]
  ext <;> simp <;> ring

theorem even_true_0_0 (p q : Fraction) :
    ∃ a' ∈ MixedPieces.pOffsetsOdd true p q, ∃ b' ∈ MixedPieces.qOffsetsOdd true p q,
      (offQ0 true p q .p1Plus) - (offQ0 true p q .dsQ1Plus) = a' - b' := by
  refine ⟨(MixedPieces.pOffsetsOdd true p q)[0]'(by simp [MixedPieces.pOffsetsOdd]),
    List.getElem_mem _, (MixedPieces.qOffsetsOdd true p q)[0]'(by simp [MixedPieces.qOffsetsOdd]),
    List.getElem_mem _, ?_⟩
  simp only [MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, offQ0, coeffOff, altQ0Coeff, texV1Odd, texV1Even, texV2, ite_true, List.getElem_cons_zero,
    ]
  ext <;> simp

theorem even_true_0_1 (p q : Fraction) (hp : 0 < p.num ∧ p.num < p.den) (hq : 0 < q.num ∧ q.num < q.den)
    (hmp : SiteInduction.muOf p = 2) (hmq : SiteInduction.muOf q = 1) (z : Site) :
    ¬ (InH p (z - (offQ0 true p q .p1Plus)) ∧ InH q (z - (shQ true p q + offQ0 true p q .dsQ1Plus))) := by
  rintro ⟨h1, h2⟩
  have hb := boxes p q hp hq hmp hmq _ _ z h1 h2
  simp only [offQ0, shQ, coeffOff, altQ0Coeff, altShifts, texV1Odd, texV1Even, texV2, ite_true, Prod.fst_add, Prod.snd_add] at hb
  omega

theorem even_true_0_2 (p q : Fraction) :
    ∃ a' ∈ MixedPieces.pOffsetsOdd true p q, ∃ b' ∈ MixedPieces.qOffsetsOdd true p q,
      (offQ0 true p q .p1Plus) - (offQ0 true p q .dsQ1Minus) = a' - b' := by
  refine ⟨(MixedPieces.pOffsetsOdd true p q)[0]'(by simp [MixedPieces.pOffsetsOdd]),
    List.getElem_mem _, (MixedPieces.qOffsetsOdd true p q)[2]'(by simp [MixedPieces.qOffsetsOdd]),
    List.getElem_mem _, ?_⟩
  simp only [MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, offQ0, coeffOff, altQ0Coeff, texV1Odd, texV1Even, texV2, ite_true, List.getElem_cons_zero,
    List.getElem_cons_succ]
  ext <;> simp

theorem even_true_0_3 (p q : Fraction) (hp : 0 < p.num ∧ p.num < p.den) (hq : 0 < q.num ∧ q.num < q.den)
    (hmp : SiteInduction.muOf p = 2) (hmq : SiteInduction.muOf q = 1) (z : Site) :
    ¬ (InH p (z - (offQ0 true p q .p1Plus)) ∧ InH q (z - (shQ true p q + offQ0 true p q .dsQ1Minus))) := by
  rintro ⟨h1, h2⟩
  have hb := boxes p q hp hq hmp hmq _ _ z h1 h2
  simp only [offQ0, shQ, coeffOff, altQ0Coeff, altShifts, texV1Odd, texV1Even, texV2, ite_true, Prod.fst_add, Prod.snd_add] at hb
  omega

theorem even_true_1_0 (p q : Fraction) (hp : 0 < p.num ∧ p.num < p.den) (hq : 0 < q.num ∧ q.num < q.den)
    (hmp : SiteInduction.muOf p = 2) (hmq : SiteInduction.muOf q = 1) (z : Site) :
    ¬ (InH p (z - (offQ0 true p q .p1Minus)) ∧ InH q (z - (offQ0 true p q .dsQ1Plus))) := by
  rintro ⟨h1, h2⟩
  have hb := boxes p q hp hq hmp hmq _ _ z h1 h2
  simp only [offQ0, coeffOff, altQ0Coeff, texV1Odd, texV1Even, texV2, ite_true] at hb
  omega

theorem even_true_1_1 (p q : Fraction) :
    ∃ a' ∈ MixedPieces.pOffsetsOdd true p q, ∃ b' ∈ MixedPieces.qOffsetsOdd true p q,
      (offQ0 true p q .p1Minus) - (shQ true p q + offQ0 true p q .dsQ1Plus) = a' - b' := by
  refine ⟨(MixedPieces.pOffsetsOdd true p q)[1]'(by simp [MixedPieces.pOffsetsOdd]),
    List.getElem_mem _, (MixedPieces.qOffsetsOdd true p q)[1]'(by simp [MixedPieces.qOffsetsOdd]),
    List.getElem_mem _, ?_⟩
  simp only [MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, offQ0, shQ, coeffOff, altQ0Coeff, altShifts, texV1Odd, texV1Even, texV2, ite_true, List.getElem_cons_zero,
    List.getElem_cons_succ]
  ext <;> simp <;> ring

theorem even_true_1_2 (p q : Fraction) (hp : 0 < p.num ∧ p.num < p.den) (hq : 0 < q.num ∧ q.num < q.den)
    (hmp : SiteInduction.muOf p = 2) (hmq : SiteInduction.muOf q = 1) (z : Site) :
    ¬ (InH p (z - (offQ0 true p q .p1Minus)) ∧ InH q (z - (offQ0 true p q .dsQ1Minus))) := by
  rintro ⟨h1, h2⟩
  have hb := boxes p q hp hq hmp hmq _ _ z h1 h2
  simp only [offQ0, coeffOff, altQ0Coeff, texV1Odd, texV1Even, texV2, ite_true] at hb
  omega

theorem even_true_1_3 (p q : Fraction) :
    ∃ a' ∈ MixedPieces.pOffsetsOdd true p q, ∃ b' ∈ MixedPieces.qOffsetsOdd true p q,
      (offQ0 true p q .p1Minus) - (shQ true p q + offQ0 true p q .dsQ1Minus) = a' - b' := by
  refine ⟨(MixedPieces.pOffsetsOdd true p q)[1]'(by simp [MixedPieces.pOffsetsOdd]),
    List.getElem_mem _, (MixedPieces.qOffsetsOdd true p q)[3]'(by simp [MixedPieces.qOffsetsOdd]),
    List.getElem_mem _, ?_⟩
  simp only [MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, offQ0, shQ, coeffOff, altQ0Coeff, altShifts, texV1Odd, texV1Even, texV2, ite_true, List.getElem_cons_zero,
    List.getElem_cons_succ]
  ext <;> simp <;> ring

/-- The pair dichotomy of the odd alternate child: every copy of `T(p₁)` and copy of `T(q₁)` among its standard
subtiles either have no common point, or sit at the relative offset of a pair of copies of the standard odd child. -/
theorem pairs_odd (o : Bool) (p q : Fraction) (hp : 0 < p.num ∧ p.num < p.den) (hq : 0 < q.num ∧ q.num < q.den)
    (hmp : SiteInduction.muOf p = 2) (hmq : SiteInduction.muOf q = 1) :
    ∀ a ∈ oddPOffs o p q, ∀ b ∈ oddQOffs o p q,
      (∀ z : Site, ¬ (InH p (z - a) ∧ InH q (z - b))) ∨
        ∃ a' ∈ MixedPieces.pOffsetsOdd o p q, ∃ b' ∈ MixedPieces.qOffsetsOdd o p q, a - b = a' - b' := by
  intro a ha b hb
  cases o <;> simp only [oddPOffs, oddQOffs, List.mem_cons, List.not_mem_nil, or_false] at ha hb <;>
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl
  · exact Or.inr (odd_false_0_0 p q)
  · exact Or.inl (odd_false_0_1 p q hp hq hmp hmq)
  · exact Or.inl (odd_false_1_0 p q hp hq hmp hmq)
  · exact Or.inr (odd_false_1_1 p q)
  · exact Or.inr (odd_false_2_0 p q)
  · exact Or.inl (odd_false_2_1 p q hp hq hmp hmq)
  · exact Or.inl (odd_false_3_0 p q hp hq hmp hmq)
  · exact Or.inr (odd_false_3_1 p q)
  · exact Or.inr (odd_true_0_0 p q)
  · exact Or.inl (odd_true_0_1 p q hp hq hmp hmq)
  · exact Or.inl (odd_true_1_0 p q hp hq hmp hmq)
  · exact Or.inr (odd_true_1_1 p q)
  · exact Or.inr (odd_true_2_0 p q)
  · exact Or.inl (odd_true_2_1 p q hp hq hmp hmq)
  · exact Or.inl (odd_true_3_0 p q hp hq hmp hmq)
  · exact Or.inr (odd_true_3_1 p q)

/-- The pair dichotomy of the even alternate child: every copy of `T(p₁)` and copy of `T(q₁)` among its standard
subtiles either have no common point, or sit at the relative offset of a pair of copies of the standard odd child. -/
theorem pairs_even (o : Bool) (p q : Fraction) (hp : 0 < p.num ∧ p.num < p.den) (hq : 0 < q.num ∧ q.num < q.den)
    (hmp : SiteInduction.muOf p = 2) (hmq : SiteInduction.muOf q = 1) :
    ∀ a ∈ evenPOffs o p q, ∀ b ∈ evenQOffs o p q,
      (∀ z : Site, ¬ (InH p (z - a) ∧ InH q (z - b))) ∨
        ∃ a' ∈ MixedPieces.pOffsetsOdd o p q, ∃ b' ∈ MixedPieces.qOffsetsOdd o p q, a - b = a' - b' := by
  intro a ha b hb
  cases o <;> simp only [evenPOffs, evenQOffs, List.mem_cons, List.not_mem_nil, or_false] at ha hb <;>
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
  · exact Or.inr (even_false_0_0 p q)
  · exact Or.inl (even_false_0_1 p q hp hq hmp hmq)
  · exact Or.inr (even_false_0_2 p q)
  · exact Or.inl (even_false_0_3 p q hp hq hmp hmq)
  · exact Or.inl (even_false_1_0 p q hp hq hmp hmq)
  · exact Or.inr (even_false_1_1 p q)
  · exact Or.inl (even_false_1_2 p q hp hq hmp hmq)
  · exact Or.inr (even_false_1_3 p q)
  · exact Or.inr (even_true_0_0 p q)
  · exact Or.inl (even_true_0_1 p q hp hq hmp hmq)
  · exact Or.inr (even_true_0_2 p q)
  · exact Or.inl (even_true_0_3 p q hp hq hmp hmq)
  · exact Or.inl (even_true_1_0 p q hp hq hmp hmq)
  · exact Or.inr (even_true_1_1 p q)
  · exact Or.inl (even_true_1_2 p q hp hq hmp hmq)
  · exact Or.inr (even_true_1_3 p q)

/-! ### The copies of a non-base word -/

/-- The parents of a non-base word lie in `(0, 1)`, with `μ = 2` for the odd one and `μ = 1` for the even one. -/
theorem parent_hyps {w : Word} (hw : ¬ IsBase w) :
    (0 < (parentsAt w).odd.num ∧ (parentsAt w).odd.num < (parentsAt w).odd.den) ∧
      (0 < (parentsAt w).even.num ∧ (parentsAt w).even.num < (parentsAt w).even.den) ∧
      SiteInduction.muOf (parentsAt w).odd = 2 ∧ SiteInduction.muOf (parentsAt w).even = 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := parents_facts hw
  exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, H3Data.muOf_of_odd _ h5, H3Data.muOf_of_even _ h6⟩

/-- The copy dichotomy of `T̂(p₀)` for a non-base word: a copy of `T(p₁)` and a copy of `T(q₁)` among the standard subtiles
have no common point, or sit at the relative offset of a pair of copies of the standard odd child. -/
theorem copies_odd {w : Word} (hw : ¬ IsBase w) :
    ∀ a ∈ oddPOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even,
    ∀ b ∈ oddQOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even,
      (∀ z : Site, ¬ (z ∈ shift (stateAt w).tOdd a ∧ z ∈ shift (stateAt w).tEven b)) ∨
        ∃ a' ∈ MixedPieces.pOffsetsOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even,
        ∃ b' ∈ MixedPieces.qOffsetsOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even, a - b = a' - b' := by
  intro a ha b hb
  obtain ⟨hp, hq, hmp, hmq⟩ := parent_hyps hw
  rcases pairs_odd _ _ _ hp hq hmp hmq a ha b hb with h | h
  · left
    intro z hz
    exact h z ⟨(mem_pCopy_iff hw a z).1 hz.1, (mem_qCopy_iff hw b z).1 hz.2⟩
  · exact Or.inr h

/-- The copy dichotomy of `T̂(q₀)` for a non-base word. -/
theorem copies_even {w : Word} (hw : ¬ IsBase w) :
    ∀ a ∈ evenPOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even,
    ∀ b ∈ evenQOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even,
      (∀ z : Site, ¬ (z ∈ shift (stateAt w).tOdd a ∧ z ∈ shift (stateAt w).tEven b)) ∨
        ∃ a' ∈ MixedPieces.pOffsetsOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even,
        ∃ b' ∈ MixedPieces.qOffsetsOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even, a - b = a' - b' := by
  intro a ha b hb
  obtain ⟨hp, hq, hmp, hmq⟩ := parent_hyps hw
  rcases pairs_even _ _ _ hp hq hmp hmq a ha b hb with h | h
  · left
    intro z hz
    exact h z ⟨(mem_pCopy_iff hw a z).1 hz.1, (mem_qCopy_iff hw b z).1 hz.2⟩
  · exact Or.inr h

theorem mem_shiftS_iff' (S : Set Site) (a z : Site) : z ∈ SiteInduction.shiftS S a ↔ z - a ∈ S :=
  CellRegisters.mem_shiftS_iff S a z

/-- A common translation of a pair of copies. -/
theorem shiftS_translate (S : Set Site) (a a' t z : Site) (ht : a = a' + t) :
    z ∈ SiteInduction.shiftS S a ↔ z - t ∈ SiteInduction.shiftS S a' := by
  rw [mem_shiftS_iff', mem_shiftS_iff', ht]
  constructor <;> intro h <;> convert h using 1 <;> abel

/-! ### Item (5), the form with the marked strings (no further input)

A common point of a copy of `T(p₁)` and a copy of `T(q₁)` among the standard subtiles of an alternate child lies in the marked
strings (the four zero-one boundary strings) of both copies. This is the form of item (d) of `lemma:standard_tile_properties`
proved in `MixedFromCells`, carried to the alternate child by the copy dichotomy. -/

/-- The marks form for a dichotomy of copies. -/
theorem marks_of_dichotomy {w : Word} (hw : ¬ IsBase w) (u1 u2 : Word) (h1 : (stateAt w).tOdd = oddTile u1)
    (h2 : (stateAt w).tEven = evenTile u2) (a b : Site)
    (hd : (∀ z : Site, ¬ (z ∈ shift (stateAt w).tOdd a ∧ z ∈ shift (stateAt w).tEven b)) ∨
        ∃ a' ∈ MixedPieces.pOffsetsOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even,
        ∃ b' ∈ MixedPieces.qOffsetsOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even, a - b = a' - b')
    (z : Site) (hza : z ∈ shift (stateAt w).tOdd a) (hzb : z ∈ shift (stateAt w).tEven b) :
    z ∈ SiteInduction.shiftS (SiteInduction.marksOdd u1) a ∧ z ∈ SiteInduction.shiftS (SiteInduction.marksEven u2) b := by
  rcases hd with hd | ⟨a', ha', b', hb', he⟩
  · exact absurd ⟨hza, hzb⟩ (hd z)
  · have hta : a = a' + (a - a') := by abel
    have htb : b = b' + (a - a') := by
      rw [← sub_eq_zero, show b - (b' + (a - a')) = -((a - b) - (a' - b')) by abel, he, sub_self, neg_zero]
    have hm := MixedFromCells.mixedOdd_all w hw u1 u2 h1 h2 a' ha' b' hb' (z - (a - a'))
      ((shiftS_translate _ a a' _ z hta).1 (by rw [mem_shiftS_iff']; rw [mem_shift, h1] at hza; exact hza))
      ((shiftS_translate _ b b' _ z htb).1 (by rw [mem_shiftS_iff']; rw [mem_shift, h2] at hzb; exact hzb))
    exact ⟨(shiftS_translate _ a a' _ z hta).2 hm.1, (shiftS_translate _ b b' _ z htb).2 hm.2⟩

/-- **Item (5), marks form, odd alternate child.** -/
theorem item5_marks_odd {w : Word} (hw : ¬ IsBase w) (u1 u2 : Word) (h1 : (stateAt w).tOdd = oddTile u1)
    (h2 : (stateAt w).tEven = evenTile u2) :
    ∀ a ∈ oddPOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even,
    ∀ b ∈ oddQOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even,
    ∀ z : Site, z ∈ shift (stateAt w).tOdd a → z ∈ shift (stateAt w).tEven b →
      z ∈ SiteInduction.shiftS (SiteInduction.marksOdd u1) a ∧ z ∈ SiteInduction.shiftS (SiteInduction.marksEven u2) b :=
  fun a ha b hb => marks_of_dichotomy hw u1 u2 h1 h2 a b (copies_odd hw a ha b hb)

/-- **Item (5), marks form, even alternate child.** -/
theorem item5_marks_even {w : Word} (hw : ¬ IsBase w) (u1 u2 : Word) (h1 : (stateAt w).tOdd = oddTile u1)
    (h2 : (stateAt w).tEven = evenTile u2) :
    ∀ a ∈ evenPOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even,
    ∀ b ∈ evenQOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even,
    ∀ z : Site, z ∈ shift (stateAt w).tOdd a → z ∈ shift (stateAt w).tEven b →
      z ∈ SiteInduction.shiftS (SiteInduction.marksOdd u1) a ∧ z ∈ SiteInduction.shiftS (SiteInduction.marksEven u2) b :=
  fun a ha b hb => marks_of_dichotomy hw u1 u2 h1 h2 a b (copies_even hw a ha b hb)

/-! ### Item (5), the stacked form, with the stacked form of item (d) as a named input

The text's conclusion: the shared boundary of the two copies is part of a stacked zero-one string, that is, each shared vertex
lies on both strands of one of the four stacked strings: the forward horizontal string of one copy and the reversed horizontal
string of the other, or the reversed vertical string of one copy and the forward vertical string of the other (the strings in
the order of `MixedOverlapStrings.strPart`: `0` forward horizontal, `1` reversed vertical, `2` reversed horizontal, `3` forward
vertical). The input `StackedMixedOdd` is the same statement for the pairs of copies of the standard odd child, which is the
stacked form of item (d) (E29, proved in the text at 7a40613; its formalisation is in progress), in the shape agreed for it. -/

/-- The shared vertices of two cell tiles: the endpoints of the boundary edges of `X` whose reversals are boundary edges of
`Y`. -/
def sharedVerts (X Y : CellTile) : Set GInt :=
  {z | ∃ e ∈ X.boundaryEdges, (e.2, e.1) ∈ Y.boundaryEdges ∧ (z = e.1 ∨ z = e.2)}

/-- The vertex `z` lies on both strands of one of the four stacked strings of a copy of `T(p₁)` (strings of `oddTile u1`) at `a`
and a copy of `T(q₁)` (strings of `evenTile u2`) at `b`. -/
def OnStackedPair (u1 u2 : Word) (a b z : Site) : Prop :=
  (z ∈ SiteInduction.shiftS (MixedOverlapStrings.oddStr u1 0) a ∧
      z ∈ SiteInduction.shiftS (MixedOverlapStrings.evenStr u2 2) b) ∨
    (z ∈ SiteInduction.shiftS (MixedOverlapStrings.oddStr u1 2) a ∧
      z ∈ SiteInduction.shiftS (MixedOverlapStrings.evenStr u2 0) b) ∨
    (z ∈ SiteInduction.shiftS (MixedOverlapStrings.oddStr u1 1) a ∧
      z ∈ SiteInduction.shiftS (MixedOverlapStrings.evenStr u2 3) b) ∨
    (z ∈ SiteInduction.shiftS (MixedOverlapStrings.oddStr u1 3) a ∧
      z ∈ SiteInduction.shiftS (MixedOverlapStrings.evenStr u2 1) b)

/-- **Named input: the stacked form of item (d)** for the standard odd child of `w`: every shared vertex of a copy of `T(p₁)`
and a copy of `T(q₁)` in its standard decomposition lies on both strands of a stacked string. -/
def StackedMixedOdd (w : Word) : Prop :=
  ∀ u1 u2 : Word, (stateAt w).tOdd = oddTile u1 → (stateAt w).tEven = evenTile u2 →
    ∀ a ∈ MixedPieces.pOffsetsOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even,
    ∀ b ∈ MixedPieces.qOffsetsOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even,
    ∀ z ∈ sharedVerts (shift (StandardClause.cellTileOf (oddTile u1)) a)
        (shift (StandardClause.cellTileOf (evenTile u2)) b), OnStackedPair u1 u2 a b z

theorem cellEdge_add (c t : GInt) (j : Fin 4) :
    cellEdge (c + t) j = ((cellEdge c j).1 + t, (cellEdge c j).2 + t) := by
  fin_cases j <;> simp only [cellEdge] <;> ext <;> simp <;> abel

theorem cellOther_add (c t : GInt) (j : Fin 4) : cellOther (c + t) j = cellOther c j + t := by
  fin_cases j <;> simp only [cellOther] <;> abel

/-- The boundary edges of a translated cell tile. -/
theorem mem_boundaryEdges_shift (X : CellTile) (t : GInt) (e : GInt × GInt) :
    e ∈ CellTile.boundaryEdges (shift X t) ↔ (e.1 - t, e.2 - t) ∈ X.boundaryEdges := by
  rw [mem_cellBoundary_iff, mem_cellBoundary_iff]
  constructor
  · rintro ⟨c, hc, j, rfl, ho⟩
    refine ⟨c - t, mem_shift.1 hc, j, ?_, ?_⟩
    · have := cellEdge_add (c - t) t j
      rw [sub_add_cancel] at this
      rw [this]; ext <;> simp
    · intro h
      apply ho
      rw [mem_shift]
      have := cellOther_add (c - t) t j
      rw [sub_add_cancel] at this
      rw [this, add_sub_cancel_right]
      exact h
  · rintro ⟨c, hc, j, he, ho⟩
    refine ⟨c + t, mem_shift.2 (by rw [add_sub_cancel_right]; exact hc), j, ?_, ?_⟩
    · rw [cellEdge_add, he]; ext <;> simp
    · intro h
      apply ho
      rw [mem_shift, cellOther_add, add_sub_cancel_right] at h
      exact h

/-- The shared vertices of two translated cell tiles. -/
theorem sharedVerts_shift (X Y : CellTile) (t z : GInt) (h : z ∈ sharedVerts (shift X t) (shift Y t)) :
    z - t ∈ sharedVerts X Y := by
  obtain ⟨e, he, he', hz⟩ := h
  refine ⟨(e.1 - t, e.2 - t), (mem_boundaryEdges_shift X t e).1 he, (mem_boundaryEdges_shift Y t (e.2, e.1)).1 he', ?_⟩
  rcases hz with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A shared vertex is a corner of a cell of each tile, hence a point of the site tile of each copy. -/
theorem mem_of_boundaryEdge (T : Finset Site) (a : GInt) (e : GInt × GInt)
    (he : e ∈ CellTile.boundaryEdges (shift (StandardClause.cellTileOf T) a)) : e.1 ∈ shift T a ∧ e.2 ∈ shift T a := by
  rw [mem_cellBoundary_iff] at he
  obtain ⟨c, hc, j, rfl, -⟩ := he
  rw [mem_shift] at hc
  have hsub := (Finset.mem_filter.1 hc).2
  have hc' : c = (c - a) + a := by abel
  rw [hc', cellEdge_add]
  simp only [mem_shift, add_sub_cancel_right]
  fin_cases j <;> simp only [cellEdge] <;> constructor <;> apply hsub <;> simp [cellCorners, add_assoc]

theorem sharedVerts_mem (T1 T2 : Finset Site) (a b z : GInt)
    (h : z ∈ sharedVerts (shift (StandardClause.cellTileOf T1) a) (shift (StandardClause.cellTileOf T2) b)) :
    z ∈ shift T1 a ∧ z ∈ shift T2 b := by
  obtain ⟨e, he, he', hz⟩ := h
  have h1 := mem_of_boundaryEdge T1 a e he
  have h2 := mem_of_boundaryEdge T2 b _ he'
  rcases hz with rfl | rfl
  · exact ⟨h1.1, h2.2⟩
  · exact ⟨h1.2, h2.1⟩

theorem onStackedPair_translate (u1 u2 : Word) (a b a' b' t z : Site) (ha : a = a' + t) (hb : b = b' + t)
    (h : OnStackedPair u1 u2 a' b' (z - t)) : OnStackedPair u1 u2 a b z := by
  unfold OnStackedPair at *
  simp only [shiftS_translate _ a a' t z ha, shiftS_translate _ b b' t z hb]
  exact h

/-- The stacked form for a dichotomy of copies. -/
theorem stacked_of_dichotomy {w : Word} (hS : StackedMixedOdd w) (u1 u2 : Word) (h1 : (stateAt w).tOdd = oddTile u1)
    (h2 : (stateAt w).tEven = evenTile u2) (a b : Site)
    (hd : (∀ z : Site, ¬ (z ∈ shift (stateAt w).tOdd a ∧ z ∈ shift (stateAt w).tEven b)) ∨
        ∃ a' ∈ MixedPieces.pOffsetsOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even,
        ∃ b' ∈ MixedPieces.qOffsetsOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even, a - b = a' - b')
    (z : GInt) (hz : z ∈ sharedVerts (shift (StandardClause.cellTileOf (oddTile u1)) a)
      (shift (StandardClause.cellTileOf (evenTile u2)) b)) : OnStackedPair u1 u2 a b z := by
  rcases hd with hd | ⟨a', ha', b', hb', he⟩
  · have hm := sharedVerts_mem _ _ a b z hz
    rw [← h1, ← h2] at hm
    exact absurd hm (hd z)
  · have hta : a = a' + (a - a') := by abel
    have htb : b = b' + (a - a') := by
      rw [← sub_eq_zero, show b - (b' + (a - a')) = -((a - b) - (a' - b')) by abel, he, sub_self, neg_zero]
    refine onStackedPair_translate u1 u2 a b a' b' (a - a') z hta htb (hS u1 u2 h1 h2 a' ha' b' hb' _ ?_)
    apply sharedVerts_shift
    rw [Standard.shift_shift, Standard.shift_shift, ← hta, ← htb]
    exact hz

/-- **Item (5) of `lemma:alternate_tile_properties`, odd alternate child `T̂(p₀)`**, given the stacked form of item (d): every
shared vertex of a copy of `T(p₁)` and a copy of `T(q₁)` among the standard subtiles lies on both strands of a stacked
horizontal or vertical zero-one string of the two copies. -/
theorem item5_odd {w : Word} (hw : ¬ IsBase w) (hS : StackedMixedOdd w) (u1 u2 : Word)
    (h1 : (stateAt w).tOdd = oddTile u1) (h2 : (stateAt w).tEven = evenTile u2) :
    ∀ a ∈ oddPOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even,
    ∀ b ∈ oddQOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even,
    ∀ z ∈ sharedVerts (shift (StandardClause.cellTileOf (oddTile u1)) a)
        (shift (StandardClause.cellTileOf (evenTile u2)) b), OnStackedPair u1 u2 a b z :=
  fun a ha b hb => stacked_of_dichotomy hS u1 u2 h1 h2 a b (copies_odd hw a ha b hb)

/-- **Item (5) of `lemma:alternate_tile_properties`, even alternate child `T̂(q₀)`**, given the stacked form of item (d). -/
theorem item5_even {w : Word} (hw : ¬ IsBase w) (hS : StackedMixedOdd w) (u1 u2 : Word)
    (h1 : (stateAt w).tOdd = oddTile u1) (h2 : (stateAt w).tEven = evenTile u2) :
    ∀ a ∈ evenPOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even,
    ∀ b ∈ evenQOffs (phase w == 1) (parentsAt w).odd (parentsAt w).even,
    ∀ z ∈ sharedVerts (shift (StandardClause.cellTileOf (oddTile u1)) a)
        (shift (StandardClause.cellTileOf (evenTile u2)) b), OnStackedPair u1 u2 a b z :=
  fun a ha b hb => stacked_of_dichotomy hS u1 u2 h1 h2 a b (copies_even hw a ha b hb)

end FLatticePaper.Tiles.AltItem5
