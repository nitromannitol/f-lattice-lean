import FLatticePaper.Tiles.CorrectedDiagramWidths
import FLatticePaper.Tiles.CorrectedBandFaces

/-! Word specializations of the two register comparisons, before selecting their finite cases. -/

namespace FLatticePaper.Tiles.CorrectedWordCoverage

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard
open CorrectedRegisterDiagram CorrectedRegisterWords CorrectedRegisterFaces CorrectedDomainLattice

/-- The first target, together with the opposite target when present, is covered
by entries one through the number of sources. -/
def Covers (P : ℕ → Prop) (two : Bool) (count : ℕ) : Prop :=
  (if two then P 0 ∨ P 9 else P 0) ↔ ∃ i : Fin count, P (i.val+1)

/-- Equality of membership on the ten possible diagram entries preserves both inclusions. -/
theorem congr_cover {P Q : ℕ → Prop} (two : Bool) {count : ℕ} (n : count ≤ 8)
    (eqv : ∀ i : Fin 10, P i.val ↔ Q i.val) : Covers P two count ↔ Covers Q two count := by
  have l : P 0 ↔ Q 0 := eqv 0
  have h : P 9 ↔ Q 9 := eqv 9
  have R : (∃ i : Fin count, P (i.val+1)) ↔ ∃ i : Fin count, Q (i.val+1) :=
    exists_congr fun i => eqv ⟨i.val+1,by have := i.isLt; omega⟩
  cases two <;> simp only [Covers,Bool.false_eq_true,if_false,if_true,l,h,R]

/-- The even checkerboard representative of an arbitrary physical site. -/
def representative (z : Site) := z-CorrectedBandFaces.reference z

theorem representative_even (z : Site) :
    ((representative z).1+(representative z).2)%2=0 := by
  by_cases ho : (z.1+z.2)%2=1 <;>
    simp [representative,CorrectedBandFaces.reference,CorrectedCellsBands.oddSite,ho] <;> omega

/-- Specialize a corrected register comparison to a word, deriving every frame
and congruence premise and replacing the cutoff tests with unbounded determinants. -/
theorem corrected (x : Digit) (xs : Word) (hw : ¬ IsBase (x::xs)) (one long : Bool)
    (N : ℕ) (hN : 0 < N) (z : Site) :
    let P := parentsAt (x::xs)
    let prev := -P.odd.det P.even
    let sec := firstSector x
    let par := CorrectedCellsBands.oddSite z
    let r := register P one N (chart (P.current .odd) (representative z))
    let shape := CorrectedRegisterDiagram.corrected r one prev long
    (Regular r one sec → r.M ∣ r.S → (∀ i : ℕ, (shape i).lattice r (orientation one prev) par sec) →
        Covers (fun i => (shape i).contains r par sec) long 8) →
      Covers (fun i => exact ((shape i).probe r par sec)) long 8 := by
  intro P prev sec par r shape proof
  have hr : Regular r one sec := regular x xs hw one N hN _
  have hd : r.M ∣ r.S := dvd_mul_left r.M (N : ℤ)
  have hp : prev=1 ∨ prev= -1 := by
    change -(P.odd.det P.even)=1 ∨ -(P.odd.det P.even)= -1
    have d : P.odd.det P.even=1 ∨ P.odd.det P.even= -1 := (parentsAt_valid (x::xs)).unit_det
    omega
  have result := proof hr hd fun i => CorrectedRegisterLattice.word (x::xs) one long par sec N _ (representative_even z) i
  refine (congr_cover long (by decide : 8 ≤ 8) fun i => ?_).mpr result
  exact shape_iff _ _ _ _ (CorrectedDiagramWidths.corrected_fits r one long par prev sec hr hp i)

/-- The six- or eight-source comparison of the mixed alternate parent for a
non-base preceding word, in actual lattice coordinates at an arbitrary site. -/
theorem mixed (x : Digit) (xs : Word) (hw : ¬ IsBase (x::xs)) (one even : Bool) (z : Site) :
    let P := parentsAt (x::xs)
    let prev := -P.odd.det P.even
    let sec := firstSector x
    let par := CorrectedCellsBands.oddSite z
    let r := register P one 1 (chart (P.current .odd) (representative z))
    let shape := CorrectedMixedDiagram.mixed r one prev even
    let count := if one || even then 8 else 6
    (Regular r one sec → r.M ∣ r.S → r.S=r.M →
        (∀ i : ℕ, (shape i).lattice r (orientation one prev) par sec) →
        Covers (fun i => (shape i).contains r par sec) true count) →
      Covers (fun i => exact ((shape i).probe r par sec)) true count := by
  intro P prev sec par r shape count proof
  have hr : Regular r one sec := regular x xs hw one 1 (by decide) _
  have run : r.S=r.M := one_mul _
  have hp : prev=1 ∨ prev= -1 := by
    have d : P.odd.det P.even=1 ∨ P.odd.det P.even= -1 := (parentsAt_valid (x::xs)).unit_det
    dsimp only [prev]; omega
  have n : count ≤ 8 := by dsimp [count]; split <;> decide
  have result := proof hr (by rw [run]) run fun i =>
    CorrectedMixedDiagram.word (x::xs) one even par sec _ (representative_even z) i
  refine (congr_cover true n fun i => ?_).mpr result
  exact shape_iff _ _ _ _ (CorrectedDiagramWidths.mixed_fits r one even par prev sec hr hp i)

end FLatticePaper.Tiles.CorrectedWordCoverage
