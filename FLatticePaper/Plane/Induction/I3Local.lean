import FLatticePaper.Plane.Induction.OpenLocal
import FLatticePaper.Plane.Induction.LocalPremisesRestricted

/-! Task 38 (I3): the restricted no-fort conditions from strict ranks.

The restricted no-fort condition `RestrictedNoFort field grade permits` says that no nonempty restricted fort lies in a
half-space `{level ≤ grade}`. Here it is derived from a strict rank on the permitted inputs, provided the rank dominates a
positive multiple of the grade up to a constant. The least-rank argument: a fort in such a half-space has a least rank
value; at a site of least rank, the local permit property (`PermitLocal`) gives a permitted input in the fort whose rank is
strictly smaller, which is impossible.

The fields the earlier word must supply for the two sheets are `RankGradeFields`: a strict rank on the permitted inputs
whose increments along the two generators of the odd parent's modified deck are a common positive multiple of the grade's
increments (the character of the rank is proportional to that of the grade). The local permit property is `PermitLocal`
(a site of Laplacian `-1` permits both inputs, a site of Laplacian `0` at least one). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- A function invariant under both generators of a period deck is invariant under the whole span. -/
theorem invariant_of_combine {f : Site → ℤ} {deck : PeriodDeck}
    (hK : ∀ x, f (x + deck.kernel) = f x) (hT : ∀ x, f (x + deck.transverse) = f x) (x : Site) (i j : ℤ) :
    f (x + deck.combine i j) = f x := by
  have hKi : ∀ (n : ℤ) (y : Site), f (y + n • deck.kernel) = f y := by
    intro n
    induction n using Int.induction_on with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      have e : y + ((k : ℤ) + 1) • deck.kernel = (y + (k : ℤ) • deck.kernel) + deck.kernel := by
        rw [add_smul, one_smul, add_assoc]
      rw [e, hK, ih]
    | pred k ih =>
      intro y
      have h1 := hK (y + (-(k : ℤ) - 1) • deck.kernel)
      have h2 := ih y
      have e : y + (-(k : ℤ) - 1) • deck.kernel + deck.kernel = y + (-(k : ℤ)) • deck.kernel := by
        rw [add_assoc, sub_smul, one_smul, sub_add_cancel]
      rw [← h1, e, h2]
  have hTi : ∀ (n : ℤ) (y : Site), f (y + n • deck.transverse) = f y := by
    intro n
    induction n using Int.induction_on with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      have e : y + ((k : ℤ) + 1) • deck.transverse = (y + (k : ℤ) • deck.transverse) + deck.transverse := by
        rw [add_smul, one_smul, add_assoc]
      rw [e, hT, ih]
    | pred k ih =>
      intro y
      have h1 := hT (y + (-(k : ℤ) - 1) • deck.transverse)
      have h2 := ih y
      have e : y + (-(k : ℤ) - 1) • deck.transverse + deck.transverse = y + (-(k : ℤ)) • deck.transverse := by
        rw [add_assoc, sub_smul, one_smul, sub_add_cancel]
      rw [← h1, e, h2]
  have hcomb : deck.combine i j = i • deck.kernel + j • deck.transverse := by
    ext <;> simp [PeriodDeck.combine]
  rw [hcomb, ← add_assoc, hTi j (x + i • deck.kernel), hKi i x]

/-- A function invariant under the span of a period deck with positive determinant is bounded below. -/
theorem exists_lower_bound_of_periodic {deck : PeriodDeck} (hpos : 0 < deck.det) {f : Site → ℤ}
    (hper : ∀ x i j, f (x + deck.combine i j) = f x) : ∃ C : ℤ, ∀ x, -C ≤ f x := by
  have hcov : deck.Covers deck.residueSquare :=
    (PeriodDeck.covers_iff_square_codes_subset deck hpos deck.residueSquare).mpr subset_rfl
  obtain ⟨rep0, hrep0, -⟩ := hcov (0, 0)
  obtain ⟨m, hm, hmax⟩ := deck.residueSquare.exists_max_image (fun y => |f y|) ⟨rep0, hrep0⟩
  refine ⟨|f m|, fun x => ?_⟩
  obtain ⟨rep, hrep, hdiff⟩ := hcov x
  obtain ⟨i, j, hij⟩ := hdiff
  have hx : x = rep + deck.combine i j := by rw [← hij]; abel
  have hfx : f x = f rep := by rw [hx]; exact hper rep i j
  have hle : |f rep| ≤ |f m| := hmax rep hrep
  have hneg := neg_abs_le (f rep)
  rw [hfx]
  linarith

/-- The fields of the earlier word for one sheet: a strict rank on the permitted inputs whose increments along the two
generators of the deck are a common positive multiple of the grade's increments. -/
def RankGradeFields (permits : Site → Site → Prop) (grade : Site → ℤ) (deck : PeriodDeck) : Prop :=
  ∃ rank : Site → ℤ, ∃ κ : ℤ, 0 < κ ∧
    (∀ c i, Edge i c → permits c i → rank i < rank c) ∧
    (∀ x, rank (x + deck.kernel) - rank x = κ * (grade (x + deck.kernel) - grade x)) ∧
    (∀ x, rank (x + deck.transverse) - rank x = κ * (grade (x + deck.transverse) - grade x))

/-- **Least-rank argument.** A strict rank on the permitted inputs, dominating `κ · grade - C` with `κ > 0`, together with
the local permit property, forbids a restricted fort in a half-space of the grade. -/
theorem restrictedNoFort_of_strictRank {field grade : Field} {permits : Site → Site → Prop}
    (hloc : PermitLocal field permits) (rank : Site → ℤ)
    (hstrict : ∀ c i, Edge i c → permits c i → rank i < rank c)
    (κ C : ℤ) (hκ : 0 < κ) (hbound : ∀ x, κ * grade x - C ≤ rank x) :
    RestrictedNoFort field grade permits := by
  classical
  intro level fort hne hfort hlevel
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨least, ⟨s, hs, hsv⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun v => ∃ x ∈ fort, rank x = v)
    ⟨κ * level - C, by
      rintro _ ⟨x, hx, rfl⟩
      have h1 := mul_le_mul_of_nonneg_left (hlevel x hx) hκ.le
      have h2 := hbound x
      linarith⟩
    ⟨rank x0, x0, hx0, rfl⟩
  -- a permitted input of `s` lying in the fort would have a strictly smaller rank than the least one
  have key : ∀ i, Edge i s → permits s i → i ∈ fort → False := by
    intro i he hp hi
    have h1 := hmin (rank i) ⟨i, hi, rfl⟩
    have h2 := hstrict s i he hp
    omega
  -- a blocked input (in the fort, or not permitted) of a permitted input is in the fort, hence excluded
  have blocked : ∀ i, Edge i s → permits s i → (i ∈ fort ∨ ¬ permits s i) → False := by
    intro i he hp hb
    rcases hb with hmem | hnp
    · exact key i he hp hmem
    · exact hnp hp
  rcases hfort s hs with ⟨hl, hn | hp⟩ | ⟨hl, hn, hp⟩
  · rcases hloc.1 s hl with ⟨h1, h2⟩
    rcases hn with hmem | hnp
    · exact blocked _ (Or.inl rfl) h1 (Or.inl hmem)
    · exact hnp h1
  · rcases hloc.1 s hl with ⟨h1, h2⟩
    rcases hp with hmem | hnp
    · exact blocked _ (Or.inr rfl) h2 (Or.inl hmem)
    · exact hnp h2
  · rcases hloc.2 s hl with h1 | h2
    · exact blocked _ (Or.inl rfl) h1 hn
    · exact blocked _ (Or.inr rfl) h2 hp

/-- The rank-grade fields give the restricted no-fort condition: the rank minus `κ · grade` is invariant under the deck,
hence bounded below, and the least-rank argument applies. -/
theorem restrictedNoFort_of_rankGrade {field grade : Field} {permits : Site → Site → Prop} {deck : PeriodDeck}
    (hpos : 0 < deck.det) (hloc : PermitLocal field permits) (hF : RankGradeFields permits grade deck) :
    RestrictedNoFort field grade permits := by
  obtain ⟨rank, κ, hκ, hstrict, hK, hT⟩ := hF
  have hK' : ∀ y, (rank - fun z => κ * grade z) (y + deck.kernel) = (rank - fun z => κ * grade z) y := by
    intro y
    simp only [Pi.sub_apply]
    linear_combination hK y
  have hT' : ∀ y, (rank - fun z => κ * grade z) (y + deck.transverse) =
      (rank - fun z => κ * grade z) y := by
    intro y
    simp only [Pi.sub_apply]
    linear_combination hT y
  have hinv : ∀ x i j, (rank - fun z => κ * grade z) (x + deck.combine i j) =
      (rank - fun z => κ * grade z) x :=
    fun x i j => invariant_of_combine hK' hT' x i j
  obtain ⟨C, hC⟩ := exists_lower_bound_of_periodic hpos hinv
  exact restrictedNoFort_of_strictRank hloc rank hstrict κ C hκ (fun x => by
    have h := hC x
    simp only [Pi.sub_apply] at h
    linarith)

/-- The restricted no-fort condition of the sheet `A`, from its rank-grade fields and the local permit property: the
permitted inputs are those of `Ξ`, and the grade is `i3aGrade`. -/
theorem noA_of_fields {word : Word}
    (hloc : PermitLocal (quarterTurnField (standardField (conjWord word)))
      (fun c i => sheetChainPotential word (standardField (conjWord word)) i ≤
        sheetChainPotential word (standardField (conjWord word)) c))
    (hF : RankGradeFields (fun c i => sheetChainPotential word (standardField (conjWord word)) i ≤
        sheetChainPotential word (standardField (conjWord word)) c) (i3aGrade word)
      (parentsAt word).odd.modifiedDeck) :
    RestrictedNoFort (quarterTurnField (standardField (conjWord word))) (i3aGrade word)
      (fun c i => sheetChainPotential word (standardField (conjWord word)) i ≤
        sheetChainPotential word (standardField (conjWord word)) c) := by
  have hint : (parentsAt word).odd.InUnitInterval := (parentsAt_valid word).odd_bounds
  exact restrictedNoFort_of_rankGrade (Fraction.det_modifiedDeck_pos hint) hloc hF

/-- The restricted no-fort condition of the sheet `C`: the permitted inputs are those of `Ξ` shifted by the sheet offset,
and the grade is the transverse grade of the frame. -/
theorem noC_of_fields {word : Word}
    (hloc : PermitLocal (quarterTurnField (standardField (conjWord word)))
      (fun c i => sheetChainPotential word (standardField (conjWord word)) (c + (frameAt word).sheetOffset) ≤
        sheetChainPotential word (standardField (conjWord word)) (i + (frameAt word).sheetOffset)))
    (hF : RankGradeFields (fun c i => sheetChainPotential word (standardField (conjWord word))
        (c + (frameAt word).sheetOffset) ≤
        sheetChainPotential word (standardField (conjWord word)) (i + (frameAt word).sheetOffset))
      (frameAt word).tGrade (parentsAt word).odd.modifiedDeck) :
    RestrictedNoFort (quarterTurnField (standardField (conjWord word))) (frameAt word).tGrade
      (fun c i => sheetChainPotential word (standardField (conjWord word)) (c + (frameAt word).sheetOffset) ≤
        sheetChainPotential word (standardField (conjWord word)) (i + (frameAt word).sheetOffset)) := by
  have hint : (parentsAt word).odd.InUnitInterval := (parentsAt_valid word).odd_bounds
  exact restrictedNoFort_of_rankGrade (Fraction.det_modifiedDeck_pos hint) hloc hF

/-- `SheetLocalInputs` at a word, from the unit increments of the chain potential (task (b), an input here) and the two
local permit properties and rank-grade fields of the sheets (the earlier word's signed data). The restricted no-fort
conditions of both sheets are then derived, not assumed. -/
theorem sheetLocalInputs_of_fields {word : Word}
    (hunit : ∀ c i : Site, FLatticePaper.Edge i c →
      -1 ≤ sheetChainPotential word (standardField (conjWord word)) i -
          sheetChainPotential word (standardField (conjWord word)) c ∧
        sheetChainPotential word (standardField (conjWord word)) i -
          sheetChainPotential word (standardField (conjWord word)) c ≤ 1)
    (hlocA : PermitLocal (quarterTurnField (standardField (conjWord word)))
      (fun c i => sheetChainPotential word (standardField (conjWord word)) i ≤
        sheetChainPotential word (standardField (conjWord word)) c))
    (hFA : RankGradeFields (fun c i => sheetChainPotential word (standardField (conjWord word)) i ≤
        sheetChainPotential word (standardField (conjWord word)) c) (i3aGrade word)
      (parentsAt word).odd.modifiedDeck)
    (hlocC : PermitLocal (quarterTurnField (standardField (conjWord word)))
      (fun c i => sheetChainPotential word (standardField (conjWord word)) (c + (frameAt word).sheetOffset) ≤
        sheetChainPotential word (standardField (conjWord word)) (i + (frameAt word).sheetOffset)))
    (hFC : RankGradeFields (fun c i => sheetChainPotential word (standardField (conjWord word))
        (c + (frameAt word).sheetOffset) ≤
        sheetChainPotential word (standardField (conjWord word)) (i + (frameAt word).sheetOffset))
      (frameAt word).tGrade (parentsAt word).odd.modifiedDeck) :
    SheetLocalInputs word :=
  ⟨hunit, hlocA, noA_of_fields hlocA hFA, hlocC, noC_of_fields hlocC hFC⟩

end FLatticePaper.Induction
