import FLatticePaper.Plane.Induction.EPolicyPrescribed
import FLatticePaper.Plane.Induction.SquareClauses
import FLatticePaper.Plane.Induction.AndOrRank

/-!
# The unit square clauses of the signed policy e(-1, eta) on the reciprocal field (task 118, W1 base)

`SquareClauseSat F sel a b`: some corner of the unit square at `(a, b)` is not kept inside the square. The selection
`selF` is equivariant under the deck (`selF_deck`), the laplacian is deck invariant, so the clause at `(a, b)` follows from
the clause at a native lower-left corner (`squareClause_of_native`). The remaining statement is the case analysis of the
native lower-left squares (`squares_native`).
-/

namespace FLatticePaper.EPolicy

open Classical FLatticePaper FLatticePaper.PureRank FLatticePaper.Construction FLatticePaper.Farey FLatticePaper.Induction
  FLatticePaper.SquareClauses FLatticePaper.AndOrRank

/-- The selection of a deck translate of a site is the selection of the site (the representatives are duplicates). -/
theorem selDisp_nativeRep_deck (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (c : ℤ × ℤ) (i0 j0 : ℤ) :
    selDisp (2 * (k : ℤ) + 3) η (nativeRep (2 * (k : ℤ) + 3) (c + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i0 j0)) =
      selDisp (2 * (k : ℤ) + 3) η (nativeRep (2 * (k : ℤ) + 3) c) := by
  have hden := stairEven_valid_reciprocal k
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hc1 : ∀ i j : ℤ, ((Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j).1 =
      i * (2 * (k : ℤ) + 3) + j * (1 - (2 * (k : ℤ) + 3)) := fun i j => by
    rw [combine_mk_one hd]
  have hc2 : ∀ i j : ℤ, ((Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j).2 =
      i + j * ((2 * (k : ℤ) + 3) + 1) := fun i j => by
    rw [combine_mk_one hd]
    ring
  obtain ⟨hy1, i1, j1, h1⟩ := nativeRep_spec hden c
  obtain ⟨hy2, i2, j2, h2⟩ := nativeRep_spec hden (c + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i0 j0)
  have e1 := congrArg Prod.fst h1
  have e2 := congrArg Prod.snd h1
  have f1 := congrArg Prod.fst h2
  have f2 := congrArg Prod.snd h2
  simp only [Prod.fst_add, Prod.snd_add] at e1 e2 f1 f2
  rw [hc1 i1 j1] at e1
  rw [hc2 i1 j1] at e2
  rw [hc1 i0 j0, hc1 i2 j2] at f1
  rw [hc2 i0 j0, hc2 i2 j2] at f2
  have hq1 : (nativeRep (2 * (k : ℤ) + 3) (c + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i0 j0)).1 =
      (nativeRep (2 * (k : ℤ) + 3) c).1 + (i0 + i1 - i2) * (2 * (k : ℤ) + 3) + (j0 + j1 - j2) * (1 - (2 * (k : ℤ) + 3)) := by
    linear_combination e1 - f1
  have hq2 : (nativeRep (2 * (k : ℤ) + 3) (c + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i0 j0)).2 =
      (nativeRep (2 * (k : ℤ) + 3) c).2 + (i0 + i1 - i2) + (j0 + j1 - j2) * ((2 * (k : ℤ) + 3) + 1) := by
    linear_combination e2 - f2
  exact (selDisp_dup (by omega) hd hη hy1 hy2 hq1 hq2).symm

end FLatticePaper.EPolicy
