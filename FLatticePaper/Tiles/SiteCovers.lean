import FLatticePaper.Tiles.SiteMaskStair
import FLatticePaper.Construction.StaircaseCoverage

/-! Task 53, item 1: the covers of the base masks, transferred from the repository's deck covers to `QuotientCover`.

The repository's `PeriodDeck.Covers` on `(Fraction.mk 1 d).modifiedDeck` is the same statement as `QuotientCover` with the periods
`perU`, `perV`: the kernel of `Fraction.modifiedDeck` is `perU` (the multiplicity `periodMultiplicity` equals `muOf`), and its
transverse is `perV`. So a cover of the raw mask sites by the deck gives a native quotient cover of the `H` set once the mask is
`H` (`M1`, `SiteMaskStair.stair_eq`). -/

namespace FLatticePaper.Tiles.SiteCovers

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SiteMaskStair

theorem periodMultiplicity_eq (f : Fraction) : f.periodMultiplicity = muOf f := by
  unfold Fraction.periodMultiplicity muOf
  split_ifs <;> omega

theorem modifiedDeck_kernel (f : Fraction) : f.modifiedDeck.kernel = perU f := by
  unfold Fraction.modifiedDeck perU
  simp only [periodMultiplicity_eq]

theorem modifiedDeck_transverse (f : Fraction) : f.modifiedDeck.transverse = perV f := by
  unfold Fraction.modifiedDeck Fraction.unmodifiedDeck perV
  simp only [add_comm f.num f.den]

/-- A cover of a finite set by the modified deck of `f` is a native quotient cover of the set with the periods of `f`. -/
theorem quotientCover_of_covers (f : Fraction) (S : Finset (ℤ × ℤ)) (h : f.modifiedDeck.Covers S) :
    QuotientCover (S : Set (ℤ × ℤ)) (perU f) (perV f) := by
  intro z
  obtain ⟨r, hr, hspan⟩ := h z
  obtain ⟨i, j, hij⟩ := hspan
  refine ⟨r, Finset.mem_coe.mpr hr, i, j, ?_, ?_⟩
  · rw [← modifiedDeck_kernel, ← modifiedDeck_transverse]
    have h1 := congrArg Prod.fst hij
    simp only [PeriodDeck.combine, Prod.fst_sub] at h1
    exact h1
  · rw [← modifiedDeck_kernel, ← modifiedDeck_transverse]
    have h2 := congrArg Prod.snd hij
    simp only [PeriodDeck.combine, Prod.snd_sub] at h2
    exact h2

/-- The raw even staircase is the set `stairF`. -/
theorem stairEven_raw_sites_eq (k : ℕ) :
    (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites = stairF (2 * (k : ℤ) + 3) := by
  ext z
  obtain ⟨x, y⟩ := z
  rw [BaseMask.mem_stairEven_raw_iff, mem_stairF (by omega : (2 : ℤ) ≤ 2 * (k : ℤ) + 3)]
  simp only [BaseMask.StairEvenCorner]
  omega

/-- `CV1`: the even staircase covers its `H` set, with the periods of `⟨1, 2k + 3⟩`. -/
theorem cover_stair (k : ℕ) :
    QuotientCover (HSet ⟨1, 2 * (k : ℤ) + 3⟩) (perU ⟨1, 2 * (k : ℤ) + 3⟩) (perV ⟨1, 2 * (k : ℤ) + 3⟩) := by
  rw [← stair_eq k]
  have hden : BaseMask.stairEven.Valid (2 * (k : ℤ) + 3) :=
    (show 3 ≤ 2 * (k : ℤ) + 3 ∧ (2 * (k : ℤ) + 3) % 2 = 1 from ⟨by omega, by omega⟩)
  have hraw := stairEven_raw_cover hden
  rw [stairEven_raw_sites_eq k] at hraw
  exact quotientCover_of_covers (Fraction.mk 1 (2 * (k : ℤ) + 3)) _ hraw

end FLatticePaper.Tiles.SiteCovers
