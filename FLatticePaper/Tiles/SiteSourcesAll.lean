import FLatticePaper.Tiles.SitePairScope
import FLatticePaper.Tiles.SiteBaseDischarge
import FLatticePaper.Tiles.SiteHullOdd
import FLatticePaper.Tiles.SiteHullEven
import FLatticePaper.Tiles.SiteBoundaryInner
import FLatticePaper.Tiles.EncPieces
import FLatticePaper.Tiles.PairCoverW0
import FLatticePaper.Tiles.PairCoverW1
import FLatticePaper.Tiles.PairEvenCover

/-! Task 53, clause (b): the four-string predicate of every standard tile, with `marksIn` the only hypothesis.

Every field of `SiteInduction.SourceHyps` except `marksIn` is now proved for all words:
* `baseEq`, `baseCov`: `SiteBaseDischarge` (the literal base tiles).
* `encOdd`, `encEven`, `propOdd`, `propEven`: the pair-indexed statements `PairHyps` for every proper pair, instantiated
  at the parents of a non-base word by `SitePairScope`.
* `hull`, `hullE`: `SiteHullOdd.hull_odd`, `SiteHullEven.hull_even`.
* `boundary`: `SiteBoundaryInner.boundary_odd`, `boundary_even`.

So `standard_fourStrings` applies to the record built here, and its only assumption is the mark containment. -/

namespace FLatticePaper.Tiles.SiteSourcesAll

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.SitePairScope FLatticePaper.Tiles.SiteStrings

/-- The odd-child cover for every proper pair: the two flags of `propOdd_W0` and `propOdd_W1`. -/
theorem propOdd_all (p q : Fraction) (h : ParPair p q)
    (_hp : QuotientCover (HSet p) (perU p) (perV p)) (_hq : QuotientCover (HSet q) (perU q) (perV q)) :
    QuotientCover (oddChildS (decide (p.det q = 1)) (HSet p) (HSet q) p q)
      (perU ((Parents.mk p q).current .odd)) (perV ((Parents.mk p q).current .odd)) := by
  obtain ⟨pn, pd⟩ := p
  obtain ⟨qn, qd⟩ := q
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  dsimp only at h1 h2 h3 h4 h5 h6 h7
  have hC : (Parents.mk ⟨pn, pd⟩ ⟨qn, qd⟩).current .odd = ⟨pn + qn, pd + qd⟩ := by
    simp [Parents.current, Parents.combine]
  rw [hC]
  have hodd0 : (pn + pd) % 2 = 1 := h5
  have heven0 : (qn + qd) % 2 = 0 := h6
  have hodd : (pd + pn) % 2 = 1 := by omega
  have heven : (qd + qn) % 2 = 0 := by omega
  rcases h7 with hD | hD
  · have hδ : pd * qn - pn * qd = -1 := by
      simp only [Fraction.det] at hD; linarith
    rw [decide_eq_true (show Fraction.det ⟨pn, pd⟩ ⟨qn, qd⟩ = 1 from hD)]
    exact PairCoverW1.propOdd_W1 pd pn qd qn (by omega) h2 (by omega) h4 hδ hodd heven
  · have hδ : pd * qn - pn * qd = 1 := by
      simp only [Fraction.det] at hD; linarith
    rw [decide_eq_false (by intro hc; simp only [Fraction.det] at hc; linarith)]
    exact PairCoverW0.propOdd_W0 pd pn qd qn (by omega) h2 (by omega) h4 hδ hodd heven

/-- The even-child cover for every proper pair (`propEven_any`, which needs no hypothesis on the parents). -/
theorem propEven_all (p q : Fraction) (h : ParPair p q)
    (_hp : QuotientCover (HSet p) (perU p) (perV p)) (_hq : QuotientCover (HSet q) (perU q) (perV q)) :
    QuotientCover (evenChildS (decide (p.det q = 1)) (HSet p) (HSet q) p q)
      (perU ((Parents.mk p q).current .even)) (perV ((Parents.mk p q).current .even)) := by
  obtain ⟨pn, pd⟩ := p
  obtain ⟨qn, qd⟩ := q
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  dsimp only at h1 h2 h3 h4 h5 h6 h7
  have hdet : pd * qn - pn * qd = 1 ∨ pd * qn - pn * qd = -1 := by
    rcases h7 with hD | hD
    · right; simp only [Fraction.det] at hD; linarith
    · left; simp only [Fraction.det] at hD; linarith
  have hodd0 : (pn + pd) % 2 = 1 := h5
  have heven0 : (qn + qd) % 2 = 0 := h6
  have hodd : (pd + pn) % 2 = 1 := by omega
  have heven : (qd + qn) % 2 = 0 := by omega
  exact FLatticePaper.Tiles.PairEvenCover.propEven_any pd pn qd qn (by omega) h2 (by omega) h4 hdet hodd heven

/-- The pair-indexed statements of `PairHyps`, for every proper pair. -/
theorem pairHyps_all : PairHyps where
  encOdd := FLatticePaper.Tiles.EncPieces.encOdd_all
  encEven := FLatticePaper.Tiles.EncPieces.encEven_all
  propOdd := fun p q h hp hq => propOdd_all p q h hp hq
  propEven := fun p q h hp hq => propEven_all p q h hp hq

/-- The source record of the induction, with `marksIn` as the only argument. -/
theorem sourceHyps_of_marks
    (hM : ∀ w : Word, marksOdd w ⊆ ((oddTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) ∧
      marksEven w ⊆ ((evenTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ))) : SourceHyps where
  baseEq := fun w hb => FLatticePaper.Tiles.SiteBaseDischarge.baseEq_all w hb
  baseCov := fun w hb => FLatticePaper.Tiles.SiteBaseDischarge.baseCov_all w hb
  encOdd := fun w hw => encOdd_word pairHyps_all w hw
  encEven := fun w hw => encEven_word pairHyps_all w hw
  propOdd := fun w hw hp hq => propOdd_word pairHyps_all w hw hp hq
  propEven := fun w hw hp hq => propEven_word pairHyps_all w hw hp hq
  hull := fun w _ z hz hu => FLatticePaper.Tiles.SiteHullOdd.hull_odd w z hz hu
  hullE := fun w _ z hz hu => FLatticePaper.Tiles.SiteHullEven.hull_even w z hz hu
  marksIn := hM
  boundary := fun w => ⟨FLatticePaper.Tiles.SiteBoundaryInner.boundary_odd w,
    FLatticePaper.Tiles.SiteBoundaryInner.boundary_even w⟩

/-- **Clause (b)**: the four-string predicate of every standard tile; `marksIn` is the only hypothesis. -/
theorem standard_fourStrings_all
    (hM : ∀ w : Word, marksOdd w ⊆ ((oddTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) ∧
      marksEven w ⊆ ((evenTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)))
    (w : Word) (par : Bool) : StandardFourStrings w par :=
  standard_fourStrings (sourceHyps_of_marks hM) w par

end FLatticePaper.Tiles.SiteSourcesAll
