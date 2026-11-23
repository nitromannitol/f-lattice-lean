import FLatticePaper.Tiles.SiteScope

/-! Task 53, item 2 (scope): the source's statements for proper pairs imply the word-indexed hypotheses of `SourceHyps`.

`PairHyps` is the source's scope: for every proper parity-compatible pair `p` (odd type) and `q` (even type) with determinant `±1`,
the six-source inclusions and the cover conclusions hold, with the orientation flag `decide (det p q = 1)`. At a non-base word the parent
pair is such a pair (`SiteScope.proper_of_not_base`, `det_parentsAt`), and its orientation flag is the phase `phase w == 1`
(`det = 2·phase − 1`). So each word-indexed field of `SourceHyps` is an instance of the pair-indexed statement. The numerical check of
these pair statements (denominators ≤ 25, 231 proper pairs, `scratchpad/prop_proper.py`) is the evidence for them; they are not proved here. -/

namespace FLatticePaper.Tiles.SitePairScope

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SiteScope

/-- A proper parity-compatible determinant-one pair: `p` odd, `q` even, both with `0 < num < den`, and `det = ±1`. -/
def ParPair (p q : Fraction) : Prop :=
  0 < p.num ∧ p.num < p.den ∧ 0 < q.num ∧ q.num < q.den ∧ p.Odd ∧ q.Even ∧
    (p.det q = 1 ∨ p.det q = -1)

/-- The source's statements, for all proper parity-compatible pairs. -/
structure PairHyps : Prop where
  encOdd : ∀ p q : Fraction, ParPair p q →
    oddChildS (decide (p.det q = 1)) (HSet p) (HSet q) p q ⊆ HSet ((Parents.mk p q).current .odd)
  encEven : ∀ p q : Fraction, ParPair p q →
    evenChildS (decide (p.det q = 1)) (HSet p) (HSet q) p q ⊆ HSet ((Parents.mk p q).current .even)
  propOdd : ∀ p q : Fraction, ParPair p q → QuotientCover (HSet p) (perU p) (perV p) →
    QuotientCover (HSet q) (perU q) (perV q) →
    QuotientCover (oddChildS (decide (p.det q = 1)) (HSet p) (HSet q) p q)
      (perU ((Parents.mk p q).current .odd)) (perV ((Parents.mk p q).current .odd))
  propEven : ∀ p q : Fraction, ParPair p q → QuotientCover (HSet p) (perU p) (perV p) →
    QuotientCover (HSet q) (perU q) (perV q) →
    QuotientCover (evenChildS (decide (p.det q = 1)) (HSet p) (HSet q) p q)
      (perU ((Parents.mk p q).current .even)) (perV ((Parents.mk p q).current .even))

/-- The parent pair of a non-base word is a proper parity-compatible pair. -/
theorem parPair_of_not_base (w : FLatticePaper.Farey.Word) (hw : ¬ IsBase w) :
    ParPair (parentsAt w).odd (parentsAt w).even := by
  obtain ⟨h1, h2, h3, h4⟩ := proper_of_not_base w hw
  have hv := parentsAt_valid w
  have hd := det_parentsAt w
  have hlt : phase w < 2 := by unfold phase; omega
  refine ⟨h1, h2, h3, h4, hv.odd_parity, hv.even_parity, ?_⟩
  omega

/-- The orientation flag of a word is its phase. -/
theorem flag_eq_phase (w : FLatticePaper.Farey.Word) :
    decide ((parentsAt w).odd.det (parentsAt w).even = 1) = (phase w == 1) := by
  have hd := det_parentsAt w
  have hlt : phase w < 2 := by unfold phase; omega
  rw [hd]
  by_cases h : phase w = 1
  · simp [h]
  · have h0 : phase w = 0 := by omega
    simp [h0]

theorem encOdd_word (P : PairHyps) (w : FLatticePaper.Farey.Word) (hw : ¬ IsBase w) :
    oddChildS (phase w == 1) (HSet (parentsAt w).odd) (HSet (parentsAt w).even) (parentsAt w).odd (parentsAt w).even ⊆
      HSet (curO w) := by
  have h := P.encOdd _ _ (parPair_of_not_base w hw)
  rw [flag_eq_phase] at h
  exact h

theorem encEven_word (P : PairHyps) (w : FLatticePaper.Farey.Word) (hw : ¬ IsBase w) :
    evenChildS (phase w == 1) (HSet (parentsAt w).odd) (HSet (parentsAt w).even) (parentsAt w).odd (parentsAt w).even ⊆
      HSet (curE w) := by
  have h := P.encEven _ _ (parPair_of_not_base w hw)
  rw [flag_eq_phase] at h
  exact h

theorem propOdd_word (P : PairHyps) (w : FLatticePaper.Farey.Word) (hw : ¬ IsBase w)
    (hp : QuotientCover (HSet (parentsAt w).odd) (perU (parentsAt w).odd) (perV (parentsAt w).odd))
    (hq : QuotientCover (HSet (parentsAt w).even) (perU (parentsAt w).even) (perV (parentsAt w).even)) :
    QuotientCover (oddChildS (phase w == 1) (HSet (parentsAt w).odd) (HSet (parentsAt w).even) (parentsAt w).odd
      (parentsAt w).even) (perU (curO w)) (perV (curO w)) := by
  have h := P.propOdd _ _ (parPair_of_not_base w hw) hp hq
  rw [flag_eq_phase] at h
  exact h

theorem propEven_word (P : PairHyps) (w : FLatticePaper.Farey.Word) (hw : ¬ IsBase w)
    (hp : QuotientCover (HSet (parentsAt w).odd) (perU (parentsAt w).odd) (perV (parentsAt w).odd))
    (hq : QuotientCover (HSet (parentsAt w).even) (perU (parentsAt w).even) (perV (parentsAt w).even)) :
    QuotientCover (evenChildS (phase w == 1) (HSet (parentsAt w).odd) (HSet (parentsAt w).even) (parentsAt w).odd
      (parentsAt w).even) (perU (curE w)) (perV (curE w)) := by
  have h := P.propEven _ _ (parPair_of_not_base w hw) hp hq
  rw [flag_eq_phase] at h
  exact h

end FLatticePaper.Tiles.SitePairScope
