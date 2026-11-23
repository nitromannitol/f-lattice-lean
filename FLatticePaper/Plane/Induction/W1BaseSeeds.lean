import FLatticePaper.Plane.Induction.TwosStrips
import FLatticePaper.Plane.Induction.TwosReciprocal
import FLatticePaper.Plane.Induction.TwosField
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.W1OddZero
import FLatticePaper.Plane.Induction.W1SeedFields

/-! # Tasks 76 and 77: the base seeds of the threes words, from the explicit reciprocal formula

The base words of the induction are the words `u` whose conjugate `conjWord u` is not proper, i.e. `u = 2^k x 3^j` (`x ∈ {1, 2}`), whose
conjugate is the threes word `3^k`. Their `SeedFields` come from `seedFields_of_conj` once `SeedFields (3^k)` is known.

* `reciprocal_neg_three`: the reciprocal field takes the value `−1` at `(0, −3)` for every `k`. Proof: the deck reduction
  `(0, −3) = (1, m−1) + combine (−1) (−1)` with `m = 2k+3` (`reciprocalField_reduction`, at the tile point `(1, m−1)`), the literal
  staircase value `stairEvenValue m (1, m−1) = −(k+1)(2k+1)`, and `stairEvenConstantV m = −m(k+3)`, `transverseGrade (1/m) y = m y₂ − y₁`,
  `periodDenominator (1/m) = m² + 2m − 1`; the resulting identity `2 R = −2` is a polynomial identity in `k`.
* `seedFields_threes k`: `SeedFields (3^k)` (no hypothesis): the even seed is the zero zone of the reciprocal field; the odd seed follows from
  the value `−1` at `(0, −3)` through `odd_zero_of_seed`.
* `seedFields_base`: `SeedFields w` for a proper `w` whose conjugate is `3^k`. -/

namespace FLatticePaper.W1BaseSeeds

open Farey FLatticePaper FLatticePaper.Induction Construction FLatticePaper.W1Seeds

/-- **The reciprocal field at `(0, −3)`** (task 77): `reciprocalField k (0, −3) = −1` for every `k`, from the explicit reduction at the
tile point `(1, m−1)` with `m = 2k+3` and deck coefficients `(−1, −1)`. -/
theorem reciprocal_neg_three (k : ℕ) : reciprocalField k (0, -3) = -1 := by
  have hk : (0 : ℤ) ≤ (k : ℤ) := by positivity
  have hy : ((1 : ℤ), ((2 * (k : ℤ) + 3) - 1)) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
    BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, Or.inr ⟨by omega, by omega⟩⟩
  have hpar : (1 + (2 * (k : ℤ) + 3)) % 2 = 0 := by omega
  have hred : ((0 : ℤ), (-3 : ℤ)) = ((1 : ℤ), ((2 * (k : ℤ) + 3) - 1)) +
      (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine (-1) (-1) := by
    refine Prod.ext ?_ ?_ <;>
      simp [Fraction.modifiedDeck, Fraction.periodMultiplicity, PeriodDeck.combine, Fraction.unmodifiedDeck, hpar] <;>
      ring
  have h := reciprocalField_reduction k hy hred
  have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((1 : ℤ), ((2 * (k : ℤ) + 3) - 1)) := by
    unfold BaseMask.StairEvenCorner
    omega
  have hdiv : ((2 * (k : ℤ) + 3) - 1) * (((2 * (k : ℤ) + 3) - 1) - 1) / 2 = (k + 1) * (2 * (k : ℤ) + 1) := by
    rw [show ((2 * (k : ℤ) + 3) - 1) * (((2 * (k : ℤ) + 3) - 1) - 1) = 2 * ((k + 1) * (2 * (k : ℤ) + 1)) by ring]
    exact Int.mul_ediv_cancel_left _ two_ne_zero
  have hval : BaseMask.stairEvenValue (2 * (k : ℤ) + 3) ((1 : ℤ), ((2 * (k : ℤ) + 3) - 1)) =
      -((k + 1) * (2 * (k : ℤ) + 1)) := by
    unfold BaseMask.stairEvenValue
    rw [if_neg hc, hdiv]
    norm_num
  have hcV : stairEvenConstantV (2 * (k : ℤ) + 3) = -((2 * (k : ℤ) + 3) * (k + 3)) := by
    rw [stairEvenConstantV_eq]
    congr 1
    rw [show (2 * (k : ℤ) + 3) * ((2 * (k : ℤ) + 3) + 3) = 2 * ((2 * (k : ℤ) + 3) * (k + 3)) by ring]
    exact Int.mul_ediv_cancel_left _ two_ne_zero
  rw [hval, hcV] at h
  simp only [Fraction.transverseGrade, Fraction.periodDenominator] at h
  have key : 2 * reciprocalField k (0, -3) = 2 * (-1) := by
    rw [h]
    ring
  linarith

/-- **The threes value** (task 77): the standard field of `3^k` takes the value `−1` at `(0, −3)`. -/
theorem standardField_threes_neg_three (k : ℕ) :
    standardField (List.replicate k Digit.three) (0, -3) = -1 := by
  rw [standardField_threes]
  exact reciprocal_neg_three k

/-- The harmonic value at the seed of the odd line: `h₀(0, −3) = −1`. -/
theorem harmonicGrid_zero_neg_three : harmonicGrid (0, -3) = -1 := by
  unfold harmonicGrid
  norm_num

/-- **The even seed of `3^k`**: the even line `t = 1 − d` is the lower boundary of the reciprocal zero zone. -/
theorem threes_even_zero (k : ℕ) :
    ∀ z : Site, EvenSite z →
      (frameAt (List.replicate k Digit.three)).tGrade z =
        2 - ((frameAt (List.replicate k Digit.three)).child.den + (frameAt (List.replicate k Digit.three)).child.num) →
        standardField (List.replicate k Digit.three) z = 0 := by
  intro z _ ht
  have hd : (frameAt (List.replicate k Digit.three)).child.den = 2 * (k : ℤ) + 3 := by
    rw [child_threes_explicit k]
  have hn : (frameAt (List.replicate k Digit.three)).child.num = 1 := by
    rw [child_threes_explicit k]
  have ht' : z.1 - (2 * (k : ℤ) + 3) * z.2 = 1 - (2 * (k : ℤ) + 3) := by
    have h := ht
    unfold ChildFrame.tGrade at h
    rw [hd, hn] at h
    linarith
  exact reciprocal_zero_zone k z (by linarith) (by linarith)

/-- The odd seed of `3^k`: the quarter turn of `standardField (3^k)` vanishes at the even point `(−2, 0)`. -/
theorem threes_odd_seed (k : ℕ) :
    quarterTurnField (standardField (List.replicate k Digit.three)) (-2, 0) = 0 := by
  rw [FLatticePaper.W1ZeroStrip.quarterTurn_eq_sub]
  show standardField (List.replicate k Digit.three) (0, -3) - harmonicGrid (0, -3) = 0
  rw [standardField_threes_neg_three, harmonicGrid_zero_neg_three]
  norm_num

/-- **`SeedFields (3^k)`** (tasks 76, 77): both seeds, with no hypothesis beyond `k`. -/
theorem seedFields_threes (k : ℕ) : SeedFields (List.replicate k Digit.three) where
  even_zero := threes_even_zero k
  odd_zero := by
    intro x hx hxl
    refine FLatticePaper.W1OddZero.odd_zero_of_seed (List.replicate k Digit.three) (reciprocal_packet k)
      (-2, 0) x (by decide) ?_ hx hxl (threes_odd_seed k)
    have hcd := child_threes_explicit k
    unfold parentN parentD
    rw [hcd]
    simp only
    omega

/-- **`SeedFields` at a base word** (task 76): a proper word `w` whose conjugate is the threes word `3^k` has both seeds, from
`seedFields_of_conj` with the conjugate's strong estimates. -/
theorem seedFields_base {w : Word} (h : ∃ x ∈ w, x ≠ Digit.three) (k : ℕ)
    (hconj : conjWord w = List.replicate k Digit.three) (hS : StrongEstimates (conjWord w)) : SeedFields w := by
  have hpar : SeedFields (conjWord w) := by
    rw [hconj]
    exact seedFields_threes k
  exact FLatticePaper.W1SeedFields.seedFields_of_conj h hS hpar

/-- **`SeedFields` of the twos word `2^(k+1)`** (task 78): its conjugate is the threes word `3^k`, so `seedFields_of_conj` gives both
seeds from `SeedFields (3^k)` (proved for every `k`), given the strong estimates of `3^k`. -/
theorem seedFields_two_succ (k : ℕ) (hS : StrongEstimates (List.replicate k Digit.three)) :
    SeedFields (List.replicate (k + 1) Digit.two) := by
  have hc : conjWord (List.replicate (k + 1) Digit.two) = List.replicate k Digit.three := conjWord_replicate_two k
  exact FLatticePaper.W1SeedFields.seedFields_of_conj
    ⟨Digit.two, List.mem_replicate.mpr ⟨by omega, rfl⟩, by decide⟩
    (by rw [hc]; exact hS) (by rw [hc]; exact seedFields_threes k)

/-- **`SeedFields` at a word whose conjugate is the twos word `2^(k+1)`** (task 78): the seeds of the conjugate are those of
`2^(k+1)`, from `seedFields_two_succ`, and `seedFields_of_conj` transfers them to `w`. -/
theorem seedFields_twos_conj {w : Word} (h : ∃ x ∈ w, x ≠ Digit.three) (k : ℕ)
    (hconj : conjWord w = List.replicate (k + 1) Digit.two) (hS : StrongEstimates (conjWord w))
    (hS3 : StrongEstimates (List.replicate k Digit.three)) : SeedFields w := by
  have hpar : SeedFields (conjWord w) := by
    rw [hconj]
    exact seedFields_two_succ k hS3
  exact FLatticePaper.W1SeedFields.seedFields_of_conj h hS hpar

end FLatticePaper.W1BaseSeeds
