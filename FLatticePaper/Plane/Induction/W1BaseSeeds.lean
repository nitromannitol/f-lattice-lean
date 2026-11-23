import FLatticePaper.Plane.Induction.TwosStrips
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.W1OddZero
import FLatticePaper.Plane.Induction.W1SeedFields

/-! # Task 76: the base seeds, reduced to one value of the reciprocal field

The base words of the induction are the words `u` whose conjugate `conjWord u` is not proper, i.e. `u = 2^k x 3^j` (`x ∈ {1, 2}`), whose
conjugate is the threes word `3^k`. Their `SeedFields` come from `seedFields_of_conj` once `SeedFields (3^k)` is known. This module proves
`SeedFields (3^k)` from the reciprocal field lemmas, except for one value of the reciprocal field:

* `even_zero`: the even line `t = 1 − d` of `3^k` (`d = 2k+3`) is the lower boundary of the reciprocal zero zone `1 − d ≤ t ≤ 2d`
  (`reciprocal_zero_zone`), so the even seed is proved outright.
* `odd_zero`: the odd line `t_p = 1 − d` (`parentN = k+1`, `parentD = k+2`) contains the even point `(−2, 0)` for every `k`; by
  `odd_zero_of_seed` the whole line is one orbit, and the quarter turn at `(−2, 0)` is `G(0, −3) − h₀(0, −3)`. So the odd seed reduces to the
  single value `G(0, −3) = −1` (`h₀(0, −3) = −1`), a named base input (numerically `G_k(0, −3) = −1` for `k ≤ 4`). The packet strips and
  periods do not determine it (the zone and reflection routes do not reach `(0, −3)`); it needs the raw tile of the reciprocal field. -/

namespace FLatticePaper.W1BaseSeeds

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Seeds

/-- The harmonic value at the seed of the odd line: `h₀(0, −3) = −1`. -/
theorem harmonicGrid_zero_neg_three : harmonicGrid (0, -3) = -1 := by
  unfold harmonicGrid
  norm_num

/-- **The even seed of `3^k`** (proved): the even line `t = 1 − d` is the lower boundary of the reciprocal zero zone. -/
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

/-- The odd seed of `3^k` reduces to the value of the reciprocal field at `(0, −3)`. -/
theorem threes_odd_seed (k : ℕ)
    (hv : standardField (List.replicate k Digit.three) (0, -3) = -1) :
    quarterTurnField (standardField (List.replicate k Digit.three)) (-2, 0) = 0 := by
  rw [FLatticePaper.W1ZeroStrip.quarterTurn_eq_sub]
  show standardField (List.replicate k Digit.three) (0, -3) - harmonicGrid (0, -3) = 0
  rw [hv, harmonicGrid_zero_neg_three]
  norm_num

/-- **`SeedFields (3^k)`** (task 76): the even seed is proved; the odd seed follows from the single value `hv`. -/
theorem seedFields_threes (k : ℕ)
    (hv : standardField (List.replicate k Digit.three) (0, -3) = -1) :
    SeedFields (List.replicate k Digit.three) where
  even_zero := threes_even_zero k
  odd_zero := by
    intro x hx hxl
    refine FLatticePaper.W1OddZero.odd_zero_of_seed (List.replicate k Digit.three) (reciprocal_packet k)
      (-2, 0) x (by decide) ?_ hx hxl (threes_odd_seed k hv)
    have hcd := child_threes_explicit k
    unfold parentN parentD
    rw [hcd]
    simp only
    omega

/-- **`SeedFields` at a base word** (task 76): a proper word `w` whose conjugate is the threes word `3^k` has both seeds, from
`seedFields_of_conj` (with the conjugate's strong estimates) and `seedFields_threes`, given the single reciprocal value `hv`. -/
theorem seedFields_base {w : Word} (h : ∃ x ∈ w, x ≠ Digit.three) (k : ℕ)
    (hconj : conjWord w = List.replicate k Digit.three) (hS : StrongEstimates (conjWord w))
    (hv : standardField (List.replicate k Digit.three) (0, -3) = -1) : SeedFields w := by
  have hpar : SeedFields (conjWord w) := by
    rw [hconj]
    exact seedFields_threes k hv
  exact FLatticePaper.W1SeedFields.seedFields_of_conj h hS hpar

end FLatticePaper.W1BaseSeeds
