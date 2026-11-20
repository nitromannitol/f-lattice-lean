import FLatticePaper.Plane.Recurrence
import Mathlib.Tactic.Ring

/-! The manuscript's checkerboard endpoints. -/

namespace FLatticePaper

/-- The endpoint function `g₀₋₁` in `lemma:checkerboard_recurrence`. -/
def zeroEndpoint (x : Site) : ℤ :=
  -(x.2 * (x.2 + 1) / 2)

theorem laplacian_zeroEndpoint (x : Site) :
    laplacian zeroEndpoint x = if EvenSite x then 0 else -1 := by
  by_cases he : EvenSite x
  · simp [laplacian, zeroEndpoint, incomingNeg, incomingPos, he]
  · simp only [laplacian, zeroEndpoint, incomingNeg, incomingPos, if_neg he]
    rw [show (x.2 - 1) * (x.2 - 1 + 1) = x.2 * (x.2 + 1) + (-x.2) * 2 by ring,
      show (x.2 + 1) * (x.2 + 1 + 1) = x.2 * (x.2 + 1) + (x.2 + 1) * 2 by ring,
      Int.add_mul_ediv_right _ _ (by decide), Int.add_mul_ediv_right _ _ (by decide)]
    omega

/-- Moving west lowers the first coordinate, and either vertical input to
an odd site lowers the parity term without changing that coordinate. -/
def checkerboardRank (x : Site) : ℤ := 2 * x.1 + (x.1 + x.2) % 2

theorem isBurningRank_of_checkerboard {g : Field}
    (hg : ∀ x, laplacian g x = if EvenSite x then 0 else -1) :
    IsBurningRank g checkerboardRank := by
  intro x
  by_cases he : EvenSite x
  · right
    refine ⟨by simpa [he] using hg x, Or.inl ?_⟩
    simp only [checkerboardRank, incomingNeg, if_pos he]
    omega
  · left
    refine ⟨by simpa [he] using hg x, ?_, ?_⟩
    · simp only [checkerboardRank, incomingNeg, if_neg he]
      simp only [EvenSite] at he
      omega
    · simp only [checkerboardRank, incomingPos, if_neg he]
      simp only [EvenSite] at he
      omega

theorem zeroEndpoint_rank : IsBurningRank zeroEndpoint checkerboardRank :=
  isBurningRank_of_checkerboard laplacian_zeroEndpoint

theorem zeroEndpoint_allowed (X : Finset Site) (hX : X.Nonempty) :
    Allowed (fun x => laplacian zeroEndpoint x + 1) X :=
  zeroEndpoint_rank.allowed X hX

theorem zeroEndpoint_finiteComparison {f : Field} (X : Finset Site) (c : ℤ)
    (hf : ∀ x ∈ X, laplacian f x ≤ 0)
    (hb : ∀ y ∈ incomingBoundary X, zeroEndpoint y - f y ≤ c) :
    ∀ x ∈ X, zeroEndpoint x - f x ≤ c :=
  zeroEndpoint_rank.finiteComparison X c hf hb

theorem zeroEndpoint_recurrent : Recurrent zeroEndpoint := zeroEndpoint_rank.recurrent

/-- The endpoint function `g₁₋₁` in `lemma:checkerboard_recurrence`. -/
def oneEndpoint (site : Site) : ℤ := -((site.2 - site.1) ^ 2 / 4)

private theorem square_quarter_even (half : ℤ) : (2 * half) ^ 2 / 4 = half ^ 2 := by
  rw [show (2 * half) ^ 2 = half ^ 2 * 4 by ring, Int.mul_ediv_cancel _ (by decide)]

private theorem square_quarter_odd (half : ℤ) : (2 * half + 1) ^ 2 / 4 = half ^ 2 + half := by
  rw [show (2 * half + 1) ^ 2 = 1 + (half ^ 2 + half) * 4 by ring,
    Int.add_mul_ediv_right _ _ (by decide)]
  omega

/-- Modulo four, an integer square has the residue of its parity. -/
theorem four_mul_square_div_four (value : ℤ) : 4 * (value ^ 2 / 4) = value ^ 2 - value % 2 := by
  let half := value / 2
  by_cases hparity : value % 2 = 0
  · have hvalue : value = 2 * half := by dsimp [half]; omega
    rw [hparity, hvalue, square_quarter_even]
    ring
  · have hparity' : value % 2 = 1 := by omega
    have hvalue : value = 2 * half + 1 := by dsimp [half]; omega
    rw [hparity', hvalue, square_quarter_odd]
    ring

private theorem neg_square_quarter_secondDiff (value : ℤ) :
    (-((value - 1) ^ 2 / 4) - -(value ^ 2 / 4)) +
      (-((value + 1) ^ 2 / 4) - -(value ^ 2 / 4)) = -(value % 2) := by
  let half := value / 2
  by_cases hparity : value % 2 = 0
  · have hcenter : value = 2 * half := by dsimp [half]; omega
    have hprev : value - 1 = 2 * (half - 1) + 1 := by omega
    have hnext : value + 1 = 2 * half + 1 := by omega
    rw [hparity, hprev, hnext, hcenter, square_quarter_even, square_quarter_odd, square_quarter_odd]
    ring
  · have hparity' : value % 2 = 1 := by omega
    have hcenter : value = 2 * half + 1 := by dsimp [half]; omega
    have hprev : value - 1 = 2 * half := by omega
    have hnext : value + 1 = 2 * (half + 1) := by omega
    rw [hparity', hprev, hnext, hcenter, square_quarter_odd, square_quarter_even, square_quarter_even]
    ring

theorem laplacian_oneEndpoint (site : Site) :
    laplacian oneEndpoint site = if EvenSite site then 0 else -1 := by
  have hdiff := neg_square_quarter_secondDiff (site.2 - site.1)
  by_cases hsite : EvenSite site
  · simp only [laplacian, incomingNeg, incomingPos, oneEndpoint, if_pos hsite]
    rw [show site.2 - (site.1 - 1) = site.2 - site.1 + 1 by omega,
      show site.2 - (site.1 + 1) = site.2 - site.1 - 1 by omega]
    unfold EvenSite at hsite
    omega
  · simp only [laplacian, incomingNeg, incomingPos, oneEndpoint, if_neg hsite]
    rw [show site.2 - 1 - site.1 = site.2 - site.1 - 1 by omega,
      show site.2 + 1 - site.1 = site.2 - site.1 + 1 by omega]
    unfold EvenSite at hsite
    omega

theorem oneEndpoint_rank : IsBurningRank oneEndpoint checkerboardRank :=
  isBurningRank_of_checkerboard laplacian_oneEndpoint

theorem oneEndpoint_recurrent : Recurrent oneEndpoint := oneEndpoint_rank.recurrent

end FLatticePaper
