import FLatticePaper.Rank
import Mathlib.Tactic.Ring

/-! Comparison for the manuscript's endpoint at `0/1`. -/

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

end FLatticePaper
