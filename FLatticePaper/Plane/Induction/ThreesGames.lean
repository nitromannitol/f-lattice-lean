import FLatticePaper.Plane.Induction.EPolicyFinal
import FLatticePaper.Plane.Induction.GamesPolicy
import FLatticePaper.Plane.Induction.RankWithValues

/-! Task w3, D: the games with a deck rank at the pure words `3^k`.

The canonical games of the reciprocal field (`EPolicyFinal.canonicalGames k`) have, for each sign, the policy `ePolicy (2k+3) η`
(definitionally). The rank of that policy with the kernel and transverse increments `(−1, η)` of `frameAt (3^k)` is
`rank_threes_of_values`, so the games with a deck rank at `3^k` follow. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem gamesWithRank_threes (k : ℕ) : GamesWithRank (List.replicate k Digit.three) := by
  have hf : frameAt (List.replicate k Digit.three) = reciprocalFrame k := by
    rfl
  have hF : standardField (List.replicate k Digit.three) = reciprocalField k := standardField_threes k
  unfold GamesWithRank
  rw [hf, hF]
  refine ⟨EPolicy.canonicalGames k, fun η hη => ?_⟩
  have h := EPolicy.rank_threes_of_values k (EPolicy.valuesAll k) η hη
  rw [hf] at h
  unfold RankWithIncrements at h
  obtain ⟨rank, lam, hlam, hstr, hU, hV⟩ := h
  refine ⟨rank, -lam, η * lam, ?_, ?_, ?_⟩
  · intro z
    have := hU z
    linarith
  · intro z
    have := hV z
    linarith
  · intro x i hx
    exact hstr x i hx

end FLatticePaper.Induction
