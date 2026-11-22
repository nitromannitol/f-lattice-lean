import FLatticePaper.Plane.AlternateMidpoint

/-! A rank for a smaller permit relation is a rank for a larger one (task 34, part (i)).

The archive's strict-rank policy keeps both inputs at a black site and one input at a white site, the chosen one being
a lower input whose slip increment is nonpositive ("D is nonincreasing on every kept edge", STRONG_PRICE section 1/
MIDPOINT_LEMMA line 8). Such a policy relation lies inside `slipPermits`, and the monotonicity below transfers the
constrained rank from the policy to `slipPermits`. -/

namespace FLatticePaper

/-- A constrained burning rank for a permit relation is one for every larger permit relation. -/
theorem IsConstrainedBurningRank.mono {α : Type*} [LT α] {field : Field} {rank : Site → α}
    {Q P : Site → Site → Prop} (hQ : IsConstrainedBurningRank field rank Q)
    (hle : ∀ center input, Q center input → P center input) :
    IsConstrainedBurningRank field rank P := by
  intro center
  rcases hQ center with ⟨hlap, hn, hp⟩ | ⟨hlap, hn | hp⟩
  · exact Or.inl ⟨hlap, ⟨hle _ _ hn.1, hn.2⟩, ⟨hle _ _ hp.1, hp.2⟩⟩
  · exact Or.inr ⟨hlap, Or.inl ⟨hle _ _ hn.1, hn.2⟩⟩
  · exact Or.inr ⟨hlap, Or.inr ⟨hle _ _ hp.1, hp.2⟩⟩

end FLatticePaper
