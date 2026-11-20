import FLatticePaper.Graph

/-! Decreasing inputs and finite comparison for the physical F-lattice. -/

namespace FLatticePaper

/-- At a site of Laplacian `-1`, both physical inputs decrease the rank.
At a site of Laplacian `0`, at least one physical input decreases it. -/
def IsBurningRank {α : Type*} [LT α] (g : Field) (rank : Site → α) : Prop :=
  ∀ x,
    (laplacian g x = -1 ∧ rank (incomingNeg x) < rank x ∧ rank (incomingPos x) < rank x) ∨
    (laplacian g x = 0 ∧ (rank (incomingNeg x) < rank x ∨ rank (incomingPos x) < rank x))

theorem IsBurningRank.superharmonic {α : Type*} [LT α] {g : Field} {rank : Site → α}
    (hr : IsBurningRank g rank) : Superharmonic g := by
  intro x
  rcases hr x with ⟨h, -, -⟩ | ⟨h, -⟩ <;> omega

/-- A least-rank vertex in any nonempty finite induced subgraph is allowed
for the height `1 + Δg`. -/
theorem IsBurningRank.allowed {α : Type*} [LinearOrder α] {g : Field} {rank : Site → α}
    (hr : IsBurningRank g rank) (X : Finset Site) (hX : X.Nonempty) :
    Allowed (fun x => laplacian g x + 1) X := by
  obtain ⟨x, hx, hmin⟩ := X.exists_min_image rank hX
  have outside {y : Site} (hy : rank y < rank x) : y ∉ X :=
    fun hmem => (not_lt_of_ge (hmin y hmem)) hy
  refine ⟨x, hx, ?_⟩
  unfold incomingDegree
  rcases hr x with ⟨h, hn, hp⟩ | ⟨h, hn | hp⟩
  · simp [h, outside hn, outside hp]
  · simp only [h, outside hn, if_false]
    split <;> omega
  · simp only [h, outside hp, if_false]
    split <;> omega

/-- Absence of a finite forbidden set implies finite comparison. The comparison
holds for every finite set, and the competitor needs to be superharmonic on it. -/
theorem finiteComparison_of_allowed {g f : Field} (X : Finset Site) (c : ℤ)
    (hg : ∀ Y : Finset Site, Y.Nonempty → Allowed (fun x => laplacian g x + 1) Y)
    (hf : ∀ x ∈ X, laplacian f x ≤ 0)
    (hb : ∀ y ∈ incomingBoundary X, g y - f y ≤ c) :
    ∀ x ∈ X, g x - f x ≤ c := by
  intro a ha
  by_contra! hbad
  let d : Field := fun x => g x - f x
  obtain ⟨b, hbX, hmax⟩ := X.exists_max_image d ⟨a, ha⟩
  have hlarge : c < d b := lt_of_lt_of_le hbad (hmax a ha)
  let K := X.filter fun x => d x = d b
  have hbK : b ∈ K := Finset.mem_filter.mpr ⟨hbX, rfl⟩
  obtain ⟨x, hxK, hxAllowed⟩ := hg K ⟨b, hbK⟩
  obtain ⟨hxX, hxMax⟩ := Finset.mem_filter.mp hxK
  have inputBound (y : Site) (hy : Edge y x) :
      d y ≤ d x + ((if y ∈ K then 1 else 0) - 1) := by
    by_cases hk : y ∈ K
    · have hyMax := (Finset.mem_filter.mp hk).2
      simp [hk, hxMax, hyMax]
    · simp only [hk, if_false]
      by_cases hyX : y ∈ X
      · have hle := hmax y hyX
        have hne : d y ≠ d b := fun heq => hk (Finset.mem_filter.mpr ⟨hyX, heq⟩)
        omega
      · have hbd : d y ≤ c := hb y ⟨hyX, x, hxX, hy⟩
        omega
  have hn := inputBound (incomingNeg x) (Or.inl rfl)
  have hp := inputBound (incomingPos x) (Or.inr rfl)
  have hfg := hf x hxX
  simp only [laplacian, incomingDegree] at hxAllowed hfg
  dsimp only [d] at hn hp
  omega

/-- A physical decreasing rank gives the finite comparison in the definition
of recurrence, in pointwise boundary-bound form. -/
theorem IsBurningRank.finiteComparison {α : Type*} [LinearOrder α]
    {g f : Field} {rank : Site → α} (hr : IsBurningRank g rank)
    (X : Finset Site) (c : ℤ) (hf : ∀ x ∈ X, laplacian f x ≤ 0)
    (hb : ∀ y ∈ incomingBoundary X, g y - f y ≤ c) :
    ∀ x ∈ X, g x - f x ≤ c :=
  finiteComparison_of_allowed X c hr.allowed hf hb

end FLatticePaper
