import FLatticePaper.Plane.Induction.TwosLaplacianTile
import FLatticePaper.Construction.LadderCoverage

/-! Every site of the twos plane has a native lattice copy (task 72). The raw cover of the odd ladder
(`ladderOdd_raw_cover`) covers the quarter turn of the site by a raw site, and the quarter turn carries the twos period lattice
`⟨U, V⟩` onto the ladder deck (`L U = (1-a, a+1)` is the transverse, `L V = -(2a, 2)` minus the kernel). The native box is exactly
the set of points whose quarter turn is raw (`nativeT_rot_raw`, and its converse below). -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey

/-- The converse of `nativeT_rot_raw`: a point whose quarter turn is raw is native. -/
theorem native_of_raw_rot {a : ℤ} {u : Site}
    (hu : QuarterTurn.counterclockwise.mapSite (2 * a, 1) u ∈ (BaseMask.ladderOdd.raw a).sites) :
    NativeT a u.1 u.2 := by
  rw [quarterTurn_offset_apply, BaseMask.mem_ladderOdd_raw_iff] at hu
  obtain ⟨x, y⟩ := u
  simp only [NativeT]
  simp only at hu
  omega

/-- Every site has a native lattice copy: `c - (i U + l V)` is native for some `i, l`. -/
theorem native_copy_exists {a : ℤ} (ha : a % 2 = 0) (hvalid : BaseMask.ladderOdd.Valid a) (c : Site) :
    ∃ u : Site, AliasOf a c u ∧ NativeT a u.1 u.2 := by
  obtain ⟨q, hq, hspan⟩ := ladderOdd_raw_cover hvalid (QuarterTurn.counterclockwise.mapSite (2 * a, 1) c)
  rw [reciprocalLadderDeck_eq ha] at hspan
  obtain ⟨k₁, k₂, hk⟩ := hspan
  have h1 := congrArg Prod.fst hk
  have h2 := congrArg Prod.snd hk
  simp only [PeriodDeck.combine, quarterTurn_offset_apply, Prod.fst_sub, Prod.snd_sub] at h1 h2
  refine ⟨(c.1 - k₂ * (a + 1) + 2 * (-k₁), c.2 - k₂ * (a - 1) - 2 * a * (-k₁)), ⟨k₂, -k₁, rfl⟩, ?_⟩
  apply native_of_raw_rot
  have hrot : QuarterTurn.counterclockwise.mapSite (2 * a, 1)
      (c.1 - k₂ * (a + 1) + 2 * (-k₁), c.2 - k₂ * (a - 1) - 2 * a * (-k₁)) = q := by
    rw [quarterTurn_offset_apply]
    apply Prod.ext
    · simp only
      linarith
    · simp only
      linarith
  rw [hrot]
  exact hq

end FLatticePaper.TwosEPolicy
