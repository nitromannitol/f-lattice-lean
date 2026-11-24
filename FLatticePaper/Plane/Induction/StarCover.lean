import Mathlib.Data.Int.Notation

/-!
# The covering of the grade torus by the three kinds of full stars (STRONG_PRICE §3, combinatorial core)

For a child `n/d` (odd `n`, `d`), write `t = n x − d y` and `s = (d+n) x + (d−n) y` for the grades of a site `(x, y)`, and
`T = d² + 2dn − n²`. The deck translates act on the grades by `(t, s) ↦ (t − jT, s + iT)`, so a deck classification of a star is a
statement on the torus `[0, T) × [0, T)`.

A site with grades `(t, s)` is of one of three kinds: an interior site of the closed polygon `E`, an H-band site, or a V source site
(the strip `3 − 2d ≤ s ≤ 2(d+n) − 1`, where the harmonic grid is forced by the packet's strips). `OkSite` is their disjunction.

`box_cover` is the covering: for every grade point `(t, s)` of the box with `s` even, one of two translates `(t, s) ↦ (t − T, s)` or
`(t, s) ↦ (t + 2T, s − T)` classifies the three sites of the star of `(t, s)`. The translate is `(t + 2T, s − T)` exactly for odd `t`
in the top band `T − (d − n) + 2 ≤ s ≤ T − 2`, and `(t − T, s)` otherwise.

The hypotheses `3 ≤ n` and `n + 4 ≤ d` are the arithmetic of proper nonbase children (STRONG_PRICE; numerically checked on the proper words
of length at most five). They are not derived here.
-/

namespace FLatticePaper.Induction.StarCover

/-- The three kinds of a site with grades `(t, s)`: the closed polygon `E`, the H-band, or the V strip. -/
def OkSite (n d T t s : ℤ) : Prop :=
  (t % 2 = 0 ∧ 2 - T ≤ t ∧ t ≤ d + n - 2 ∧ 0 ≤ s ∧ s ≤ T + 2 * n) ∨
  (t % 2 = 1 ∧ n - T ≤ t ∧ t ≤ d ∧ 2 - d + n ≤ s ∧ s ≤ T + d + n - 2) ∨
  (t % 2 = 0 ∧ 2 * n ≤ s ∧ s ≤ T) ∨
  (t % 2 = 1 ∧ d + n ≤ s ∧ s ≤ T - (d - n)) ∨
  (3 - 2 * d ≤ s ∧ s ≤ 2 * (d + n) - 1)

/-- Even-centre case: the translate `(t, s) ↦ (t − T, s)` classifies the star of an even `(t, s)` in the box. -/
theorem box_even (n d T t s : ℤ) (hno : n % 2 = 1) (hdo : d % 2 = 1) (hn : 3 ≤ n) (hnd : n + 4 ≤ d)
    (_hT : 2 * d + 2 * n ≤ T) (hTe : T % 2 = 0)
    (ht : t % 2 = 0) (ht0 : 0 ≤ t) (htT : t < T) (hs0 : 0 ≤ s) (hsT : s < T) (hs2 : s % 2 = 0) :
    OkSite n d T (t - T) s ∧ OkSite n d T (t - T - n) (s - (d + n)) ∧
      OkSite n d T (t - T + n) (s + (d + n)) := by
  unfold OkSite
  refine ⟨?_, ?_, ?_⟩
  · by_cases h : 2 * n ≤ s
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
  · by_cases h : s ≤ 2 * (d + n) - 1 + (d + n)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))
  · by_cases h : s ≤ T - 2 * d
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))
    · exact Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, by omega⟩)

/-- Odd centre in the top band: the translate `(t, s) ↦ (t + 2T, s − T)` makes all three sites V sites. -/
theorem box_odd_band (n d T t s : ℤ) (hno : n % 2 = 1) (hdo : d % 2 = 1) (hn : 3 ≤ n) (_hnd : n + 4 ≤ d)
    (_hT : 2 * d + 2 * n ≤ T) (hTe : T % 2 = 0)
    (_ht : t % 2 = 1) (_ht0 : 0 ≤ t) (_htT : t < T) (_hs0 : 0 ≤ s) (hsT : s < T) (hs2 : s % 2 = 0)
    (hband : T - (d - n) + 2 ≤ s ∧ s ≤ T - 2) :
    OkSite n d T (t + 2 * T) (s - T) ∧ OkSite n d T (t + 2 * T + d) (s - T - (d - n)) ∧
      OkSite n d T (t + 2 * T - d) (s - T + (d - n)) := by
  unfold OkSite
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inr ?_))), Or.inr (Or.inr (Or.inr (Or.inr ?_))),
    Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩ <;> omega

/-- Odd centre outside the top band: the translate `(t, s) ↦ (t − T, s)` classifies the star. -/
theorem box_odd_out (n d T t s : ℤ) (hno : n % 2 = 1) (hdo : d % 2 = 1) (hn : 3 ≤ n) (hnd : n + 4 ≤ d)
    (_hT : 2 * d + 2 * n ≤ T) (hTe : T % 2 = 0)
    (ht : t % 2 = 1) (ht0 : 0 ≤ t) (htT : t < T) (hs0 : 0 ≤ s) (hsT : s < T) (hs2 : s % 2 = 0)
    (hband : ¬ (T - (d - n) + 2 ≤ s ∧ s ≤ T - 2)) :
    OkSite n d T (t - T) s ∧ OkSite n d T (t - T + d) (s - (d - n)) ∧
      OkSite n d T (t - T - d) (s + (d - n)) := by
  unfold OkSite
  refine ⟨?_, ?_, ?_⟩
  · by_cases h : d + n ≤ s
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
  · by_cases h : d - n ≤ s
    · exact Or.inl ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
  · by_cases h : 2 * n ≤ s + (d - n)
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))

/-- **The covering of the box.** For a grade point `(t, s)` of the box `[0, T) × [0, T)` with `s` even, the three sites of its star are
classified by one translate: the translate `(t, s) ↦ (t − T, s)` for even `t`, and for odd `t` the translate `(t, s) ↦ (t + 2T, s − T)`
in the top band and `(t, s) ↦ (t − T, s)` outside it. The sites of the star of an odd centre are `(t ± d, s ∓ (d − n))`, and those of
an even centre are `(t ∓ n, s ∓ (d + n))`. -/
theorem box_cover (n d T t s : ℤ) (hno : n % 2 = 1) (hdo : d % 2 = 1) (hn : 3 ≤ n) (hnd : n + 4 ≤ d)
    (hT : 2 * d + 2 * n ≤ T) (hTe : T % 2 = 0)
    (ht0 : 0 ≤ t) (htT : t < T) (hs0 : 0 ≤ s) (hsT : s < T) (hs2 : s % 2 = 0) :
    (t % 2 = 0 ∧ OkSite n d T (t - T) s ∧ OkSite n d T (t - T - n) (s - (d + n)) ∧
        OkSite n d T (t - T + n) (s + (d + n))) ∨
    (t % 2 = 1 ∧ T - (d - n) + 2 ≤ s ∧ s ≤ T - 2 ∧
        OkSite n d T (t + 2 * T) (s - T) ∧ OkSite n d T (t + 2 * T + d) (s - T - (d - n)) ∧
          OkSite n d T (t + 2 * T - d) (s - T + (d - n))) ∨
    (t % 2 = 1 ∧ ¬ (T - (d - n) + 2 ≤ s ∧ s ≤ T - 2) ∧
        OkSite n d T (t - T) s ∧ OkSite n d T (t - T + d) (s - (d - n)) ∧
          OkSite n d T (t - T - d) (s + (d - n))) := by
  have hpar : t % 2 = 0 ∨ t % 2 = 1 := by omega
  rcases hpar with ht | ht
  · obtain ⟨h1, h2, h3⟩ := box_even n d T t s hno hdo hn hnd hT hTe ht ht0 htT hs0 hsT hs2
    exact Or.inl ⟨ht, h1, h2, h3⟩
  · by_cases hb : T - (d - n) + 2 ≤ s ∧ s ≤ T - 2
    · obtain ⟨h1, h2, h3⟩ := box_odd_band n d T t s hno hdo hn hnd hT hTe ht ht0 htT hs0 hsT hs2 hb
      exact Or.inr (Or.inl ⟨ht, hb.1, hb.2, h1, h2, h3⟩)
    · obtain ⟨h1, h2, h3⟩ := box_odd_out n d T t s hno hdo hn hnd hT hTe ht ht0 htT hs0 hsT hs2 hb
      exact Or.inr (Or.inr ⟨ht, hb, h1, h2, h3⟩)

end FLatticePaper.Induction.StarCover
