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

theorem native_box {a : ℤ} (ha : 4 ≤ a) {p : Site} (hp : NativeT a p.1 p.2) :
    -1 ≤ p.1 ∧ p.1 ≤ a + 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 3 * a - 2 := by
  simp only [NativeT] at hp
  omega

set_option maxHeartbeats 400000 in
/-- The coefficient `I` of a difference of two native points is in `[-1, 1]`. -/
theorem native_pair_I {a I L : ℤ} (ha : 4 ≤ a) {p q : Site} (hp : NativeT a p.1 p.2) (hq : NativeT a q.1 q.2)
    (hD1 : p.1 - q.1 = I * (a + 1) - 2 * L) (hD2 : p.2 - q.2 = I * (a - 1) + 2 * a * L) :
    -1 ≤ I ∧ I ≤ 1 := by
  obtain ⟨hp1, hp1', hp2, hp2'⟩ := native_box ha hp
  obtain ⟨hq1, hq1', hq2, hq2'⟩ := native_box ha hq
  have hT : I * (2 * a * a + 4 * a - 2) = 2 * a * (p.1 - q.1) + 2 * (p.2 - q.2) := by
    rw [hD1, hD2]
    ring
  have hT0 : 0 < 2 * a * a + 4 * a - 2 := by nlinarith
  constructor
  · by_contra hc
    have h1 : I * (2 * a * a + 4 * a - 2) ≤ -2 * (2 * a * a + 4 * a - 2) :=
      mul_le_mul_of_nonneg_right (by omega) hT0.le
    have h2 : 2 * a * (-(a + 2)) ≤ 2 * a * (p.1 - q.1) := mul_le_mul_of_nonneg_left (by omega) (by omega)
    nlinarith
  · by_contra hc
    have h1 : 2 * (2 * a * a + 4 * a - 2) ≤ I * (2 * a * a + 4 * a - 2) :=
      mul_le_mul_of_nonneg_right (by omega) hT0.le
    have h2 : 2 * a * (p.1 - q.1) ≤ 2 * a * (a + 2) := mul_le_mul_of_nonneg_left (by omega) (by omega)
    nlinarith

set_option maxHeartbeats 400000 in
/-- The coefficient `L` of a difference of two native points is in `[-1, 1]`, given `I` is. -/
theorem native_pair_L {a I L : ℤ} (ha : 4 ≤ a) (hI1 : -1 ≤ I) (hI2 : I ≤ 1) {p q : Site}
    (hp : NativeT a p.1 p.2) (hq : NativeT a q.1 q.2) (hD2 : p.2 - q.2 = I * (a - 1) + 2 * a * L) :
    -1 ≤ L ∧ L ≤ 1 := by
  obtain ⟨_, _, hp2, hp2'⟩ := native_box ha hp
  obtain ⟨_, _, hq2, hq2'⟩ := native_box ha hq
  constructor
  · by_contra hc
    have h1 : 2 * a * L ≤ 2 * a * (-2) := mul_le_mul_of_nonneg_left (by omega) (by omega)
    have h2 : I * (a - 1) ≤ 1 * (a - 1) := mul_le_mul_of_nonneg_right hI2 (by omega)
    nlinarith
  · by_contra hc
    have h1 : 2 * a * 2 ≤ 2 * a * L := mul_le_mul_of_nonneg_left (by omega) (by omega)
    have h2 : (-1) * (a - 1) ≤ I * (a - 1) := mul_le_mul_of_nonneg_right hI1 (by omega)
    nlinarith

set_option maxHeartbeats 400000 in
/-- Two native points differing by `I U + L V` with `I, L ∈ {-1, 0, 1}` are equal, or one of them is free. The free member is
`p` for `(I, L) = (-1, 0)` and `(0, -1)`, and `q` for `(1, 0)` and `(0, 1)`; the other four offsets do not occur. -/
theorem native_pair_cases {a I L : ℤ} (ha : 4 ≤ a) (hI1 : -1 ≤ I) (hI2 : I ≤ 1) (hL1 : -1 ≤ L) (hL2 : L ≤ 1)
    {p q : Site} (hp : NativeT a p.1 p.2) (hq : NativeT a q.1 q.2)
    (hD1 : p.1 - q.1 = I * (a + 1) - 2 * L) (hD2 : p.2 - q.2 = I * (a - 1) + 2 * a * L) :
    (I = 0 ∧ L = 0) ∨ FreeSite a p.1 p.2 ∨ FreeSite a q.1 q.2 := by
  simp only [NativeT] at hp hq
  interval_cases I <;> interval_cases L
  · exfalso
    omega
  · right
    left
    simp only [FreeSite, FreeHSite, FreeVSite]
    omega
  · exfalso
    omega
  · right
    left
    simp only [FreeSite, FreeHSite, FreeVSite]
    omega
  · left
    exact ⟨rfl, rfl⟩
  · right
    right
    simp only [FreeSite, FreeHSite, FreeVSite]
    omega
  · exfalso
    omega
  · right
    right
    simp only [FreeSite, FreeHSite, FreeVSite]
    omega
  · exfalso
    omega

set_option maxHeartbeats 400000 in
theorem native_pair_zero_or_free {a I L : ℤ} (ha : 4 ≤ a) {p q : Site} (hp : NativeT a p.1 p.2)
    (hq : NativeT a q.1 q.2) (hD1 : p.1 - q.1 = I * (a + 1) - 2 * L) (hD2 : p.2 - q.2 = I * (a - 1) + 2 * a * L) :
    (I = 0 ∧ L = 0) ∨ FreeSite a p.1 p.2 ∨ FreeSite a q.1 q.2 := by
  obtain ⟨hI1, hI2⟩ := native_pair_I ha hp hq hD1 hD2
  obtain ⟨hL1, hL2⟩ := native_pair_L ha hI1 hI2 hp hq hD2
  exact native_pair_cases ha hI1 hI2 hL1 hL2 hp hq hD1 hD2

/-- A non-free class has at most one native lattice copy. -/
theorem native_alias_unique {a : ℤ} (ha : 4 ≤ a) {c u u' : Site} (hu : AliasOf a c u) (hu' : AliasOf a c u')
    (hn : NativeT a u.1 u.2) (hn' : NativeT a u'.1 u'.2) (hnf : ¬ FreeClass a c) : u = u' := by
  obtain ⟨i, l, hi⟩ := hu
  obtain ⟨i', l', hi'⟩ := hu'
  have h := native_pair_zero_or_free (I := i' - i) (L := l' - l) ha hn hn'
    (by rw [hi, hi']; ring) (by rw [hi, hi']; ring)
  rcases h with ⟨h0, h1⟩ | hf | hf'
  · have hii : i = i' := by omega
    have hll : l = l' := by omega
    rw [hi, hi', hii, hll]
  · exact absurd ⟨u, ⟨i, l, hi⟩, hf⟩ hnf
  · exact absurd ⟨u', ⟨i', l', hi'⟩, hf'⟩ hnf

end FLatticePaper.TwosEPolicy
