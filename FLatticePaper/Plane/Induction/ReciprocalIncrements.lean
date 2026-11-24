import FLatticePaper.Plane.Induction.TwosReciprocal
import FLatticePaper.Construction.StaircaseCoverage

/-! The increments of the reciprocal field `reciprocalField k = standardField (3^k)` (child `1/d`, `d = 2k+3`), as an explicit
formula on native representatives.

A site `z` is *native with representative* `(y, i, j)` when `y` is a raw site of the near-one staircase tile and
`z = y + combine i j` (`combine i j = i K + j T`, the kernel and the transverse period of `1/d`). By
`reciprocalField_reduction`, `2 · F z = 2 · stairEvenValue y + 2 j (−transverseGrade y + cV) − T j (j−1)`.

`reciprocal_native_step`: if `y` and `y + e` are both raw and `z = y + combine i j`, then the increment of `F` along `e` at `z` is
the raw increment `stairEvenValue (y + e) − stairEvenValue y` minus `j (d e₂ − e₁)`. The raw increment is explicit (the
stair value is `−C(y₂,2) + min(y₁−1,0) + [corner]`), so this is the shared evaluator; the covering of every site by such a
representative is a separate statement. -/

namespace FLatticePaper.Induction

open Farey Construction

/-- The grade increment of `1/d` along a unit step: `transverseGrade (y + e) − transverseGrade y = d e₂ − e₁`. -/
theorem transverseGrade_step (d : ℤ) (y e : Site) :
    (Fraction.mk 1 d).transverseGrade (y + e) - (Fraction.mk 1 d).transverseGrade y = d * e.2 - e.1 := by
  unfold Fraction.transverseGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- **The native increment.** For raw `y`, `y + e` of the staircase tile and `z = y + combine i j`, the increment of
`reciprocalField k` along `e` at `z` is the raw increment minus `j` times the grade increment. -/
theorem reciprocal_native_step (k : ℕ) {z y e : Site} {i j : ℤ}
    (hy : y ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites)
    (hye : y + e ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites)
    (hz : z = y + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j) :
    reciprocalField k (z + e) - reciprocalField k z =
      BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (y + e) - BaseMask.stairEvenValue (2 * (k : ℤ) + 3) y -
        j * ((2 * (k : ℤ) + 3) * e.2 - e.1) := by
  have h1 := reciprocalField_reduction k hy hz
  have hze : z + e = (y + e) + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j := by
    rw [hz]
    abel
  have h2 := reciprocalField_reduction k hye hze
  have hg := transverseGrade_step (2 * (k : ℤ) + 3) y e
  have key : 2 * (reciprocalField k (z + e) - reciprocalField k z) =
      2 * (BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (y + e) - BaseMask.stairEvenValue (2 * (k : ℤ) + 3) y -
        j * ((2 * (k : ℤ) + 3) * e.2 - e.1)) := by
    linear_combination h2 - h1 - (2 * j) * hg
  exact mul_left_cancel₀ two_ne_zero key


/-! ### The raw tile in coordinates, and the strong covering -/

/-- The raw sites of the near-one staircase tile of `1/d`, in coordinates. -/
def RawMem (d x y : ℤ) : Prop :=
  (2 - d ≤ x ∧ x ≤ d) ∧ (0 ≤ y ∧ y ≤ d + 1) ∧
    ((x = 0 ∧ y = 0) ∨ (x = 2 ∧ y = d + 1) ∨ (1 ≤ x + y ∧ x + y ≤ d + 2))

theorem raw_mem_iff (d x y : ℤ) :
    (x, y) ∈ (BaseMask.stairEven.raw d).sites ↔ RawMem d x y := by
  rw [BaseMask.mem_stairEven_raw_iff]
  unfold RawMem BaseMask.StairEvenCorner
  simp only
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by tauto⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by tauto⟩

set_option maxHeartbeats 400000 in
/-- The strong covering of the raw tile for the step `e = (1, 0)`: a shift `c ∈ [(0, 0), (1, 0), (0, -1)]` of `y` has `y − c` and `y − c + e`
both raw. -/
theorem strongCover_right (d x y : ℤ) (hd : 3 ≤ d) (hodd : d % 2 = 1) (hy : RawMem d x y) :
    (RawMem d (x - ((0) * d + (0) * (1 - d))) (y - ((0) + (0) * (1 + d))) ∧ RawMem d (x - ((0) * d + (0) * (1 - d)) + (1)) (y - ((0) + (0) * (1 + d)) + (0)))
      ∨ (RawMem d (x - ((1) * d + (0) * (1 - d))) (y - ((1) + (0) * (1 + d))) ∧ RawMem d (x - ((1) * d + (0) * (1 - d)) + (1)) (y - ((1) + (0) * (1 + d)) + (0)))
      ∨ (RawMem d (x - ((0) * d + (-1) * (1 - d))) (y - ((0) + (-1) * (1 + d))) ∧ RawMem d (x - ((0) * d + (-1) * (1 - d)) + (1)) (y - ((0) + (-1) * (1 + d)) + (0))) := by
  unfold RawMem at hy ⊢
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := hy
  rcases h5 with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩ | hb
  all_goals omega

set_option maxHeartbeats 400000 in
/-- The strong covering of the raw tile for the step `e = (-1, 0)`: a shift `c ∈ [(0, 0), (-1, 0), (0, 1)]` of `y` has `y − c` and `y − c + e`
both raw. -/
theorem strongCover_left (d x y : ℤ) (hd : 3 ≤ d) (hodd : d % 2 = 1) (hy : RawMem d x y) :
    (RawMem d (x - ((0) * d + (0) * (1 - d))) (y - ((0) + (0) * (1 + d))) ∧ RawMem d (x - ((0) * d + (0) * (1 - d)) + (-1)) (y - ((0) + (0) * (1 + d)) + (0)))
      ∨ (RawMem d (x - ((-1) * d + (0) * (1 - d))) (y - ((-1) + (0) * (1 + d))) ∧ RawMem d (x - ((-1) * d + (0) * (1 - d)) + (-1)) (y - ((-1) + (0) * (1 + d)) + (0)))
      ∨ (RawMem d (x - ((0) * d + (1) * (1 - d))) (y - ((0) + (1) * (1 + d))) ∧ RawMem d (x - ((0) * d + (1) * (1 - d)) + (-1)) (y - ((0) + (1) * (1 + d)) + (0))) := by
  unfold RawMem at hy ⊢
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := hy
  rcases h5 with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩ | hb
  all_goals omega

set_option maxHeartbeats 400000 in
/-- The strong covering of the raw tile for the step `e = (0, 1)`: a shift `c ∈ [(0, 0), (1, 0), (0, 1)]` of `y` has `y − c` and `y − c + e`
both raw. -/
theorem strongCover_up (d x y : ℤ) (hd : 3 ≤ d) (hodd : d % 2 = 1) (hy : RawMem d x y) :
    (RawMem d (x - ((0) * d + (0) * (1 - d))) (y - ((0) + (0) * (1 + d))) ∧ RawMem d (x - ((0) * d + (0) * (1 - d)) + (0)) (y - ((0) + (0) * (1 + d)) + (1)))
      ∨ (RawMem d (x - ((1) * d + (0) * (1 - d))) (y - ((1) + (0) * (1 + d))) ∧ RawMem d (x - ((1) * d + (0) * (1 - d)) + (0)) (y - ((1) + (0) * (1 + d)) + (1)))
      ∨ (RawMem d (x - ((0) * d + (1) * (1 - d))) (y - ((0) + (1) * (1 + d))) ∧ RawMem d (x - ((0) * d + (1) * (1 - d)) + (0)) (y - ((0) + (1) * (1 + d)) + (1))) := by
  unfold RawMem at hy ⊢
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := hy
  rcases h5 with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩ | hb
  all_goals omega

set_option maxHeartbeats 400000 in
/-- The strong covering of the raw tile for the step `e = (0, -1)`: a shift `c ∈ [(0, 0), (-1, 0), (0, -1)]` of `y` has `y − c` and `y − c + e`
both raw. -/
theorem strongCover_down (d x y : ℤ) (hd : 3 ≤ d) (hodd : d % 2 = 1) (hy : RawMem d x y) :
    (RawMem d (x - ((0) * d + (0) * (1 - d))) (y - ((0) + (0) * (1 + d))) ∧ RawMem d (x - ((0) * d + (0) * (1 - d)) + (0)) (y - ((0) + (0) * (1 + d)) + (-1)))
      ∨ (RawMem d (x - ((-1) * d + (0) * (1 - d))) (y - ((-1) + (0) * (1 + d))) ∧ RawMem d (x - ((-1) * d + (0) * (1 - d)) + (0)) (y - ((-1) + (0) * (1 + d)) + (-1)))
      ∨ (RawMem d (x - ((0) * d + (-1) * (1 - d))) (y - ((0) + (-1) * (1 + d))) ∧ RawMem d (x - ((0) * d + (-1) * (1 - d)) + (0)) (y - ((0) + (-1) * (1 + d)) + (-1))) := by
  unfold RawMem at hy ⊢
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := hy
  rcases h5 with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩ | hb
  all_goals omega

/-- The combine of `1/d` for odd `d`: `i K + j T` with `K = (d,1)`, `T = (1−d,1+d)`. -/
theorem combine_eq (d : ℤ) (hodd : d % 2 = 1) (i j : ℤ) :
    (Fraction.mk 1 d).modifiedDeck.combine i j = (i * d + j * (1 - d), i + j * (1 + d)) := by
  have h := reciprocalEvenDeck_eq hodd
  unfold reciprocalEvenDeck at h
  rw [h]
  ext <;> simp [PeriodDeck.combine]

/-- Every site has a raw representative of the staircase tile, up to the period lattice of `1/d`. -/
theorem raw_cover_rep (k : ℕ) (z : Site) :
    ∃ y : Site, RawMem (2 * (k : ℤ) + 3) y.1 y.2 ∧
      ∃ i j : ℤ, z = y + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j := by
  obtain ⟨rep, hrep, hspan⟩ := stairEven_raw_cover (stairEven_valid_reciprocal k) z
  obtain ⟨i, j, hij⟩ := hspan
  refine ⟨rep, (raw_mem_iff _ _ _).mp ?_, i, j, ?_⟩
  · simpa using hrep
  · have h : z - rep = (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j := hij
    calc z = (z - rep) + rep := by abel
      _ = _ := by rw [h]; abel

/-- The existential form of the strong covering for `e = (1, 0)`. -/
theorem strongCoverE_right (d x y : ℤ) (hd : 3 ≤ d) (hodd : d % 2 = 1) (hy : RawMem d x y) :
    ∃ a b : ℤ, RawMem d (x - (a * d + b * (1 - d))) (y - (a + b * (1 + d))) ∧
      RawMem d (x - (a * d + b * (1 - d)) + (1)) (y - (a + b * (1 + d)) + (0)) := by
  rcases strongCover_right d x y hd hodd hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨0, 0, h1, h2⟩
  · exact ⟨1, 0, h1, h2⟩
  · exact ⟨0, -1, h1, h2⟩

/-- The existential form of the strong covering for `e = (-1, 0)`. -/
theorem strongCoverE_left (d x y : ℤ) (hd : 3 ≤ d) (hodd : d % 2 = 1) (hy : RawMem d x y) :
    ∃ a b : ℤ, RawMem d (x - (a * d + b * (1 - d))) (y - (a + b * (1 + d))) ∧
      RawMem d (x - (a * d + b * (1 - d)) + (-1)) (y - (a + b * (1 + d)) + (0)) := by
  rcases strongCover_left d x y hd hodd hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨0, 0, h1, h2⟩
  · exact ⟨-1, 0, h1, h2⟩
  · exact ⟨0, 1, h1, h2⟩

/-- The existential form of the strong covering for `e = (0, 1)`. -/
theorem strongCoverE_up (d x y : ℤ) (hd : 3 ≤ d) (hodd : d % 2 = 1) (hy : RawMem d x y) :
    ∃ a b : ℤ, RawMem d (x - (a * d + b * (1 - d))) (y - (a + b * (1 + d))) ∧
      RawMem d (x - (a * d + b * (1 - d)) + (0)) (y - (a + b * (1 + d)) + (1)) := by
  rcases strongCover_up d x y hd hodd hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨0, 0, h1, h2⟩
  · exact ⟨1, 0, h1, h2⟩
  · exact ⟨0, 1, h1, h2⟩

/-- The existential form of the strong covering for `e = (0, -1)`. -/
theorem strongCoverE_down (d x y : ℤ) (hd : 3 ≤ d) (hodd : d % 2 = 1) (hy : RawMem d x y) :
    ∃ a b : ℤ, RawMem d (x - (a * d + b * (1 - d))) (y - (a + b * (1 + d))) ∧
      RawMem d (x - (a * d + b * (1 - d)) + (0)) (y - (a + b * (1 + d)) + (-1)) := by
  rcases strongCover_down d x y hd hodd hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨0, 0, h1, h2⟩
  · exact ⟨-1, 0, h1, h2⟩
  · exact ⟨0, -1, h1, h2⟩

/-- Every site `z` and unit step `e` have a raw representative `y` with `y` and `y + e` both raw. -/
theorem strong_rep_unit (k : ℕ) (z e : Site)
    (he : e = (1, 0) ∨ e = (-1, 0) ∨ e = (0, 1) ∨ e = (0, -1)) :
    ∃ y : Site, RawMem (2 * (k : ℤ) + 3) y.1 y.2 ∧ RawMem (2 * (k : ℤ) + 3) (y.1 + e.1) (y.2 + e.2) ∧
      ∃ i j : ℤ, z = y + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j := by
  obtain ⟨y0, hy0, i0, j0, hz0⟩ := raw_cover_rep k z
  have hd : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have hodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  rcases he with rfl | rfl | rfl | rfl
  · obtain ⟨a, b, h1, h2⟩ := strongCoverE_right _ y0.1 y0.2 hd hodd hy0
    refine ⟨(y0.1 - (a * _ + b * (1 - _)), y0.2 - (a + b * (1 + _))), h1, h2, i0 + a, j0 + b, ?_⟩
    rw [hz0]
    simp only [combine_eq _ hodd]
    ext <;> simp <;> ring
  · obtain ⟨a, b, h1, h2⟩ := strongCoverE_left _ y0.1 y0.2 hd hodd hy0
    refine ⟨(y0.1 - (a * _ + b * (1 - _)), y0.2 - (a + b * (1 + _))), h1, h2, i0 + a, j0 + b, ?_⟩
    rw [hz0]
    simp only [combine_eq _ hodd]
    ext <;> simp <;> ring
  · obtain ⟨a, b, h1, h2⟩ := strongCoverE_up _ y0.1 y0.2 hd hodd hy0
    refine ⟨(y0.1 - (a * _ + b * (1 - _)), y0.2 - (a + b * (1 + _))), h1, h2, i0 + a, j0 + b, ?_⟩
    rw [hz0]
    simp only [combine_eq _ hodd]
    ext <;> simp <;> ring
  · obtain ⟨a, b, h1, h2⟩ := strongCoverE_down _ y0.1 y0.2 hd hodd hy0
    refine ⟨(y0.1 - (a * _ + b * (1 - _)), y0.2 - (a + b * (1 + _))), h1, h2, i0 + a, j0 + b, ?_⟩
    rw [hz0]
    simp only [combine_eq _ hodd]
    ext <;> simp <;> ring

/-- **The shared increment evaluator at every site.** For every site `z` and unit step `e` there are a raw site `y` with `y`
and `y + e` raw and `z = y + combine i j`, and the increment of `reciprocalField k` along `e` at `z` is the raw stair increment
minus `j (d e₂ − e₁)`, with `d = 2k+3`. -/
theorem reciprocal_increment (k : ℕ) (z e : Site)
    (he : e = (1, 0) ∨ e = (-1, 0) ∨ e = (0, 1) ∨ e = (0, -1)) :
    ∃ y : Site, ∃ i j : ℤ, y ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites ∧
      y + e ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites ∧
      z = y + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j ∧
      reciprocalField k (z + e) - reciprocalField k z =
        BaseMask.stairEvenValue (2 * (k : ℤ) + 3) (y + e) - BaseMask.stairEvenValue (2 * (k : ℤ) + 3) y -
          j * ((2 * (k : ℤ) + 3) * e.2 - e.1) := by
  obtain ⟨y, hy, hye, i, j, hz⟩ := strong_rep_unit k z e he
  have hy' : y ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites := (raw_mem_iff _ _ _).mpr hy
  have hye' : y + e ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites := (raw_mem_iff _ _ _).mpr hye
  exact ⟨y, i, j, hy', hye', hz, reciprocal_native_step k hy' hye' hz⟩

end FLatticePaper.Induction
