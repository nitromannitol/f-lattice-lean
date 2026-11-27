import FLatticePaper.Construction.NearOneBaseCases
import FLatticePaper.Construction.LadderRotation

/-! # The rotated doubled standard staircase equals the translated near-one doubled height on its tile

Surgical manuscript, `lemma:doubled_staircase_laplacian` (E18, doubled identity): for even `d ≥ 4`, the rotated standard
doubled height `rotateLadderField d F` (with `F` the standard height on `paperLadderTile d`) agrees with
`paperNearLadderValue d (x + e₂)` at every `x` such that `x + e₂` lies in `paperNearLadderTile d`. The quarter turn
`x ↦ (2d − x₂, x₁ + 1)` sends that set into `paperLadderTile d`. -/

namespace FLatticePaper.Construction

open Farey

theorem rotateLadder_mapSite_pointwise (d : ℤ) (x : Site) :
    QuarterTurn.counterclockwise.mapSite (2 * d, 1) x = (2 * d - x.2, x.1 + 1) := by
  apply Prod.ext
  · change -x.2 + 2 * d = 2 * d - x.2
    omega
  · rfl

/-- The quarter turn of a near-one doubled tile point (translated by `e₂`) lies in the standard doubled tile. -/
theorem ladderTile_of_nearLadder_tile_point {d : ℤ} {x : Site} (hx : (x.1, x.2 + 1) ∈ paperNearLadderTile d) :
    (2 * d - x.2, x.1 + 1) ∈ paperLadderTile d := by
  obtain ⟨x1, x2⟩ := x
  simp only [paperNearLadderTile, paperLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC,
    paperNearLadderD, paperLadderA, paperLadderB, paperLadderC, paperLadderD, Set.mem_sdiff, Set.mem_union,
    Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx ⊢
  omega

/-- **Pointwise rotation identity (doubled).** On the translated near-one doubled tile, the rotated standard doubled height
is the near-one height at `x + e₂`. -/
theorem rotateLadderField_eq_nearLadder_tile {d : ℤ} (hd : 4 ≤ d ∧ d % 2 = 0) (F : Field)
    (hF : ∀ z ∈ paperLadderTile d, F z = paperLadderValue d z) (x : Site)
    (hx : (x.1, x.2 + 1) ∈ paperNearLadderTile d) :
    rotateLadderField d F x = paperNearLadderValue d (x.1, x.2 + 1) := by
  have hmem := ladderTile_of_nearLadder_tile_point hx
  unfold rotateLadderField
  rw [rotateLadder_mapSite_pointwise, hF _ hmem]
  obtain ⟨x1, x2⟩ := x
  have h2 := two_mul_chooseTwo x1
  have hA : (x1 + 1) * (x1 + 1 + 1) / 2 = chooseTwo x1 + 2 * x1 + 1 := by
    have e : (x1 + 1) * (x1 + 1 + 1) = 2 * (chooseTwo x1 + 2 * x1 + 1) := by linear_combination (-1 : ℤ) * h2
    rw [e]
    omega
  have hsq : (x2 + 1 - x1) ^ 2 = (x1 - x2 - 1) ^ 2 := by ring
  unfold paperLadderValue paperNearLadderValue centeredQuarterTurnCorrection
  simp only [Set.indicator_apply, Set.mem_union, paperLadderA, paperLadderB, paperNearLadderA, paperNearLadderB,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  rw [hA, hsq]
  generalize (x1 - x2 - 1) ^ 2 = q
  generalize chooseTwo x1 = c
  split_ifs <;> omega

/-- **The global identity, doubled (surgical `lemma:doubled_staircase_laplacian`, E18).** For the near-one doubled odometer
`field` (tile values, periods of `Fraction.rotate ⟨1,d⟩`, uniqueness), `field (x + e₂) = rotateLadderField d F x` for all `x`.
Overlap pairs `(0,1) ↦ (d+1,d)` (kernel `(d+1,d−1)`) and `(1,1) ↦ (−1,2d+1)` (transverse `(−2,2d)`) force the constants. -/
theorem nearLadder_plus_eq_rotate {d : ℤ} (hd : 4 ≤ d ∧ d % 2 = 0) (F : Field)
    (hFtile : ∀ z ∈ paperLadderTile d, F z = paperLadderValue d z)
    {cUF cVF : ℤ} (hFper : HasGeneratorPeriods (Fraction.mk 1 d) F cUF cVF)
    (field : Field) (cU cV : ℤ)
    (htile : ∀ x ∈ paperNearLadderTile d, field x = paperNearLadderValue d x)
    (hper : HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) field cU cV)
    (huniq : ∀ other : Field, (∀ x ∈ paperNearLadderTile d, other x = paperNearLadderValue d x) →
      HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) other cU cV → other = field) (x : Site) :
    field (x + (0, 1)) = rotateLadderField d F x := by
  have hRp := hasGeneratorPeriods_rotateLadderField hd.2 hFper
  have hk : (Fraction.mk 1 d).rotate.modifiedDeck.kernel = (d + 1, d - 1) := by
    rw [nearOneLadderDeck_eq hd.2]
  have hT : (Fraction.mk 1 d).rotate.modifiedDeck.transverse = (-2, 2 * d) := by
    rw [nearOneLadderDeck_eq hd.2]
  have hVtile : ∀ y ∈ paperNearLadderTile d,
      rotateLadderField d F (y - (0, 1)) = paperNearLadderValue d y := by
    intro y hy
    have e1 : ((y - (0, 1)).1, (y - (0, 1)).2 + 1) = y := by
      ext <;> simp
    have h := rotateLadderField_eq_nearLadder_tile hd F hFtile (y - (0, 1)) (by rw [e1]; exact hy)
    rw [e1] at h
    exact h
  have hkV : ∀ y : Site, rotateLadderField d F (y + (Fraction.mk 1 d).rotate.modifiedDeck.kernel - (0, 1)) =
      rotateLadderField d F (y - (0, 1)) + (d + cVF + chooseTwo (d + 1)) := by
    intro y
    have e : y + (Fraction.mk 1 d).rotate.modifiedDeck.kernel - (0, 1) =
        (y - (0, 1)) + (Fraction.mk 1 d).rotate.modifiedDeck.kernel := by abel
    rw [e]
    exact hRp.1 _
  have hTG : ∀ z : Site, (Fraction.mk 1 d).rotate.transverseGrade (z - (0, 1)) =
      (Fraction.mk 1 d).rotate.transverseGrade z - (Fraction.mk 1 d).rotate.den := by
    intro z
    unfold Fraction.transverseGrade
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  have hTV : ∀ y : Site, rotateLadderField d F (y + (Fraction.mk 1 d).rotate.modifiedDeck.transverse - (0, 1)) =
      rotateLadderField d F (y - (0, 1)) - (Fraction.mk 1 d).rotate.transverseGrade y +
        ((Fraction.mk 1 d).rotate.den + (ladderEvenConstantV d - cUF)) := by
    intro y
    have e : y + (Fraction.mk 1 d).rotate.modifiedDeck.transverse - (0, 1) =
        (y - (0, 1)) + (Fraction.mk 1 d).rotate.modifiedDeck.transverse := by abel
    rw [e, hRp.2 _, hTG y]
    ring
  -- the overlap points
  have m0 : ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderTile d := by
    simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
      Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have m1 : ((d + 1 : ℤ), d) ∈ paperNearLadderTile d := by
    simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
      Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have m2 : ((1 : ℤ), (1 : ℤ)) ∈ paperNearLadderTile d := by
    simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
      Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have m3 : ((-1 : ℤ), 2 * d + 1) ∈ paperNearLadderTile d := by
    unfold paperNearLadderTile
    refine ⟨Or.inl (Or.inl (Set.mem_insert _ _)), ?_⟩
    intro hD
    simp only [paperNearLadderD, Set.mem_setOf_eq] at hD
    omega
  have e1 : ((0 : ℤ), (1 : ℤ)) + (d + 1, d - 1) = (d + 1, d) := by
    simp only [Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  have e2 : ((1 : ℤ), (1 : ℤ)) + (-2, 2 * d) = (-1, 2 * d + 1) := by
    simp only [Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  have hcU : cU = d + cVF + chooseTwo (d + 1) := by
    have h1 := hper.1 (0, 1)
    rw [hk, e1] at h1
    have h2 := hkV (0, 1)
    rw [hk, e1] at h2
    have f1 := htile _ m1
    have f0 := htile _ m0
    have v1 := hVtile _ m1
    have v0 := hVtile _ m0
    linarith
  have hcV : cV = (Fraction.mk 1 d).rotate.den + (ladderEvenConstantV d - cUF) := by
    have h1 := hper.2 (1, 1)
    rw [hT, e2] at h1
    have h2 := hTV (1, 1)
    rw [hT, e2] at h2
    have f1 := htile _ m3
    have f2 := htile _ m2
    have v1 := hVtile _ m3
    have v2 := hVtile _ m2
    linarith
  have hVper : HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩)
      (fun y => rotateLadderField d F (y - (0, 1))) cU cV := by
    refine ⟨fun y => ?_, fun y => ?_⟩
    · show rotateLadderField d F (y + (Fraction.mk 1 d).rotate.modifiedDeck.kernel - (0, 1)) =
        rotateLadderField d F (y - (0, 1)) + cU
      rw [hcU]
      exact hkV y
    · show rotateLadderField d F (y + (Fraction.mk 1 d).rotate.modifiedDeck.transverse - (0, 1)) =
        rotateLadderField d F (y - (0, 1)) - (Fraction.mk 1 d).rotate.transverseGrade y + cV
      rw [hcV]
      exact hTV y
  have hVeq := huniq (fun y => rotateLadderField d F (y - (0, 1))) hVtile hVper
  rw [← congrFun hVeq (x + (0, 1))]
  show rotateLadderField d F (x + (0, 1) - (0, 1)) = rotateLadderField d F x
  rw [add_sub_cancel_right]

/-- The Laplacian of the rotated standard doubled height: `Δ(rotateLadderField d F)(x) = ΔF(2d − x₂, x₁ + 1)`. -/
theorem laplacian_rotateLadderField {d : ℤ} (hd : d % 2 = 0) (F : Field) (x : Site) :
    laplacian (rotateLadderField d F) x = laplacian F (2 * d - x.2, x.1 + 1) := by
  have hodd : ¬ EvenSite (2 * d, 1) := by
    unfold EvenSite
    simp only
    omega
  have h := laplacian_quarterTurn_add_harmonic QuarterTurn.counterclockwise (2 * d, 1) hodd F
    centeredQuarterTurnCorrection harmonic_centeredQuarterTurnCorrection x
  unfold rotateLadderField
  rw [h, rotateLadder_mapSite_pointwise]

/-- **The Laplacian identity of surgical `lemma:doubled_staircase_laplacian` (E18), the doubled pair.** For the near-one
doubled odometer `field` and the standard doubled odometer `F` of `1/d`, the Laplacian of `z ↦ field (z + e₂)` at `x` is the
Laplacian of `F` at `(2d − x₂, x₁ + 1)`, for every `x ∈ Z²`. -/
theorem doubled_staircase_laplacian_rotation {d : ℤ} (hd : 4 ≤ d ∧ d % 2 = 0) (F : Field)
    (hFtile : ∀ z ∈ paperLadderTile d, F z = paperLadderValue d z)
    {cUF cVF : ℤ} (hFper : HasGeneratorPeriods (Fraction.mk 1 d) F cUF cVF)
    (field : Field) (cU cV : ℤ)
    (htile : ∀ x ∈ paperNearLadderTile d, field x = paperNearLadderValue d x)
    (hper : HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) field cU cV)
    (huniq : ∀ other : Field, (∀ x ∈ paperNearLadderTile d, other x = paperNearLadderValue d x) →
      HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) other cU cV → other = field) (x : Site) :
    laplacian (fun z => field (z + (0, 1))) x = laplacian F (2 * d - x.2, x.1 + 1) := by
  have hfun : (fun z : Site => field (z + (0, 1))) = rotateLadderField d F := by
    funext z
    exact nearLadder_plus_eq_rotate hd F hFtile hFper field cU cV htile hper huniq z
  rw [hfun, laplacian_rotateLadderField hd.2]

end FLatticePaper.Construction
