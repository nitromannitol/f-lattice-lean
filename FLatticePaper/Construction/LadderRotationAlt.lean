import FLatticePaper.Construction.LadderRotationTile

/-! # The alternate doubled identity (surgical `lemma:doubled_staircase_laplacian`, line 2581; E18)

For even `d ≥ 4`, with the near-one alternate doubled odometer translated by `e₂`:
`ĝ_{near}(z + e₂) = ĝ_{1/d}(2d − 2 − z₂, z₁ + 1) + corr(z) + z₁ + 1`, where `corr = centeredQuarterTurnCorrection`
(the operator's `−h₀`). The correction `corr + z₁ + 1` is harmonic, so the Laplacian identity follows. -/

namespace FLatticePaper.Construction

open Farey

/-- The rotated alternate doubled field: `F(2d − 2 − z₂, z₁ + 1) + (corr z + z₁ + 1)`. -/
def rotateAltLadderField (d : ℤ) (F : Field) : Field := fun z =>
  F (2 * d - 2 - z.2, z.1 + 1) + (centeredQuarterTurnCorrection z + z.1 + 1)

/-- `corr` shifted by `2e₂` is `corr` plus the affine function `z₁ − z₂ − 2`. -/
theorem centeredQuarterTurnCorrection_add_two (z : Site) :
    centeredQuarterTurnCorrection (z + (0, 2)) = centeredQuarterTurnCorrection z + z.1 - z.2 - 2 := by
  obtain ⟨x, y⟩ := z
  simp only [centeredQuarterTurnCorrection, Prod.mk_add_mk, add_zero]
  have e : (x - (y + 2) - 1) ^ 2 = (x - y - 1) ^ 2 - 4 * (x - y - 1) + 4 := by ring
  rw [e]
  generalize (x - y - 1) ^ 2 = q
  omega

theorem harmonic_affine_fst (x : Site) : laplacian (fun z : Site => z.1 + 1) x = 0 := by
  unfold laplacian incomingNeg incomingPos
  by_cases h : EvenSite x
  · simp only [if_pos h]
    ring
  · simp only [if_neg h]
    ring

/-- The correction `corr + z₁ + 1` is harmonic. -/
theorem harmonic_alt_correction :
    Harmonic (fun z : Site => centeredQuarterTurnCorrection z + z.1 + 1) := by
  intro x
  have h1 := harmonic_centeredQuarterTurnCorrection x
  have h2 := harmonic_affine_fst x
  unfold laplacian at h1 h2 ⊢
  dsimp only at h1 h2 ⊢
  linarith

theorem mapSite_alt_pointwise (d : ℤ) (x : Site) :
    QuarterTurn.counterclockwise.mapSite (2 * d - 2, 1) x = (2 * d - 2 - x.2, x.1 + 1) := by
  apply Prod.ext
  · change -x.2 + (2 * d - 2) = 2 * d - 2 - x.2
    omega
  · rfl

/-- The Laplacian of the rotated alternate doubled field. -/
theorem laplacian_rotateAltLadderField {d : ℤ} (hd : d % 2 = 0) (F : Field) (x : Site) :
    laplacian (rotateAltLadderField d F) x = laplacian F (2 * d - 2 - x.2, x.1 + 1) := by
  have hodd : ¬ EvenSite (2 * d - 2, 1) := by
    unfold EvenSite
    simp only
    omega
  have h := laplacian_quarterTurn_add_harmonic QuarterTurn.counterclockwise (2 * d - 2, 1) hodd F
    (fun z : Site => centeredQuarterTurnCorrection z + z.1 + 1) harmonic_alt_correction x
  have hfun : (rotateAltLadderField d F) = fun input =>
      F (QuarterTurn.counterclockwise.mapSite (2 * d - 2, 1) input) +
        (centeredQuarterTurnCorrection input + input.1 + 1) := by
    funext z
    rw [mapSite_alt_pointwise]
    rfl
  rw [hfun, h, mapSite_alt_pointwise]

theorem ladderAltTile_of_nearAltTile_point {d : ℤ} {x : Site}
    (hx : (x.1, x.2 + 1) ∈ paperNearLadderAltTile d) :
    (2 * d - 2 - x.2, x.1 + 1) ∈ paperLadderAltTile d := by
  obtain ⟨x1, x2⟩ := x
  simp only [paperNearLadderAltTile, paperLadderAltTile, paperNearLadderAltA, paperNearLadderAltB,
    paperNearLadderAltC, paperNearLadderAltD, paperLadderAltA, paperLadderAltB, paperLadderAltC, paperLadderAltD,
    Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx ⊢
  omega

/-- **Pointwise identity (alternate doubled).** On the translated near-one alternate tile, the rotated alternate height is the
near-one alternate height at `x + e₂`. -/
theorem rotateAltLadderField_eq_nearLadderAlt_tile {d : ℤ} (hd : 4 ≤ d ∧ d % 2 = 0) (F : Field)
    (hF : ∀ z ∈ paperLadderAltTile d, F z = paperLadderAltValue d z) (x : Site)
    (hx : (x.1, x.2 + 1) ∈ paperNearLadderAltTile d) :
    rotateAltLadderField d F x = paperNearLadderAltValue d (x.1, x.2 + 1) := by
  have hmem := ladderAltTile_of_nearAltTile_point hx
  unfold rotateAltLadderField
  rw [hF _ hmem]
  obtain ⟨x1, x2⟩ := x
  have h2 := two_mul_chooseTwo x1
  have hA : (x1 + 1) * (x1 + 1 + 1) / 2 = chooseTwo x1 + 2 * x1 + 1 := by
    have e : (x1 + 1) * (x1 + 1 + 1) = 2 * (chooseTwo x1 + 2 * x1 + 1) := by
      linear_combination (-1 : ℤ) * h2
    rw [e]
    omega
  have hsq : (x2 + 1 - x1) ^ 2 = (x1 - x2 - 1) ^ 2 := by ring
  unfold paperLadderAltValue paperNearLadderAltValue centeredQuarterTurnCorrection
  simp only [Set.indicator_apply, Set.mem_union, paperLadderAltA, paperLadderAltB, paperNearLadderAltA,
    paperNearLadderAltB, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq]
  rw [hA, hsq]
  generalize (x1 - x2 - 1) ^ 2 = q
  generalize chooseTwo x1 = c
  split_ifs <;> omega

/-- The shift identity: `rotateAltLadderField (y − e₂) = rotateLadderField (y + e₂) + (y₂ + 2)`. -/
theorem rotateAltLadderField_sub_eq (d : ℤ) (F : Field) (y : Site) :
    rotateAltLadderField d F (y - (0, 1)) = rotateLadderField d F (y + (0, 1)) + (y.2 + 2) := by
  obtain ⟨y1, y2⟩ := y
  have hsub : ((y1, y2) - (0, 1) : Site) = (y1, y2 - 1) := by
    rw [Prod.mk_sub_mk, sub_zero]
  have hadd : ((y1, y2) + (0, 1) : Site) = (y1, y2 + 1) := by
    rw [Prod.mk_add_mk, add_zero]
  rw [hsub, hadd]
  unfold rotateAltLadderField rotateLadderField
  rw [rotateLadder_mapSite_pointwise]
  dsimp only
  have key : F (2 * d - 2 - (y2 - 1), y1 + 1) = F (2 * d - (y2 + 1), y1 + 1) := by
    congr 1
    exact Prod.ext (by ring) rfl
  rw [key]
  have hc := centeredQuarterTurnCorrection_add_two (y1, y2 - 1)
  have e2 : ((y1, y2 - 1) : Site) + (0, 2) = (y1, y2 + 1) := by
    simp only [Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  rw [e2] at hc
  dsimp only at hc
  rw [hc]
  ring

/-- **The global identity, alternate doubled (surgical line 2581, E18).** For the near-one alternate doubled odometer `field`
and the standard alternate odometer `F` of `1/d`: `field (x + e₂) = rotateAltLadderField d F x` for all `x ∈ Z²`. -/
theorem nearLadderAlt_plus_eq_rotate {d : ℤ} (hd : 4 ≤ d ∧ d % 2 = 0) (F : Field)
    (hFtile : ∀ z ∈ paperLadderAltTile d, F z = paperLadderAltValue d z)
    {cUF cVF : ℤ} (hFper : HasGeneratorPeriods (Fraction.mk 1 d) F cUF cVF)
    (field : Field) (cU cV : ℤ)
    (htile : ∀ x ∈ paperNearLadderAltTile d, field x = paperNearLadderAltValue d x)
    (hper : HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) field cU cV)
    (huniq : ∀ other : Field, (∀ x ∈ paperNearLadderAltTile d, other x = paperNearLadderAltValue d x) →
      HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) other cU cV → other = field) (x : Site) :
    field (x + (0, 1)) = rotateAltLadderField d F x := by
  have hRp := hasGeneratorPeriods_rotateLadderField hd.2 hFper
  have hk : (Fraction.mk 1 d).rotate.modifiedDeck.kernel = (d + 1, d - 1) := by
    rw [nearOneLadderDeck_eq hd.2]
  have hT : (Fraction.mk 1 d).rotate.modifiedDeck.transverse = (-2, 2 * d) := by
    rw [nearOneLadderDeck_eq hd.2]
  have hVtile : ∀ y ∈ paperNearLadderAltTile d,
      rotateAltLadderField d F (y - (0, 1)) = paperNearLadderAltValue d y := by
    intro y hy
    have e1 : ((y - (0, 1)).1, (y - (0, 1)).2 + 1) = y := by
      ext <;> simp
    have h := rotateAltLadderField_eq_nearLadderAlt_tile hd F hFtile (y - (0, 1)) (by rw [e1]; exact hy)
    rw [e1] at h
    exact h
  -- the periods of `V y = rotateAltLadderField (y − e₂)`
  have hVk : ∀ y : Site, rotateAltLadderField d F (y + (Fraction.mk 1 d).rotate.modifiedDeck.kernel - (0, 1)) =
      rotateAltLadderField d F (y - (0, 1)) + (d + cVF + chooseTwo (d + 1) + (d - 1)) := by
    intro y
    rw [rotateAltLadderField_sub_eq, rotateAltLadderField_sub_eq]
    have e : y + (Fraction.mk 1 d).rotate.modifiedDeck.kernel + (0, 1) =
        (y + (0, 1)) + (Fraction.mk 1 d).rotate.modifiedDeck.kernel := by abel
    rw [e, hRp.1 (y + (0, 1))]
    have hy2 : (y + (Fraction.mk 1 d).rotate.modifiedDeck.kernel).2 = y.2 + (d - 1) := by
      rw [hk, Prod.snd_add]
    rw [hy2]
    ring
  have hTG : ∀ z : Site, (Fraction.mk 1 d).rotate.transverseGrade (z + (0, 1)) =
      (Fraction.mk 1 d).rotate.transverseGrade z + (Fraction.mk 1 d).rotate.den := by
    intro z
    unfold Fraction.transverseGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have hVt : ∀ y : Site, rotateAltLadderField d F (y + (Fraction.mk 1 d).rotate.modifiedDeck.transverse - (0, 1)) =
      rotateAltLadderField d F (y - (0, 1)) - (Fraction.mk 1 d).rotate.transverseGrade y +
        ((ladderEvenConstantV d - cUF) - (Fraction.mk 1 d).rotate.den + 2 * d) := by
    intro y
    rw [rotateAltLadderField_sub_eq, rotateAltLadderField_sub_eq]
    have e : y + (Fraction.mk 1 d).rotate.modifiedDeck.transverse + (0, 1) =
        (y + (0, 1)) + (Fraction.mk 1 d).rotate.modifiedDeck.transverse := by abel
    rw [e, hRp.2 (y + (0, 1)), hTG y]
    have hy2 : (y + (Fraction.mk 1 d).rotate.modifiedDeck.transverse).2 = y.2 + 2 * d := by
      rw [hT, Prod.snd_add]
    rw [hy2]
    ring
  -- the overlap points
  have m0 : ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile d := by
    simp only [paperNearLadderAltTile, paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC,
      paperNearLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have m1 : ((d + 1 : ℤ), d) ∈ paperNearLadderAltTile d := by
    simp only [paperNearLadderAltTile, paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC,
      paperNearLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have m2 : ((2 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile d := by
    simp only [paperNearLadderAltTile, paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC,
      paperNearLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have m3 : ((0 : ℤ), 2 * d + 1) ∈ paperNearLadderAltTile d := by
    simp only [paperNearLadderAltTile, paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC,
      paperNearLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have e1 : ((0 : ℤ), (1 : ℤ)) + (d + 1, d - 1) = (d + 1, d) := by
    simp only [Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  have e2 : ((2 : ℤ), (1 : ℤ)) + (-2, 2 * d) = (0, 2 * d + 1) := by
    simp only [Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  have hcU : cU = d + cVF + chooseTwo (d + 1) + (d - 1) := by
    have h1 := hper.1 (0, 1)
    rw [hk, e1] at h1
    have h2 := hVk (0, 1)
    rw [hk, e1] at h2
    have f1 := htile _ m1
    have f0 := htile _ m0
    have v1 := hVtile _ m1
    have v0 := hVtile _ m0
    linarith
  have hcV : cV = (ladderEvenConstantV d - cUF) - (Fraction.mk 1 d).rotate.den + 2 * d := by
    have h1 := hper.2 (2, 1)
    rw [hT, e2] at h1
    have h2 := hVt (2, 1)
    rw [hT, e2] at h2
    have f1 := htile _ m3
    have f2 := htile _ m2
    have v1 := hVtile _ m3
    have v2 := hVtile _ m2
    linarith
  have hVper : HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩)
      (fun y => rotateAltLadderField d F (y - (0, 1))) cU cV := by
    refine ⟨fun y => ?_, fun y => ?_⟩
    · show rotateAltLadderField d F (y + (Fraction.mk 1 d).rotate.modifiedDeck.kernel - (0, 1)) =
        rotateAltLadderField d F (y - (0, 1)) + cU
      rw [hcU]
      exact hVk y
    · show rotateAltLadderField d F (y + (Fraction.mk 1 d).rotate.modifiedDeck.transverse - (0, 1)) =
        rotateAltLadderField d F (y - (0, 1)) - (Fraction.mk 1 d).rotate.transverseGrade y + cV
      rw [hcV]
      exact hVt y
  have hVeq := huniq (fun y => rotateAltLadderField d F (y - (0, 1))) hVtile hVper
  rw [← congrFun hVeq (x + (0, 1))]
  show rotateAltLadderField d F (x + (0, 1) - (0, 1)) = rotateAltLadderField d F x
  rw [add_sub_cancel_right]

/-- **The Laplacian identity of surgical `lemma:doubled_staircase_laplacian` (line 2581).** For the near-one alternate doubled
odometer `field` and the standard alternate odometer `F` of `1/d`:
`Δ (z ↦ field (z + e₂)) (x) = Δ F (2d − 2 − x₂, x₁ + 1)` for every `x ∈ Z²`. -/
theorem doubled_alt_laplacian_rotation {d : ℤ} (hd : 4 ≤ d ∧ d % 2 = 0) (F : Field)
    (hFtile : ∀ z ∈ paperLadderAltTile d, F z = paperLadderAltValue d z)
    {cUF cVF : ℤ} (hFper : HasGeneratorPeriods (Fraction.mk 1 d) F cUF cVF)
    (field : Field) (cU cV : ℤ)
    (htile : ∀ x ∈ paperNearLadderAltTile d, field x = paperNearLadderAltValue d x)
    (hper : HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) field cU cV)
    (huniq : ∀ other : Field, (∀ x ∈ paperNearLadderAltTile d, other x = paperNearLadderAltValue d x) →
      HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) other cU cV → other = field) (x : Site) :
    laplacian (fun z => field (z + (0, 1))) x = laplacian F (2 * d - 2 - x.2, x.1 + 1) := by
  have hfun : (fun z : Site => field (z + (0, 1))) = rotateAltLadderField d F := by
    funext z
    exact nearLadderAlt_plus_eq_rotate hd F hFtile hFper field cU cV htile hper huniq z
  rw [hfun, laplacian_rotateAltLadderField hd.2]

end FLatticePaper.Construction
