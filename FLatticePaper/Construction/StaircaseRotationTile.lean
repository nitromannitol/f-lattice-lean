import FLatticePaper.Construction.NearOneBaseCases
import FLatticePaper.Construction.StaircaseRotation

/-! # The rotated standard staircase equals the translated near-one height on its tile

Surgical manuscript, `lemma:staircase_laplacian` (E18): the odometer `g_{R(1/d)}` of the near-one tile is the
translate `x ↦ g_{p_1}(x + e₂)`. For odd `d ≥ 3`, the rotated standard height `rotateStaircaseField d F` (with
`F` the standard height on `paperStairTile d`) agrees with `paperNearStairValue d (x + e₂)` at every `x` such that
`x + e₂` lies in `paperNearStairTile d`. The quarter turn `x ↦ (d − x₂, x₁)` sends that set into `paperStairTile d`. -/

namespace FLatticePaper.Construction

open Farey

theorem rotateStaircase_mapSite_pointwise (d : ℤ) (x : Site) :
    QuarterTurn.counterclockwise.mapSite (d, 0) x = (d - x.2, x.1) := by
  apply Prod.ext <;> dsimp [QuarterTurn.mapSite, QuarterTurn.turn] <;> omega

/-- The quarter turn of a near-one tile point (translated by `e₂`) lies in the standard tile. -/
theorem stairTile_of_nearOne_tile_point {d : ℤ} {x : Site} (hx : (x.1, x.2 + 1) ∈ paperNearStairTile d) :
    (d - x.2, x.1) ∈ paperStairTile d := by
  obtain ⟨x1, x2⟩ := x
  simp only [paperNearStairTile, paperStairTile, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, Prod.mk.injEq] at hx ⊢
  omega

/-- **Pointwise rotation identity.** On the translated near-one tile, the rotated standard height is the near-one
height at `x + e₂`. -/
theorem rotateStaircaseField_eq_nearOne_tile {d : ℤ} (hd : 3 ≤ d) (F : Field)
    (hF : ∀ z ∈ paperStairTile d, F z = paperStairValue d z) (x : Site)
    (hx : (x.1, x.2 + 1) ∈ paperNearStairTile d) :
    rotateStaircaseField d F x = paperNearStairValue d (x.1, x.2 + 1) := by
  have hmem := stairTile_of_nearOne_tile_point hx
  unfold rotateStaircaseField
  rw [rotateStaircase_mapSite_pointwise, hF _ hmem]
  obtain ⟨x1, x2⟩ := x
  have h2 := two_mul_chooseTwo x1
  have hA : x1 * (x1 + 1) / 2 = chooseTwo x1 + x1 := by
    have e : x1 * (x1 + 1) = 2 * (chooseTwo x1 + x1) := by linear_combination (-1 : ℤ) * h2
    rw [e]
    omega
  have hsq : (x2 + 1 - x1) ^ 2 = (x1 - x2 - 1) ^ 2 := by ring
  have hmin : d - (x2 + 1) = d - x2 - 1 := by ring
  have hite : (if (x1, x2 + 1) = (0, d + 1) ∨ (x1, x2 + 1) = (d + 1, d - 1) then (1 : ℤ) else 0) =
      (if (d - x2, x1) = (0, 0) ∨ (d - x2, x1) = (2, d + 1) then (1 : ℤ) else 0) := by
    simp only [Prod.mk.injEq]
    split_ifs <;> omega
  unfold paperStairValue paperNearStairValue centeredQuarterTurnCorrection
  simp only at *
  rw [hite, hmin]
  rw [show x1 * (x1 + 1) / 2 = chooseTwo x1 + x1 from hA]
  rw [hsq]
  generalize (x1 - x2 - 1) ^ 2 = q
  generalize chooseTwo x1 = c
  omega

/-- **Laplacian of the rotated standard staircase.** For odd `d`, `Δ(rotateStaircaseField d F)(x) = ΔF(d − x₂, x₁)`, the
identity of `lemma:staircase_laplacian` (surgical E18) once `g_{R(1/d)}` is the rotated standard height. -/
theorem laplacian_rotateStaircaseField {d : ℤ} (hd : d % 2 = 1) (F : Field) (x : Site) :
    laplacian (rotateStaircaseField d F) x = laplacian F (d - x.2, x.1) := by
  have hodd : ¬ EvenSite (d, 0) := by
    unfold EvenSite
    simp only
    omega
  have h := laplacian_quarterTurn_add_harmonic QuarterTurn.counterclockwise (d, 0) hodd F
    centeredQuarterTurnCorrection harmonic_centeredQuarterTurnCorrection x
  unfold rotateStaircaseField
  rw [h, rotateStaircase_mapSite_pointwise]

/-- **The near-one staircase odometer in the surgical form.** `near_staircase_base` with its recurrence stated for the
translate `z ↦ field (z + e₂)` (the R-odometer of surgical `lemma:staircase_laplacian`). The two translates differ by the
even vector `2e₂`, so superharmonicity and recurrence transfer (`superharmonic_translate_even`, `recurrent_translate_even`). -/
theorem near_staircase_base_plus {d : ℤ} (hd : 3 ≤ d ∧ d % 2 = 1) :
    ∃ constantU constantV : ℤ, ∃ field : Field,
      (∀ x ∈ paperNearStairTile d, field x = paperNearStairValue d x) ∧
      HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) field constantU constantV ∧
      (∀ other : Field, (∀ x ∈ paperNearStairTile d, other x = paperNearStairValue d x) →
        HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) other constantU constantV → other = field) ∧
      Superharmonic (fun z => field (z + (0, 1))) ∧ Recurrent (fun z => field (z + (0, 1))) := by
  obtain ⟨cU, cV, field, h1, h2, h3, hs, hr⟩ := near_staircase_base hd
  refine ⟨cU, cV, field, h1, h2, h3, ?_, ?_⟩
  · have e : (fun z : Site => field (z + (0, 1))) = fun z => (fun y => field (y - (0, 1))) (z - (0, -2)) := by
      funext z
      congr 1
      ext <;> simp
      all_goals omega
    rw [e]
    exact superharmonic_translate_even (by unfold EvenSite; norm_num) hs
  · have e : (fun z : Site => field (z + (0, 1))) = fun z => (fun y => field (y - (0, 1))) (z - (0, -2)) := by
      funext z
      congr 1
      ext <;> simp
      all_goals omega
    rw [e]
    exact recurrent_translate_even (field := fun z => field (z - (0, 1))) (w := (0, -2))
      (by unfold EvenSite; norm_num) hr

/-- **The global identity (surgical `lemma:staircase_laplacian`, E18).** Let `field` be the near-one odometer (tile values,
periods, uniqueness among fields with the same constants). Then `field (x + e₂) = rotateStaircaseField d F x` for every `x`.
Proof: `V y = rotateStaircaseField d F (y − e₂)` has the tile values and the periods of `rotate ⟨1,d⟩` with the constants
`(A, den + B)` (from `rotateStaircaseField_periods`, `nearOneDeck_eq`, and the shift of `transverseGrade` by `−e₂`).
Two overlap pairs of the tile, `(0,1) ↦ (d+1,d)` (kernel) and `(1,1) ↦ (0,d+1)` (transverse), force `cU = A`, `cV = den + B`.
Uniqueness then gives `V = field`. -/
theorem nearOne_plus_eq_rotate {d : ℤ} (hd : 3 ≤ d ∧ d % 2 = 1) (F : Field)
    (hFtile : ∀ z ∈ paperStairTile d, F z = paperStairValue d z)
    {cUF cVF : ℤ} (hFper : HasGeneratorPeriods (Fraction.mk 1 d) F cUF cVF)
    (field : Field) (cU cV : ℤ)
    (htile : ∀ x ∈ paperNearStairTile d, field x = paperNearStairValue d x)
    (hper : HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) field cU cV)
    (huniq : ∀ other : Field, (∀ x ∈ paperNearStairTile d, other x = paperNearStairValue d x) →
      HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) other cU cV → other = field) (x : Site) :
    field (x + (0, 1)) = rotateStaircaseField d F x := by
  have hRp := rotateStaircaseField_periods hd.2 hFper
  have hk : (Fraction.mk 1 d).rotate.modifiedDeck.kernel = (d + 1, d - 1) := by
    rw [nearOneDeck_eq hd.2]
  have hT : (Fraction.mk 1 d).rotate.modifiedDeck.transverse = (-1, d) := by
    rw [nearOneDeck_eq hd.2]
  have hVtile : ∀ y ∈ paperNearStairTile d,
      rotateStaircaseField d F (y - (0, 1)) = paperNearStairValue d y := by
    intro y hy
    have e1 : ((y - (0, 1)).1, (y - (0, 1)).2 + 1) = y := by
      ext <;> simp
    have h := rotateStaircaseField_eq_nearOne_tile hd.1 F hFtile (y - (0, 1))
      (by rw [e1]; exact hy)
    rw [e1] at h
    exact h
  have hkV : ∀ y : Site, rotateStaircaseField d F (y + (Fraction.mk 1 d).rotate.modifiedDeck.kernel - (0, 1)) =
      rotateStaircaseField d F (y - (0, 1)) + (d + cVF + chooseTwo (d + 1)) := by
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
  have hTV : ∀ y : Site, rotateStaircaseField d F (y + (Fraction.mk 1 d).rotate.modifiedDeck.transverse - (0, 1)) =
      rotateStaircaseField d F (y - (0, 1)) - (Fraction.mk 1 d).rotate.transverseGrade y +
        ((Fraction.mk 1 d).rotate.den + (centeredQuarterTurnCorrection (-1, d) - cUF)) := by
    intro y
    have e : y + (Fraction.mk 1 d).rotate.modifiedDeck.transverse - (0, 1) =
        (y - (0, 1)) + (Fraction.mk 1 d).rotate.modifiedDeck.transverse := by abel
    rw [e, hRp.2 _, hTG y]
    ring
  -- the overlap points
  have m0 : ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairTile d := by
    simp only [paperNearStairTile, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq]
    omega
  have m1 : ((d + 1 : ℤ), d) ∈ paperNearStairTile d := by
    simp only [paperNearStairTile, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq]
    omega
  have m2 : ((1 : ℤ), (1 : ℤ)) ∈ paperNearStairTile d := by
    simp only [paperNearStairTile, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq]
    omega
  have m3 : ((0 : ℤ), d + 1) ∈ paperNearStairTile d := by
    unfold paperNearStairTile
    exact Set.mem_union_right _ (Set.mem_insert _ _)
  have e1 : ((0 : ℤ), (1 : ℤ)) + (d + 1, d - 1) = (d + 1, d) := by
    ext <;> simp
  have e2 : ((1 : ℤ), (1 : ℤ)) + (-1, d) = (0, d + 1) := by
    ext <;> simp
    all_goals ring
  -- the constants are forced by the overlaps
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
  have hcV : cV = (Fraction.mk 1 d).rotate.den + (centeredQuarterTurnCorrection (-1, d) - cUF) := by
    have h1 := hper.2 (1, 1)
    rw [hT, e2] at h1
    have h2 := hTV (1, 1)
    rw [hT, e2] at h2
    have f1 := htile _ m3
    have f2 := htile _ m2
    have v1 := hVtile _ m3
    have v2 := hVtile _ m2
    linarith
  have hVper : HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) (fun y => rotateStaircaseField d F (y - (0, 1))) cU cV := by
    refine ⟨fun y => ?_, fun y => ?_⟩
    · show rotateStaircaseField d F (y + (Fraction.mk 1 d).rotate.modifiedDeck.kernel - (0, 1)) =
        rotateStaircaseField d F (y - (0, 1)) + cU
      rw [hcU]
      exact hkV y
    · show rotateStaircaseField d F (y + (Fraction.mk 1 d).rotate.modifiedDeck.transverse - (0, 1)) =
        rotateStaircaseField d F (y - (0, 1)) - (Fraction.mk 1 d).rotate.transverseGrade y + cV
      rw [hcV]
      exact hTV y
  have hVeq := huniq (fun y => rotateStaircaseField d F (y - (0, 1))) hVtile hVper
  rw [← congrFun hVeq (x + (0, 1))]
  show rotateStaircaseField d F (x + (0, 1) - (0, 1)) = rotateStaircaseField d F x
  rw [add_sub_cancel_right]

/-- **The Laplacian identity of surgical `lemma:staircase_laplacian` (E18), the staircase pair.** For any near-one odometer
`field` (its tile values, periods, uniqueness) and any standard odometer `F` of `1/d`, the Laplacian of the translate
`z ↦ field (z + e₂)` at `x` is the Laplacian of `F` at `(d − x₂, x₁)`, for every `x ∈ Z²`. -/
theorem staircase_laplacian_rotation {d : ℤ} (hd : 3 ≤ d ∧ d % 2 = 1) (F : Field)
    (hFtile : ∀ z ∈ paperStairTile d, F z = paperStairValue d z)
    {cUF cVF : ℤ} (hFper : HasGeneratorPeriods (Fraction.mk 1 d) F cUF cVF)
    (field : Field) (cU cV : ℤ)
    (htile : ∀ x ∈ paperNearStairTile d, field x = paperNearStairValue d x)
    (hper : HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) field cU cV)
    (huniq : ∀ other : Field, (∀ x ∈ paperNearStairTile d, other x = paperNearStairValue d x) →
      HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) other cU cV → other = field) (x : Site) :
    laplacian (fun z => field (z + (0, 1))) x = laplacian F (d - x.2, x.1) := by
  have hfun : (fun z : Site => field (z + (0, 1))) = rotateStaircaseField d F := by
    funext z
    exact nearOne_plus_eq_rotate hd F hFtile hFper field cU cV htile hper huniq z
  rw [hfun, laplacian_rotateStaircaseField hd.2]

/-- The quarter turn of a near-one alternate tile point (translated by `e₂`) lies in the standard alternate tile. -/
theorem stairAltTile_of_nearAlt_tile_point {d : ℤ} {x : Site} (hx : (x.1, x.2 + 1) ∈ paperNearStairAltTile d) :
    (d - x.2, x.1) ∈ paperStairAltTile d := by
  obtain ⟨x1, x2⟩ := x
  simp only [paperNearStairAltTile, paperNearStairAltA, paperNearStairAltB, paperNearStairAltC, paperNearStairAltD,
    paperStairAltTile, paperStairAltA, paperStairAltB, paperStairAltC, paperStairAltD, Set.mem_union,
    Set.mem_setOf_eq] at hx ⊢
  omega

/-- **Pointwise rotation identity (alternate).** On the translated near-one alternate tile, the rotated standard alternate
height is the near-one alternate height at `x + e₂`. -/
theorem rotateStaircaseField_eq_nearAlt_tile {d : ℤ} (hd : 3 ≤ d) (F : Field)
    (hF : ∀ z ∈ paperStairAltTile d, F z = paperStairAltValue d z) (x : Site)
    (hx : (x.1, x.2 + 1) ∈ paperNearStairAltTile d) :
    rotateStaircaseField d F x = paperNearStairAltValue d (x.1, x.2 + 1) := by
  have hmem := stairAltTile_of_nearAlt_tile_point hx
  unfold rotateStaircaseField
  rw [rotateStaircase_mapSite_pointwise, hF _ hmem]
  obtain ⟨x1, x2⟩ := x
  have h2 := two_mul_chooseTwo x1
  have hA : x1 * (x1 + 1) / 2 = chooseTwo x1 + x1 := by
    have e : x1 * (x1 + 1) = 2 * (chooseTwo x1 + x1) := by linear_combination (-1 : ℤ) * h2
    rw [e]
    omega
  have hsq : (x2 + 1 - x1) ^ 2 = (x1 - x2 - 1) ^ 2 := by ring
  unfold paperStairAltValue paperNearStairAltValue centeredQuarterTurnCorrection
  simp only [Set.indicator_apply, Set.mem_union, paperStairAltA, paperStairAltB, paperNearStairAltA,
    paperNearStairAltB, Set.mem_setOf_eq]
  rw [hA, hsq]
  generalize (x1 - x2 - 1) ^ 2 = q
  generalize chooseTwo x1 = c
  split_ifs <;> omega

/-- **The global identity, alternate staircase.** For the near-one alternate odometer `field` (tile values, periods of
`Fraction.rotate ⟨1,d⟩`, uniqueness) and the standard alternate odometer `F` of `1/d`, `field (x + e₂) = rotateStaircaseField d F x`
for every `x ∈ Z²`. Same overlap pairs as `nearOne_plus_eq_rotate`: `(0,1) ↦ (d+1,d)` and `(1,1) ↦ (0,d+1)`. -/
theorem nearAlt_plus_eq_rotate {d : ℤ} (hd : 3 ≤ d ∧ d % 2 = 1) (F : Field)
    (hFtile : ∀ z ∈ paperStairAltTile d, F z = paperStairAltValue d z)
    {cUF cVF : ℤ} (hFper : HasGeneratorPeriods (Fraction.mk 1 d) F cUF cVF)
    (field : Field) (cU cV : ℤ)
    (htile : ∀ x ∈ paperNearStairAltTile d, field x = paperNearStairAltValue d x)
    (hper : HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) field cU cV)
    (huniq : ∀ other : Field, (∀ x ∈ paperNearStairAltTile d, other x = paperNearStairAltValue d x) →
      HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) other cU cV → other = field) (x : Site) :
    field (x + (0, 1)) = rotateStaircaseField d F x := by
  have hRp := rotateStaircaseField_periods hd.2 hFper
  have hk : (Fraction.mk 1 d).rotate.modifiedDeck.kernel = (d + 1, d - 1) := by
    rw [nearOneDeck_eq hd.2]
  have hT : (Fraction.mk 1 d).rotate.modifiedDeck.transverse = (-1, d) := by
    rw [nearOneDeck_eq hd.2]
  have hVtile : ∀ y ∈ paperNearStairAltTile d,
      rotateStaircaseField d F (y - (0, 1)) = paperNearStairAltValue d y := by
    intro y hy
    have e1 : ((y - (0, 1)).1, (y - (0, 1)).2 + 1) = y := by
      ext <;> simp
    have h := rotateStaircaseField_eq_nearAlt_tile hd.1 F hFtile (y - (0, 1)) (by rw [e1]; exact hy)
    rw [e1] at h
    exact h
  have hkV : ∀ y : Site, rotateStaircaseField d F (y + (Fraction.mk 1 d).rotate.modifiedDeck.kernel - (0, 1)) =
      rotateStaircaseField d F (y - (0, 1)) + (d + cVF + chooseTwo (d + 1)) := by
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
  have hTV : ∀ y : Site, rotateStaircaseField d F (y + (Fraction.mk 1 d).rotate.modifiedDeck.transverse - (0, 1)) =
      rotateStaircaseField d F (y - (0, 1)) - (Fraction.mk 1 d).rotate.transverseGrade y +
        ((Fraction.mk 1 d).rotate.den + (centeredQuarterTurnCorrection (-1, d) - cUF)) := by
    intro y
    have e : y + (Fraction.mk 1 d).rotate.modifiedDeck.transverse - (0, 1) =
        (y - (0, 1)) + (Fraction.mk 1 d).rotate.modifiedDeck.transverse := by abel
    rw [e, hRp.2 _, hTG y]
    ring
  have m0 : ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile d := by
    unfold paperNearStairAltTile
    simp only [paperNearStairAltA, paperNearStairAltB, paperNearStairAltC, paperNearStairAltD, Set.mem_union,
      Set.mem_setOf_eq]
    omega
  have m1 : ((d + 1 : ℤ), d) ∈ paperNearStairAltTile d := by
    unfold paperNearStairAltTile
    simp only [paperNearStairAltA, paperNearStairAltB, paperNearStairAltC, paperNearStairAltD, Set.mem_union,
      Set.mem_setOf_eq, true_and]
    omega
  have m2 : ((1 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile d := by
    unfold paperNearStairAltTile
    simp only [paperNearStairAltA, paperNearStairAltB, paperNearStairAltC, paperNearStairAltD, Set.mem_union,
      Set.mem_setOf_eq]
    omega
  have m3 : ((0 : ℤ), d + 1) ∈ paperNearStairAltTile d := by
    unfold paperNearStairAltTile
    simp only [paperNearStairAltA, paperNearStairAltB, paperNearStairAltC, paperNearStairAltD, Set.mem_union,
      Set.mem_setOf_eq]
    omega
  have e1 : ((0 : ℤ), (1 : ℤ)) + (d + 1, d - 1) = (d + 1, d) := by
    simp only [Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  have e2 : ((1 : ℤ), (1 : ℤ)) + (-1, d) = (0, d + 1) := by
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
  have hcV : cV = (Fraction.mk 1 d).rotate.den + (centeredQuarterTurnCorrection (-1, d) - cUF) := by
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
      (fun y => rotateStaircaseField d F (y - (0, 1))) cU cV := by
    refine ⟨fun y => ?_, fun y => ?_⟩
    · show rotateStaircaseField d F (y + (Fraction.mk 1 d).rotate.modifiedDeck.kernel - (0, 1)) =
        rotateStaircaseField d F (y - (0, 1)) + cU
      rw [hcU]
      exact hkV y
    · show rotateStaircaseField d F (y + (Fraction.mk 1 d).rotate.modifiedDeck.transverse - (0, 1)) =
        rotateStaircaseField d F (y - (0, 1)) - (Fraction.mk 1 d).rotate.transverseGrade y + cV
      rw [hcV]
      exact hTV y
  have hVeq := huniq (fun y => rotateStaircaseField d F (y - (0, 1))) hVtile hVper
  rw [← congrFun hVeq (x + (0, 1))]
  show rotateStaircaseField d F (x + (0, 1) - (0, 1)) = rotateStaircaseField d F x
  rw [add_sub_cancel_right]

/-- **The Laplacian identity of surgical `lemma:staircase_laplacian` (E18), alternate pair.** For the near-one alternate
odometer `field` and the standard alternate odometer `F` of `1/d`, `Δ (z ↦ field (z + e₂)) (x) = Δ F (d − x₂, x₁)`. -/
theorem staircase_alt_laplacian_rotation {d : ℤ} (hd : 3 ≤ d ∧ d % 2 = 1) (F : Field)
    (hFtile : ∀ z ∈ paperStairAltTile d, F z = paperStairAltValue d z)
    {cUF cVF : ℤ} (hFper : HasGeneratorPeriods (Fraction.mk 1 d) F cUF cVF)
    (field : Field) (cU cV : ℤ)
    (htile : ∀ x ∈ paperNearStairAltTile d, field x = paperNearStairAltValue d x)
    (hper : HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) field cU cV)
    (huniq : ∀ other : Field, (∀ x ∈ paperNearStairAltTile d, other x = paperNearStairAltValue d x) →
      HasGeneratorPeriods (Fraction.rotate ⟨1, d⟩) other cU cV → other = field) (x : Site) :
    laplacian (fun z => field (z + (0, 1))) x = laplacian F (d - x.2, x.1) := by
  have hfun : (fun z : Site => field (z + (0, 1))) = rotateStaircaseField d F := by
    funext z
    exact nearAlt_plus_eq_rotate hd F hFtile hFper field cU cV htile hper huniq z
  rw [hfun, laplacian_rotateStaircaseField hd.2]

end FLatticePaper.Construction
