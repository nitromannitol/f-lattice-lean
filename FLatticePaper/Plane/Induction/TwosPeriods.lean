import FLatticePaper.Plane.Induction.TwosNearOne
import FLatticePaper.Plane.Induction.TwosIdentification
import FLatticePaper.Plane.Induction.TwosPieces
import FLatticePaper.Plane.Induction.Sheets
import FLatticePaper.Plane.Induction.Periodization
import FLatticePaper.Construction.NearOneBaseCases

/-! # The periods of the twos sheet minimum, and the identification with the physical near-one field (task 39)

* `periods_combine`: a field with generator periods has the period increment at every `combine i j`.
* `rotate_tile_identity`: the physical near-one field `rotateLadderField d S` takes the TeX value at the point `x`
  of the tile, read at `x - (0,1)`.
* `rotate_eq_on_E`: on the closed polygon of `2^(k+1)`, the physical field equals `paperNearLadderValue d (z.1, z.2+1)`:
  the tile points by `rotate_tile_identity`, the two boundary points through a kernel translate and two explicit
  values.
* `twos_hper`: the sheet minimum respects the periods on the closed polygon.
* `twos_standardField_eq_rotate`: the standard field of `2^(k+1)` is the physical field on the whole plane (covering of
  the polygon). -/

namespace FLatticePaper.Induction
open Farey Construction

/-! ### Periods at every combination -/

theorem site_add_mk (a b c d : ℤ) : ((a, b) : Site) + (c, d) = (a + c, b + d) := rfl

theorem site_sub_mk (a b c d : ℤ) : ((a, b) : Site) - (c, d) = (a - c, b - d) := rfl

theorem tg_add (fr : Fraction) (a b : Site) :
    fr.transverseGrade (a + b) = fr.transverseGrade a + fr.transverseGrade b := by
  simp only [Fraction.transverseGrade, Prod.fst_add, Prod.snd_add]
  ring

theorem tg_kernel (fr : Fraction) : fr.transverseGrade fr.modifiedDeck.kernel = 0 := by
  simp only [Fraction.transverseGrade, Fraction.modifiedDeck, Fraction.unmodifiedDeck]
  ring

theorem tg_transverse (fr : Fraction) :
    fr.transverseGrade fr.modifiedDeck.transverse = fr.periodDenominator := by
  simp only [Fraction.transverseGrade, Fraction.modifiedDeck, Fraction.unmodifiedDeck, Fraction.periodDenominator]
  ring

theorem combine_split (fr : Fraction) (i j : ℤ) :
    fr.modifiedDeck.combine i j = fr.modifiedDeck.combine i 0 + fr.modifiedDeck.combine 0 j := by
  apply Prod.ext <;> simp only [PeriodDeck.combine, Prod.fst_add, Prod.snd_add] <;> ring

theorem tg_combine_left (fr : Fraction) (i : ℤ) :
    fr.transverseGrade (fr.modifiedDeck.combine i 0) = 0 := by
  have hK := tg_kernel fr
  simp only [Fraction.transverseGrade, PeriodDeck.combine] at hK ⊢
  linear_combination i * hK

theorem tg_combine_right (fr : Fraction) (j : ℤ) :
    fr.transverseGrade (fr.modifiedDeck.combine 0 j) = j * fr.periodDenominator := by
  have hV := tg_transverse fr
  simp only [Fraction.transverseGrade, PeriodDeck.combine] at hV ⊢
  linear_combination j * hV

theorem periods_kernel {fr : Fraction} {F : Field} {cU cV : ℤ} (h : HasGeneratorPeriods fr F cU cV) :
    ∀ i : ℤ, ∀ w : Site, F (w + fr.modifiedDeck.combine i 0) = F w + i * cU := by
  intro i
  refine Int.induction_on i ?_ ?_ ?_
  · intro w
    have h0 : fr.modifiedDeck.combine 0 0 = 0 := by
      ext <;> simp [PeriodDeck.combine]
    simp [h0]
  · intro n ih w
    have hs : fr.modifiedDeck.combine ((n : ℤ) + 1) 0 =
        fr.modifiedDeck.combine (n : ℤ) 0 + fr.modifiedDeck.kernel := by
      apply Prod.ext <;> simp only [PeriodDeck.combine, Prod.fst_add, Prod.snd_add] <;> ring
    rw [hs, ← add_assoc, h.1 (w + fr.modifiedDeck.combine (n : ℤ) 0), ih w]
    ring
  · intro n ih w
    have hs : fr.modifiedDeck.combine (-(n : ℤ) - 1) 0 + fr.modifiedDeck.kernel =
        fr.modifiedDeck.combine (-(n : ℤ)) 0 := by
      apply Prod.ext <;> simp only [PeriodDeck.combine, Prod.fst_add, Prod.snd_add] <;> ring
    have key := h.1 (w + fr.modifiedDeck.combine (-(n : ℤ) - 1) 0)
    rw [add_assoc, hs, ih w] at key
    linarith

theorem periods_transverse {fr : Fraction} {F : Field} {cU cV : ℤ} (h : HasGeneratorPeriods fr F cU cV) :
    ∀ j : ℤ, ∀ w : Site, F (w + fr.modifiedDeck.combine 0 j) =
      F w + j * (cV - fr.transverseGrade w) - fr.periodDenominator * chooseTwo j := by
  intro j
  refine Int.induction_on j ?_ ?_ ?_
  · intro w
    have h0 : fr.modifiedDeck.combine 0 0 = 0 := by
      ext <;> simp [PeriodDeck.combine]
    simp [h0, chooseTwo]
  · intro n ih w
    have hs : fr.modifiedDeck.combine 0 ((n : ℤ) + 1) =
        fr.modifiedDeck.combine 0 (n : ℤ) + fr.modifiedDeck.transverse := by
      apply Prod.ext <;> simp only [PeriodDeck.combine, Prod.fst_add, Prod.snd_add] <;> ring
    have hc : chooseTwo ((n : ℤ) + 1) = chooseTwo (n : ℤ) + n := by
      have h1 := two_mul_chooseTwo ((n : ℤ) + 1)
      have h2 := two_mul_chooseTwo (n : ℤ)
      linarith
    rw [hs, ← add_assoc, h.2 (w + fr.modifiedDeck.combine 0 (n : ℤ)), ih w, tg_add, tg_combine_right, hc]
    ring
  · intro n ih w
    have hs : fr.modifiedDeck.combine 0 (-(n : ℤ) - 1) + fr.modifiedDeck.transverse =
        fr.modifiedDeck.combine 0 (-(n : ℤ)) := by
      apply Prod.ext <;> simp only [PeriodDeck.combine, Prod.fst_add, Prod.snd_add] <;> ring
    have hc : chooseTwo (-(n : ℤ) - 1) = chooseTwo (-(n : ℤ)) + ((n : ℤ) + 1) := by
      have h1 := two_mul_chooseTwo (-(n : ℤ) - 1)
      have h2 := two_mul_chooseTwo (-(n : ℤ))
      linarith
    have key := h.2 (w + fr.modifiedDeck.combine 0 (-(n : ℤ) - 1))
    rw [add_assoc, hs, ih w, tg_add, tg_combine_right] at key
    rw [hc]
    linarith

/-- The period increment at every combination of the deck (the increments of `periodIncrement`). -/
theorem periods_combine {fr : Fraction} {F : Field} {cU cV : ℤ} (h : HasGeneratorPeriods fr F cU cV) (z : Site)
    (i j : ℤ) :
    F (z + fr.modifiedDeck.combine i j) = F z + periodIncrement fr cU cV z i j := by
  rw [combine_split, ← add_assoc, periods_transverse h j (z + fr.modifiedDeck.combine i 0),
    periods_kernel h i z, tg_add, tg_combine_left]
  unfold periodIncrement
  ring

/-! ### The deck of the child of `2^(k+1)` -/

theorem twos_combine_zero (k : ℕ) (i : ℤ) :
    (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.combine i 0 =
      (i * (2 * (k : ℤ) + 5), i * (2 * (k : ℤ) + 3)) := by
  have hK : (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.kernel =
      ((frameAt (List.replicate (k + 1) Digit.two)).child.den,
        (frameAt (List.replicate (k + 1) Digit.two)).child.num) :=
    ChildFrame.child_modifiedDeck_kernel _
  simp only [PeriodDeck.combine]
  rw [hK, twos_child_eq k]
  dsimp only
  apply Prod.ext <;> ring

/-! ### The physical field on the tile -/

/-- The tile identity of a near-one field with the llCenter agreement: the field at `x - (0,1)` is the TeX value at `x`. -/
theorem nearOne_tile_identity (raw : HeightTile Site) (hne : raw.sites.Nonempty) (S : Set Site)
    (value : Site → ℤ) (hmem : ∀ x, x ∈ raw.sites ↔ x ∈ S)
    (hheight : ∀ x (hx : x ∈ raw.sites), raw.height ⟨x, hx⟩ = value x)
    (hpoint : ((0 : ℤ), (1 : ℤ)) ∈ raw.sites)
    (hmin : ∀ site ∈ raw.sites, ((0 : ℤ), (1 : ℤ)).2 ≤ site.2 ∧
      (((0 : ℤ), (1 : ℤ)).2 = site.2 → ((0 : ℤ), (1 : ℤ)).1 ≤ site.1))
    {field : Field}
    (hagree : ((raw.trim hne).llCenter (raw.trim_sites_nonempty hne)).Agrees field 0) :
    ∀ x ∈ S, field (x - (0, 1)) = value x := by
  intro x hxS
  have hx : x ∈ raw.sites := (hmem x).mpr hxS
  have hraw : x - (0, 1) + (0, 1) ∈ raw.sites := by simpa using hx
  have hs : x - (0, 1) ∈ ((raw.trim hne).llCenter (raw.trim_sites_nonempty hne)).sites :=
    (mem_llCenter_iff raw hne hpoint hmin (x - (0, 1))).mpr hraw
  have e1 := hagree ⟨x - (0, 1), hs⟩
  have e2 := llCenter_height_eq raw hne hpoint hmin (x - (0, 1)) hs hraw
  have e3 := height_congr_site raw hraw hx (by simp)
  calc field (x - (0, 1)) = field (x - (0, 1)) + 0 := (add_zero _).symm
    _ = ((raw.trim hne).llCenter (raw.trim_sites_nonempty hne)).height ⟨x - (0, 1), hs⟩ := e1.symm
    _ = raw.height ⟨x - (0, 1) + (0, 1), hraw⟩ := e2
    _ = raw.height ⟨x, hx⟩ := e3
    _ = value x := hheight x hx

/-- The physical near-one field `rotateLadderField d S` of an odd-ladder source `S` reads the TeX tile values at the
shifted points: `S` agrees with the odd ladder on its raw tile. -/
theorem rotate_tile_identity {d : ℤ} (hd : 4 ≤ d ∧ d % 2 = 0) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw d).Agrees S 0) :
    ∀ x ∈ paperNearLadderTile d, rotateLadderField d S (x - (0, 1)) = paperNearLadderValue d x := by
  have hden : BaseMask.ladderEven.Valid d := hd
  have hpt : ((0 : ℤ), (1 : ℤ)) ∈ (BaseMask.ladderEven.raw d).sites :=
    BaseMask.mem_ladderEven_raw_direct.mpr (by dsimp only; omega)
  have hmem : ∀ x, x ∈ (BaseMask.ladderEven.raw d).sites ↔ x ∈ paperNearLadderTile d := by
    intro x
    obtain ⟨a, b⟩ := x
    rw [BaseMask.mem_ladderEven_raw_direct]
    simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC,
      paperNearLadderD, Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, Prod.mk.injEq, not_or]
    constructor <;> intro h <;> omega
  have hheight : ∀ x (hx : x ∈ (BaseMask.ladderEven.raw d).sites),
      (BaseMask.ladderEven.raw d).height ⟨x, hx⟩ = paperNearLadderValue d x := by
    intro x hx
    classical
    rw [BaseMask.ladderEven_raw_height_direct d ⟨x, hx⟩]
    obtain ⟨a, b⟩ := x
    rw [paperNearLadderValue, Set.indicator_apply]
    dsimp only
    rw [show (a - b) ^ 2 = (b - a) ^ 2 by ring]
    split_ifs with h1 h2 h2 <;>
      simp only [paperNearLadderA, paperNearLadderB, Set.mem_union, Set.mem_setOf_eq,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2 ⊢ <;> omega
  have hmin : ∀ site ∈ (BaseMask.ladderEven.raw d).sites,
      ((0 : ℤ), (1 : ℤ)).2 ≤ site.2 ∧ (((0 : ℤ), (1 : ℤ)).2 = site.2 → ((0 : ℤ), (1 : ℤ)).1 ≤ site.1) := by
    intro site hsite
    obtain ⟨a, b⟩ := site
    rw [BaseMask.mem_ladderEven_raw_direct] at hsite
    dsimp only at hsite ⊢
    omega
  exact nearOne_tile_identity (BaseMask.ladderEven.raw d) ⟨(0, 1), hpt⟩ (paperNearLadderTile d)
    (paperNearLadderValue d) hmem hheight hpt hmin (BaseMask.ladderEven_agrees_rotateLadderField hden hagree)

/-! ### The TeX value at the boundary points -/

/-- The TeX value without the indicator outside `A ∪ B`. -/
theorem nearValue_eq_formula (d x1 x2 : ℤ) (hx : ¬ ((x1, x2) ∈ paperNearLadderA d ∪ paperNearLadderB d)) :
    paperNearLadderValue d (x1, x2) = -((x2 - x1) ^ 2 / 4) + min 0 (d - x2) + min 0 (2 * d - x2) +
      max ((x2 - x1) - d) 0 := by
  unfold paperNearLadderValue
  rw [Set.indicator_of_notMem hx, add_zero]

theorem value_left (k : ℕ) :
    paperNearLadderValue (2 * (k : ℤ) + 4) (-1, 2 * (k : ℤ) + 5) =
      paperNearLadderValue (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 4, 4 * (k : ℤ) + 8) := by
  rw [nearValue_eq_formula _ _ _ (by
      simp only [paperNearLadderA, paperNearLadderB, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq, not_or]
      omega),
    nearValue_eq_formula _ _ _ (by
      simp only [paperNearLadderA, paperNearLadderB, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq, not_or]
      omega)]
  have f1 : (2 * (k : ℤ) + 5 - -1) ^ 2 / 4 = ((k : ℤ) + 3) ^ 2 := by
    rw [show (2 * (k : ℤ) + 5 - -1) ^ 2 = 4 * ((k : ℤ) + 3) ^ 2 by ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  have f2 : (4 * (k : ℤ) + 8 - (2 * (k : ℤ) + 4)) ^ 2 / 4 = ((k : ℤ) + 2) ^ 2 := by
    rw [show (4 * (k : ℤ) + 8 - (2 * (k : ℤ) + 4)) ^ 2 = 4 * ((k : ℤ) + 2) ^ 2 by ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  rw [f1, f2]
  simp only [min_def, max_def]
  split_ifs <;> first | (exfalso; omega) | ring

theorem value_right (k : ℕ) :
    paperNearLadderValue (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 5, 4 * (k : ℤ) + 7) =
      paperNearLadderValue (2 * (k : ℤ) + 4) (0, 2 * (k : ℤ) + 4) := by
  rw [nearValue_eq_formula _ _ _ (by
      simp only [paperNearLadderA, paperNearLadderB, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq, not_or]
      omega),
    nearValue_eq_formula _ _ _ (by
      simp only [paperNearLadderA, paperNearLadderB, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.mk.injEq, not_or]
      omega)]
  have f1 : (4 * (k : ℤ) + 7 - (2 * (k : ℤ) + 5)) ^ 2 / 4 = ((k : ℤ) + 1) ^ 2 := by
    rw [show (4 * (k : ℤ) + 7 - (2 * (k : ℤ) + 5)) ^ 2 = 4 * ((k : ℤ) + 1) ^ 2 by ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  have f2 : (2 * (k : ℤ) + 4 - 0) ^ 2 / 4 = ((k : ℤ) + 2) ^ 2 := by
    rw [show (2 * (k : ℤ) + 4 - 0) ^ 2 = 4 * ((k : ℤ) + 2) ^ 2 by ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  rw [f1, f2]
  simp only [min_def, max_def]
  split_ifs <;> first | (exfalso; omega) | ring

/-! ### The tile points of the polygon -/

theorem mem_tile_top (k : ℕ) : ((2 * (k : ℤ) + 4), 4 * (k : ℤ) + 8) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
  simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
    Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
    not_or]
  omega

theorem mem_tile_zero (k : ℕ) : ((0 : ℤ), 2 * (k : ℤ) + 4) ∈ paperNearLadderTile (2 * (k : ℤ) + 4) := by
  simp only [paperNearLadderTile, paperNearLadderA, paperNearLadderB, paperNearLadderC, paperNearLadderD,
    Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
    not_or]
  omega

/-! ### The physical field on the closed polygon -/

/-- On the closed polygon of `2^(k+1)`, the physical field is the TeX value read at `z + (0,1)`. -/
theorem rotate_eq_on_E (k : ℕ) {S : Field} (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {z : Site} (hz : z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon) :
    rotateLadderField (2 * (k : ℤ) + 4) S z = paperNearLadderValue (2 * (k : ℤ) + 4) (z.1, z.2 + 1) := by
  have hd : 4 ≤ 2 * (k : ℤ) + 4 ∧ (2 * (k : ℤ) + 4) % 2 = 0 := ⟨by omega, by omega⟩
  have hper := twos_physical_periods k hperiod
  rcases closedPolygon_twos_tile k z hz with h | h | h
  · have := rotate_tile_identity hd hagree (z.1, z.2 + 1) h
    simpa using this
  · obtain ⟨z1, z2⟩ := z
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hc := twos_combine_zero k (-1)
    have e := periods_combine hper (2 * (k : ℤ) + 4, 4 * (k : ℤ) + 7) (-1) 0
    rw [hc] at e
    have hpos : ((2 * (k : ℤ) + 4, 4 * (k : ℤ) + 7) : Site) + (-1 * (2 * (k : ℤ) + 5), -1 * (2 * (k : ℤ) + 3)) =
        (-1, 2 * (k : ℤ) + 4) := by
      rw [site_add_mk]
      exact Prod.ext (by ring) (by ring)
    rw [hpos] at e
    have hinc : periodIncrement (frameAt (List.replicate (k + 1) Digit.two)).child 0
        (ladderEvenConstantV (2 * (k : ℤ) + 4)) (2 * (k : ℤ) + 4, 4 * (k : ℤ) + 7) (-1) 0 = 0 := by
      unfold periodIncrement
      simp [chooseTwo]
    rw [hinc, add_zero] at e
    have t := rotate_tile_identity hd hagree (2 * (k : ℤ) + 4, 4 * (k : ℤ) + 8) (mem_tile_top k)
    have hsub : ((2 * (k : ℤ) + 4, 4 * (k : ℤ) + 8) : Site) - (0, 1) = (2 * (k : ℤ) + 4, 4 * (k : ℤ) + 7) := by
      rw [site_sub_mk]
      exact Prod.ext (by ring) (by ring)
    rw [hsub] at t
    show rotateLadderField (2 * (k : ℤ) + 4) S (-1, 2 * (k : ℤ) + 4) =
      paperNearLadderValue (2 * (k : ℤ) + 4) (-1, 2 * (k : ℤ) + 4 + 1)
    rw [e, t, show 2 * (k : ℤ) + 4 + 1 = 2 * (k : ℤ) + 5 by ring]
    exact (value_left k).symm
  · obtain ⟨z1, z2⟩ := z
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hc := twos_combine_zero k 1
    have e := periods_combine hper (0, 2 * (k : ℤ) + 3) 1 0
    rw [hc] at e
    have hpos : ((0, 2 * (k : ℤ) + 3) : Site) + (1 * (2 * (k : ℤ) + 5), 1 * (2 * (k : ℤ) + 3)) =
        (2 * (k : ℤ) + 5, 4 * (k : ℤ) + 6) := by
      rw [site_add_mk]
      exact Prod.ext (by ring) (by ring)
    rw [hpos] at e
    have hinc : periodIncrement (frameAt (List.replicate (k + 1) Digit.two)).child 0
        (ladderEvenConstantV (2 * (k : ℤ) + 4)) (0, 2 * (k : ℤ) + 3) 1 0 = 0 := by
      unfold periodIncrement
      simp [chooseTwo]
    rw [hinc, add_zero] at e
    have t := rotate_tile_identity hd hagree (0, 2 * (k : ℤ) + 4) (mem_tile_zero k)
    have hsub : ((0, 2 * (k : ℤ) + 4) : Site) - (0, 1) = (0, 2 * (k : ℤ) + 3) := by
      rw [site_sub_mk]
      exact Prod.ext (by ring) (by ring)
    rw [hsub] at t
    show rotateLadderField (2 * (k : ℤ) + 4) S (2 * (k : ℤ) + 5, 4 * (k : ℤ) + 6) =
      paperNearLadderValue (2 * (k : ℤ) + 4) (2 * (k : ℤ) + 5, 4 * (k : ℤ) + 6 + 1)
    rw [e, t, show 4 * (k : ℤ) + 6 + 1 = 4 * (k : ℤ) + 7 by ring]
    exact (value_right k).symm

/-! ### The periods of the sheet minimum, and the standard field -/

/-- The sheet minimum of `2^(k+1)` respects the periods on the closed polygon (`hper` of the identification). -/
theorem twos_hper (k : ℕ) {S : Field} (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4))) :
    RespectsPeriodsOn (frameAt (List.replicate (k + 1) Digit.two)).child
      (frameAt (List.replicate (k + 1) Digit.two)).coherentConstantU
      (frameAt (List.replicate (k + 1) Digit.two)).coherentConstantV
      (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon
      ((frameAt (List.replicate (k + 1) Digit.two)).sheetMin
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))) := by
  rw [(twos_coherentConstants k).1, (twos_coherentConstants k).2]
  have hg : ∀ z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon,
      ((frameAt (List.replicate (k + 1) Digit.two)).sheetMin
        (quarterTurnField (standardField (conjWord (List.replicate (k + 1) Digit.two))))) z =
        rotateLadderField (2 * (k : ℤ) + 4) S z := by
    intro z hz
    rw [rotate_eq_on_E k hagree hperiod hz]
    unfold ChildFrame.sheetMin
    exact twos_closed_min k z hz
  unfold RespectsPeriodsOn
  intro y hy i j hy'
  rw [hg _ hy', hg y hy]
  exact periods_combine (twos_physical_periods k hperiod) y i j

/-- The periods of the standard field of `2^(k+1)`: the sewn field of the sheet minimum. -/
theorem twos_standardField_periods (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4))) :
    HasGeneratorPeriods (frameAt (List.replicate (k + 1) Digit.two)).child
      (standardField (List.replicate (k + 1) Digit.two)) 0 (ladderEvenConstantV (2 * (k : ℤ) + 4)) := by
  have hproper : ∃ x ∈ List.replicate (k + 1) Digit.two, x ≠ Digit.three :=
    ⟨Digit.two, by simp, by decide⟩
  have hs := (frameAt (List.replicate (k + 1) Digit.two)).sewnField_spec (twos_hper k hagree hperiod)
  rw [(twos_coherentConstants k).1, (twos_coherentConstants k).2] at hs
  rw [standardField_proper hproper, (twos_coherentConstants k).1, (twos_coherentConstants k).2]
  exact hs.2

/-- The standard field of `2^(k+1)` is the physical near-one field on the whole plane. -/
theorem twos_standardField_eq_rotate (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (z : Site) :
    standardField (List.replicate (k + 1) Digit.two) z = rotateLadderField (2 * (k : ℤ) + 4) S z := by
  have hper := twos_hper k hagree hperiod
  have hF := twos_standardField_periods k hagree hperiod
  obtain ⟨y, hy, i, j, hz⟩ := (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon_covers z
  have hFy : standardField (List.replicate (k + 1) Digit.two) y = rotateLadderField (2 * (k : ℤ) + 4) S y := by
    rw [twos_standardField_eq_on_E k hper y hy, rotate_eq_on_E k hagree hperiod hy]
  rw [hz, periods_combine hF y i j, periods_combine (twos_physical_periods k hperiod) y i j, hFy]

/-- The packet of the standard field of `2^(k+1)`: the periods and the reflection and binarity come from the physical
field; the zero and harmonic strip facts on the closed polygon are the hypotheses `hzero`, `hharm`. -/
theorem twos_packet_standard (k : ℕ)
    (hzero : ∀ z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon,
      1 - (frameAt (List.replicate (k + 1) Digit.two)).child.den ≤
        (frameAt (List.replicate (k + 1) Digit.two)).tGrade z →
      standardField (List.replicate (k + 1) Digit.two) z = 0)
    (hharm : ∀ z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon,
      (frameAt (List.replicate (k + 1) Digit.two)).sGrade z ≤
        2 * ((frameAt (List.replicate (k + 1) Digit.two)).child.den +
          (frameAt (List.replicate (k + 1) Digit.two)).child.num) - 1 →
      standardField (List.replicate (k + 1) Digit.two) z = harmonicGrid z) :
    (frameAt (List.replicate (k + 1) Digit.two)).Packet
      (standardField (List.replicate (k + 1) Digit.two)) := by
  obtain ⟨S, hagree, hperiod, -⟩ := ladderOdd_exists_extension (show BaseMask.ladderOdd.Valid (2 * (k : ℤ) + 4) from
    ⟨by omega, by omega⟩)
  have hden : BaseMask.ladderOdd.Valid (2 * (k : ℤ) + 4) := ⟨by omega, by omega⟩
  have hfun : standardField (List.replicate (k + 1) Digit.two) = rotateLadderField (2 * (k : ℤ) + 4) S :=
    funext (twos_standardField_eq_rotate k hagree hperiod)
  refine (frameAt (List.replicate (k + 1) Digit.two)).packet_of_stripInputs ?_ ?_ ?_
  · rw [(twos_coherentConstants k).1, (twos_coherentConstants k).2]
    exact twos_standardField_periods k hagree hperiod
  · refine ⟨hzero, hharm, fun z _ => ?_⟩
    rw [hfun, twos_centre k, twos_tGrade k, twos_symmetryConstant k]
    have h := rotateLadderField_reflection hden hagree hperiod z
    rw [show (2 * (k : ℤ) + 4 - 1) = 2 * (k : ℤ) + 3 by ring,
      show (2 * (k : ℤ) + 4 + 1) = 2 * (k : ℤ) + 5 by ring] at h
    exact h
  · intro z _
    rw [hfun]
    exact rotateLadderField_binary hden hagree hperiod z

end FLatticePaper.Induction
