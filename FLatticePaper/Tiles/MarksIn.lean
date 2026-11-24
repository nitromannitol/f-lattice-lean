import FLatticePaper.Tiles.VBase
import FLatticePaper.Tiles.BaseInvariant
import FLatticePaper.Tiles.SiteLowLeft
import FLatticePaper.Tiles.SiteSourcesAll
import FLatticePaper.Tiles.StandardHalfTurn

/-! Task 53, marksIn: the marked sites of every standard tile lie in the tile.

`markedSites T wh vw` is the forward horizontal string of `wh` at `c(T) = (0,0)`, the reversed vertical string of `vw` shifted by
`(-1,-1)`, and the half-turn images of both. The horizontal sites lie in the tile by `BaseInvariant.horizontal_marks`, the vertical
ones by `VBase.vertical_marks` (through `stringSites true true = VS0` shifted by `(1,1)`), and the half-turn images lie in the tile
because every standard tile is centrally symmetric (`rot (rot T) = shift T v`): the centre of the half-turn is `-v`. -/

namespace FLatticePaper.Tiles.MarksIn

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.SiteJunction FLatticePaper.Tiles.SiteConcat FLatticePaper.Tiles.VJunction
open FLatticePaper.Tiles.VBase FLatticePaper.Tiles.BaseInvariant FLatticePaper.Tiles.HorizontalGlue
open FLatticePaper.Tiles.StandardHalfTurn FLatticePaper.Tiles.SiteLowLeft FLatticePaper.Tiles.VGlue
open FLatticePaper.Tiles.SiteInduction

/-! ### The central symmetry of a tile -/

theorem rot_rot_mem (T : Tile) (v : ℤ × ℤ) (h : rot (rot T) = shift T v) (z : ℤ × ℤ) (hz : z ∈ T) :
    (-z.1 - v.1, -z.2 - v.2) ∈ T := by
  have hx : ((-z.1, -z.2) : ℤ × ℤ) ∈ rot (rot T) := by
    rw [mem_rot, mem_rot]
    simpa using hz
  rw [h, mem_shift] at hx
  have e : ((-z.1, -z.2) : ℤ × ℤ) - v = (-z.1 - v.1, -z.2 - v.2) := by
    ext <;> simp
  rw [e] at hx
  exact hx

theorem minX_eq (T : Tile) (hT : T.Nonempty) :
    minX T = (T.image Prod.fst).min' (hT.image Prod.fst) := by
  unfold minX
  rw [← Finset.coe_min' (hT.image Prod.fst)]
  rfl

theorem maxX_eq (T : Tile) (hT : T.Nonempty) :
    maxX T = (T.image Prod.fst).max' (hT.image Prod.fst) := by
  unfold maxX
  rw [← Finset.coe_max' (hT.image Prod.fst)]
  rfl

theorem minY_eq (T : Tile) (hT : T.Nonempty) :
    minY T = (T.image Prod.snd).min' (hT.image Prod.snd) := by
  unfold minY
  rw [← Finset.coe_min' (hT.image Prod.snd)]
  rfl

theorem maxY_eq (T : Tile) (hT : T.Nonempty) :
    maxY T = (T.image Prod.snd).max' (hT.image Prod.snd) := by
  unfold maxY
  rw [← Finset.coe_max' (hT.image Prod.snd)]
  rfl

theorem minX_le (T : Tile) (hT : T.Nonempty) (z : ℤ × ℤ) (hz : z ∈ T) : minX T ≤ z.1 := by
  rw [minX_eq T hT]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem Prod.fst hz)

theorem le_maxX (T : Tile) (hT : T.Nonempty) (z : ℤ × ℤ) (hz : z ∈ T) : z.1 ≤ maxX T := by
  rw [maxX_eq T hT]
  exact Finset.le_max' _ _ (Finset.mem_image_of_mem Prod.fst hz)

theorem minY_le (T : Tile) (hT : T.Nonempty) (z : ℤ × ℤ) (hz : z ∈ T) : minY T ≤ z.2 := by
  rw [minY_eq T hT]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem Prod.snd hz)

theorem le_maxY (T : Tile) (hT : T.Nonempty) (z : ℤ × ℤ) (hz : z ∈ T) : z.2 ≤ maxY T := by
  rw [maxY_eq T hT]
  exact Finset.le_max' _ _ (Finset.mem_image_of_mem Prod.snd hz)

theorem exists_minX (T : Tile) (hT : T.Nonempty) : ∃ p ∈ T, p.1 = minX T := by
  obtain ⟨p, hp, hpx⟩ := Finset.mem_image.1 (Finset.min'_mem (T.image Prod.fst) (hT.image Prod.fst))
  exact ⟨p, hp, by rw [minX_eq T hT]; exact hpx⟩

theorem exists_maxX (T : Tile) (hT : T.Nonempty) : ∃ p ∈ T, p.1 = maxX T := by
  obtain ⟨p, hp, hpx⟩ := Finset.mem_image.1 (Finset.max'_mem (T.image Prod.fst) (hT.image Prod.fst))
  exact ⟨p, hp, by rw [maxX_eq T hT]; exact hpx⟩

theorem exists_minY (T : Tile) (hT : T.Nonempty) : ∃ p ∈ T, p.2 = minY T := by
  obtain ⟨p, hp, hpx⟩ := Finset.mem_image.1 (Finset.min'_mem (T.image Prod.snd) (hT.image Prod.snd))
  exact ⟨p, hp, by rw [minY_eq T hT]; exact hpx⟩

theorem exists_maxY (T : Tile) (hT : T.Nonempty) : ∃ p ∈ T, p.2 = maxY T := by
  obtain ⟨p, hp, hpx⟩ := Finset.mem_image.1 (Finset.max'_mem (T.image Prod.snd) (hT.image Prod.snd))
  exact ⟨p, hp, by rw [maxY_eq T hT]; exact hpx⟩

/-- The centre of the half-turn of a tile with central symmetry `z ↦ -z - v` is `-v`. -/
theorem halfTurn_centre (T : Tile) (v : ℤ × ℤ) (hT : T.Nonempty)
    (hsym : ∀ z ∈ T, (-z.1 - v.1, -z.2 - v.2) ∈ T) :
    minX T + maxX T = -v.1 ∧ minY T + maxY T = -v.2 := by
  obtain ⟨p, hp, hpx⟩ := exists_minX T hT
  obtain ⟨q, hq, hqx⟩ := exists_maxX T hT
  obtain ⟨p', hp', hpy⟩ := exists_minY T hT
  obtain ⟨q', hq', hqy⟩ := exists_maxY T hT
  have h1 := le_maxX T hT _ (hsym p hp)
  have h2 := minX_le T hT _ (hsym q hq)
  have h3 := le_maxY T hT _ (hsym p' hp')
  have h4 := minY_le T hT _ (hsym q' hq')
  simp only at h1 h2 h3 h4
  constructor <;> omega

theorem halfTurn_mem (T : Tile) (v : ℤ × ℤ) (h : rot (rot T) = shift T v) (y : ℤ × ℤ) (hy : y ∈ T) :
    halfTurn T y ∈ T := by
  have hT : T.Nonempty := ⟨y, hy⟩
  have hsym : ∀ z ∈ T, (-z.1 - v.1, -z.2 - v.2) ∈ T := fun z hz => rot_rot_mem T v h z hz
  obtain ⟨hx, hy'⟩ := halfTurn_centre T v hT hsym
  have e : halfTurn T y = (-v.1 - y.1, -v.2 - y.2) := by
    simp only [halfTurn, halfTurnCentre]
    rw [hx, hy']
  rw [e]
  have e2 : ((-v.1 - y.1, -v.2 - y.2) : ℤ × ℤ) = (-y.1 - v.1, -y.2 - v.2) := by
    ext <;> ring
  rw [e2]
  exact hsym y hy

theorem halfTurn_oddTile (w : Word) (y : ℤ × ℤ) (hy : y ∈ oddTile w) : halfTurn (oddTile w) y ∈ oddTile w :=
  halfTurn_mem _ _ (rot_rot_oddTile w) y hy

theorem halfTurn_evenTile (w : Word) (y : ℤ × ℤ) (hy : y ∈ evenTile w) : halfTurn (evenTile w) y ∈ evenTile w :=
  halfTurn_mem _ _ (rot_rot_evenTile w) y hy

/-! ### The vertical sites -/

theorem stringSites_true_iff (L : List Letter) (y : ℤ × ℤ) :
    y ∈ stringSites true true L ↔ (y.1 - 1, y.2 - 1) ∈ VS0 L := by
  have hmap : stringSites true true L = (VS0 L).map (fun z => z + (1, 1)) := by
    rw [stringSites_eq_sitesFrom]
    have hs : startPos true true = (1, 1) := rfl
    rw [hs]
    have h := sitesFrom_translate_gen true true none (0, 0) (1, 1) L
    have h11 : ((0 : ℤ), (0 : ℤ)) + ((1 : ℤ), (1 : ℤ)) = ((1 : ℤ), (1 : ℤ)) := by ext <;> simp
    rw [h11] at h
    exact h
  rw [hmap, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨(y.1 - 1, y.2 - 1), h, by ext <;> simp⟩

/-! ### The marked sites -/

theorem markedSites_eq (T : Tile) (wh vw : List Letter) (hc : lowLeft T = (0, 0)) :
    markedSites T wh vw =
      (stringSites false false wh).map (fun z => (z.1 + 0, z.2 + 0)) ++
        (stringSites true true vw.reverse).map (fun z => (z.1 + 0 - 1, z.2 + 0 - 1)) ++
        ((stringSites false false wh).map (fun z => (z.1 + 0, z.2 + 0))).map (halfTurn T) ++
        ((stringSites true true vw.reverse).map (fun z => (z.1 + 0 - 1, z.2 + 0 - 1))).map (halfTurn T) := by
  unfold markedSites
  rw [hc]

theorem markedSites_sub (T : Tile) (wh vw : List Letter) (hc : lowLeft T = (0, 0))
    (hSh : ∀ y ∈ stringSites false false wh, y ∈ T)
    (hSv : ∀ y ∈ stringSites true true vw.reverse, (y.1 - 1, y.2 - 1) ∈ T)
    (hhalf : ∀ y ∈ T, halfTurn T y ∈ T) : ∀ z ∈ markedSites T wh vw, z ∈ T := by
  intro z hz
  rw [markedSites_eq T wh vw hc] at hz
  have hS : ∀ a ∈ (stringSites false false wh).map (fun z => (z.1 + 0, z.2 + 0)), a ∈ T := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    simpa using hSh b hb
  have hV : ∀ a ∈ (stringSites true true vw.reverse).map (fun z => (z.1 + 0 - 1, z.2 + 0 - 1)), a ∈ T := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    simpa using hSv b hb
  rcases List.mem_append.1 hz with hz1 | hz2
  · rcases List.mem_append.1 hz1 with hz3 | hz4
    · rcases List.mem_append.1 hz3 with hz5 | hz6
      · exact hS z hz5
      · exact hV z hz6
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hz4
      exact hhalf a (hS a ha)
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hz2
    exact hhalf a (hV a ha)

theorem marksOdd_sub (w : Word) :
    marksOdd w ⊆ ((oddTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
  intro z hz
  apply Finset.mem_coe.2
  have hSh : ∀ y ∈ stringSites false false (hWordOf w false), y ∈ oddTile w := (horizontal_marks w).1
  have hSv : ∀ y ∈ stringSites true true (vWordOf w false).reverse, (y.1 - 1, y.2 - 1) ∈ oddTile w := by
    intro y hy
    exact (vertical_marks w).1 _ ((stringSites_true_iff _ y).1 hy)
  exact markedSites_sub (oddTile w) (hWordOf w false) (vWordOf w false) (lowLeft_oddTile w) hSh hSv
    (halfTurn_oddTile w) z hz

theorem marksEven_sub (w : Word) :
    marksEven w ⊆ ((evenTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
  intro z hz
  apply Finset.mem_coe.2
  have hSh : ∀ y ∈ stringSites false false (hWordOf w true), y ∈ evenTile w := (horizontal_marks w).2
  have hSv : ∀ y ∈ stringSites true true (vWordOf w true).reverse, (y.1 - 1, y.2 - 1) ∈ evenTile w := by
    intro y hy
    exact (vertical_marks w).2 _ ((stringSites_true_iff _ y).1 hy)
  exact markedSites_sub (evenTile w) (hWordOf w true) (vWordOf w true) (lowLeft_evenTile w) hSh hSv
    (halfTurn_evenTile w) z hz

/-- **The marked sites of every standard tile lie in the tile**: the hypothesis `marksIn` of the four-string record. -/
theorem marks_all (w : Word) :
    marksOdd w ⊆ ((oddTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) ∧
      marksEven w ⊆ ((evenTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) :=
  ⟨marksOdd_sub w, marksEven_sub w⟩

/-- **Clause (b) without hypotheses**: the four-string predicate of every standard tile. -/
theorem standard_fourStrings_unconditional (w : Word) (par : Bool) : StandardFourStrings w par :=
  FLatticePaper.Tiles.SiteSourcesAll.standard_fourStrings_all marks_all w par

end FLatticePaper.Tiles.MarksIn
