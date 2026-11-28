import FLatticePaper.Tiles.PartialBoundary
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel

/-! # Translating a respected string

Shifting the placed tiles of a string by `v`, and reading the odometer at the shifted argument, preserves `RespectsTiles`.
The shifted family keeps the affine factors `a_k` and replaces the constants `b_k` by `b_k − a_k · v`: then its `k`-th odometer is
the old one at `x − v`. The slopes are those of the old sets (`slopeOf_translate`: the unit squares of a translated set are the
translated unit squares), and the boundary conditions are invariant, since the terms `a_k · v` cancel on both sides.

Unlike `LSidesEven.respectsTiles_add_const` (an additive constant on the values), this is a shift of the argument. -/

namespace FLatticePaper.Tiles.RespectsTranslate

open FLatticePaper.Tiles

/-- Membership in a translated list: `y ∈ T.map (· + v)` exactly when `y − v ∈ T`. -/
theorem mem_map_add_iff (T : List GInt) (v y : GInt) : y ∈ T.map (· + v) ↔ y - v ∈ T := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
    simpa using ha
  · intro h
    exact List.mem_map.mpr ⟨y - v, h, by simp⟩

/-- The unit squares of a translated set are the translated unit squares. -/
theorem unitSquares_map_add (T : List GInt) (v : GInt) :
    unitSquares (T.map (· + v)) = (unitSquares T).map (· + v) := by
  unfold unitSquares
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  have e1 : x + v + (1, 0) - v = x + (1, 0) := by abel
  have e2 : x + v + (0, 1) - v = x + (0, 1) := by abel
  have e3 : x + v + (1, 1) - v = x + (1, 1) := by abel
  simp only [Function.comp_apply, mem_map_add_iff, e1, e2, e3]

/-- **The slope is invariant under translation.** The odometer read at the shifted argument, on the shifted set, has the slope of
the odometer on the set. -/
theorem slopeOf_translate (f : GInt → ℤ) (T : List GInt) (v : GInt) :
    slopeOf (fun x => f (x - v)) (T.map (· + v)) = slopeOf f T := by
  have e0 : ∀ x : GInt, x + v - v = x := fun x => by abel
  have e1 : ∀ x : GInt, x + v + (1, 0) - v = x + (1, 0) := fun x => by abel
  have e2 : ∀ x : GInt, x + v + (0, 1) - v = x + (0, 1) := fun x => by abel
  have e3 : ∀ x : GInt, x + v + (1, 1) - v = x + (1, 1) := fun x => by abel
  simp only [slopeOf, unitSquares_map_add, List.map_map, List.length_map, Function.comp_def, e0, e1, e2, e3]

/-- The shifted family: the tiles translated by `v`, the factors `a_k` kept, the constants `b_k − a_k · v`. -/
def shiftFam (F : PTFamily) (v : GInt) : PTFamily :=
  ⟨F.ts.map (fun t => (t.1, t.2 + v)), F.a, fun k => F.b k - ((F.a k).1 * v.1 + (F.a k).2 * v.2)⟩

theorem shiftFam_n (F : PTFamily) (v : GInt) : (shiftFam F v).n = F.n := by
  simp [PTFamily.n, shiftFam]

theorem shiftFam_tile (F : PTFamily) (v : GInt) (k : ℕ) (hk : k < F.n) :
    (shiftFam F v).tile k = ((F.tile k).1, (F.tile k).2 + v) := by
  have hk' : k < F.ts.length := hk
  unfold PTFamily.tile shiftFam
  simp only
  rw [List.getD_eq_getElem _ _ (by simpa using hk'), List.getD_eq_getElem _ _ hk', List.getElem_map]

theorem shiftFam_dom (F : PTFamily) (v : GInt) (k : ℕ) (hk : k < F.n) :
    (shiftFam F v).dom k = (F.dom k).map (· + v) := by
  unfold PTFamily.dom
  rw [shiftFam_tile F v k hk]
  simp only [List.map_map, Function.comp_def, add_assoc]

theorem shiftFam_odo (F : PTFamily) (v : GInt) (k : ℕ) (hk : k < F.n) (x : GInt) :
    (shiftFam F v).odo k x = F.odo k (x - v) := by
  unfold PTFamily.odo
  rw [shiftFam_tile F v k hk]
  have e : x - ((F.tile k).2 + v) = x - v - (F.tile k).2 := by abel
  simp only [shiftFam, Prod.fst_sub, Prod.snd_sub]
  rw [e]
  ring

/-- **Translating a respected string.** If `S` respects the string `ts` (reversed when `rev`), then the odometer `x ↦ S (x − v)`
respects the string translated by `v`. -/
theorem respectsTiles_translate (o : Orientation) (rev : Bool) (ts : List (ZTile × GInt)) (S : GInt → ℤ) (v : GInt)
    (h : RespectsTiles o rev ts S) :
    RespectsTiles o rev (ts.map (fun t => (t.1, t.2 + v))) (fun x => S (x - v)) := by
  obtain ⟨F, hts, hval, hresp⟩ := h
  refine ⟨shiftFam F v, ?_, ?_, ?_⟩
  · rw [← hts]
    rfl
  · intro k hk x hx
    have hk' : k < F.n := by rwa [shiftFam_n] at hk
    rw [shiftFam_dom F v k hk'] at hx
    have hx' : x - v ∈ F.dom k := (mem_map_add_iff _ _ _).mp hx
    show S (x - v) = (shiftFam F v).odo k x
    rw [shiftFam_odo F v k hk' x]
    exact hval k hk' (x - v) hx'
  · intro k hk
    have hk' : k + 1 < F.n := by rwa [shiftFam_n] at hk
    have hk0 : k < F.n := by omega
    obtain ⟨h1, h2⟩ := hresp k hk'
    refine ⟨?_, fun hne x hx y hy hxy => ?_⟩
    · have ho1 : (shiftFam F v).odo (k + 1) = fun x => F.odo (k + 1) (x - v) := by
        funext x; exact shiftFam_odo F v (k + 1) hk' x
      have ho0 : (shiftFam F v).odo k = fun x => F.odo k (x - v) := by
        funext x; exact shiftFam_odo F v k hk0 x
      have hd1 : (shiftFam F v).dom (k + 1) = (F.dom (k + 1)).map (· + v) := shiftFam_dom F v (k + 1) hk'
      have hd0 : (shiftFam F v).dom k = (F.dom k).map (· + v) := shiftFam_dom F v k hk0
      have ht0 : ((shiftFam F v).tile k).1 = (F.tile k).1 := by rw [shiftFam_tile F v k hk0]
      have ht1 : ((shiftFam F v).tile (k + 1)).1 = (F.tile (k + 1)).1 := by
        rw [shiftFam_tile F v (k + 1) hk']
      rw [ho1, ho0, hd1, hd0, slopeOf_translate, slopeOf_translate, ht0, ht1]
      exact h1
    · have hne' : ¬ ∃ z, z ∈ F.dom k ∧ z ∈ F.dom (k + 1) := by
        rintro ⟨z, hz1, hz2⟩
        apply hne
        refine ⟨z + v, ?_, ?_⟩
        · rw [shiftFam_dom F v k (by omega)]
          exact List.mem_map.mpr ⟨z, hz1, rfl⟩
        · rw [shiftFam_dom F v (k + 1) hk']
          exact List.mem_map.mpr ⟨z, hz2, rfl⟩
      have hx' : x - v ∈ F.dom k := by
        rw [shiftFam_dom F v k (by omega)] at hx
        exact (mem_map_add_iff _ _ _).mp hx
      have hy' : y - v ∈ F.dom (k + 1) := by
        rw [shiftFam_dom F v (k + 1) hk'] at hy
        exact (mem_map_add_iff _ _ _).mp hy
      have hxy' : unitApart (x - v) (y - v) := by
        unfold unitApart at hxy ⊢
        have e1 : (x - v).1 - (y - v).1 = x.1 - y.1 := by simp
        have e2 : (x - v).2 - (y - v).2 = x.2 - y.2 := by simp
        rw [e1, e2]
        exact hxy
      obtain ⟨h3, h4⟩ := h2 hne' (x - v) hx' (y - v) hy' hxy'
      rw [shiftFam_odo F v k (by omega) x, shiftFam_odo F v (k + 1) hk' y]
      simp only [shiftFam]
      refine ⟨fun ho => ?_, fun ho => ?_⟩
      · have := h3 ho
        simp only [ptDot, Prod.fst_sub, Prod.snd_sub] at this ⊢
        linear_combination this
      · have := h4 ho
        simp only [ptDot, Prod.fst_sub, Prod.snd_sub] at this ⊢
        linear_combination this

end FLatticePaper.Tiles.RespectsTranslate
