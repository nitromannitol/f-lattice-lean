import FLatticePaper.Tiles.ZeroOneGeneral

/-! Slopes of translated and affinely shifted partial odometers (task 16). -/

namespace FLatticePaper.Tiles
open Finset

theorem sum_map_add_const (S : List Site) (g : Site → ℚ) (k : ℚ) :
    (S.map fun x => g x + k).sum = (S.map g).sum + S.length * k := by
  induction S with
  | nil => simp
  | cons x S ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; push_cast; ring

theorem mem_map_add_iff (T : List Site) (c z : Site) : z ∈ T.map (· + c) ↔ z - c ∈ T := by
  constructor
  · intro h
    obtain ⟨y, hy, hyz⟩ := List.mem_map.mp h
    have : z - c = y := by rw [← hyz]; abel
    rw [this]; exact hy
  · intro h
    exact List.mem_map.mpr ⟨z - c, h, by abel⟩

theorem unitSquares_map_add (T : List Site) (c : Site) :
    unitSquares (T.map (· + c)) = (unitSquares T).map (· + c) := by
  unfold unitSquares
  rw [List.filter_map]
  apply congrArg
  apply List.filter_congr
  intro x _
  have e : ∀ e : Site, x + c + e - c = x + e := fun e => by abel
  simp only [Function.comp_apply, mem_map_add_iff, e]

theorem slopeOf_translate (f : Site → ℤ) (T : List Site) (c : Site) :
    slopeOf (fun x => f (x - c)) (T.map (· + c)) = slopeOf f T := by
  have e1 : ∀ x e : Site, x + c + e - c = x + e := fun x e => by abel
  have e0 : ∀ x : Site, x + c - c = x := fun x => by abel
  simp only [slopeOf, unitSquares_map_add, List.length_map, List.map_map, Function.comp_def, e1, e0]

/-- The real-part term of one unit square, as in `slopeOf`. -/
def reTerm (f : Site → ℤ) (x : Site) : ℚ :=
  (((f (x + (1, 0)) : ℚ) - (f x : ℚ) + ((f (x + (1, 1)) : ℚ) - (f (x + (0, 1)) : ℚ))) / 2)

/-- The imaginary-part term of one unit square, as in `slopeOf`. -/
def imTerm (f : Site → ℤ) (x : Site) : ℚ :=
  (((f (x + (0, 1)) : ℚ) - (f x : ℚ) + ((f (x + (1, 1)) : ℚ) - (f (x + (1, 0)) : ℚ))) / 2)

theorem slopeOf_fst (f : Site → ℤ) (T : List Site) :
    (slopeOf f T).1 = ((unitSquares T).map (reTerm f)).sum / ((unitSquares T).length : ℚ) := rfl

theorem slopeOf_snd (f : Site → ℤ) (T : List Site) :
    (slopeOf f T).2 = ((unitSquares T).map (imTerm f)).sum / ((unitSquares T).length : ℚ) := rfl

theorem reTerm_affine (f : Site → ℤ) (a : Site) (κ : ℤ) :
    reTerm (fun y => f y + dotS a y + κ) = fun x => reTerm f x + (a.1 : ℚ) := by
  funext x
  unfold reTerm dotS
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast
  ring

theorem imTerm_affine (f : Site → ℤ) (a : Site) (κ : ℤ) :
    imTerm (fun y => f y + dotS a y + κ) = fun x => imTerm f x + (a.2 : ℚ) := by
  funext x
  unfold imTerm dotS
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast
  ring

theorem slopeOf_affine_fst (f : Site → ℤ) (T : List Site) (a : Site) (κ : ℤ)
    (hn : ((unitSquares T).length : ℚ) ≠ 0) :
    (slopeOf (fun x => f x + dotS a x + κ) T).1 = (slopeOf f T).1 + (a.1 : ℚ) := by
  rw [slopeOf_fst, slopeOf_fst, reTerm_affine, sum_map_add_const, add_div, mul_div_cancel_left₀ _ hn]

theorem slopeOf_affine_snd (f : Site → ℤ) (T : List Site) (a : Site) (κ : ℤ)
    (hn : ((unitSquares T).length : ℚ) ≠ 0) :
    (slopeOf (fun x => f x + dotS a x + κ) T).2 = (slopeOf f T).2 + (a.2 : ℚ) := by
  rw [slopeOf_snd, slopeOf_snd, imTerm_affine, sum_map_add_const, add_div, mul_div_cancel_left₀ _ hn]

theorem slopeOf_affine (f : Site → ℤ) (T : List Site) (a : Site) (κ : ℤ)
    (hT : unitSquares T ≠ []) :
    slopeOf (fun x => f x + dotS a x + κ) T = slopeOf f T + ((a.1 : ℚ), (a.2 : ℚ)) := by
  have hn : ((unitSquares T).length : ℚ) ≠ 0 := by
    have : (unitSquares T).length ≠ 0 := fun h => hT (List.eq_nil_of_length_eq_zero h)
    exact_mod_cast this
  exact Prod.ext (by rw [Prod.fst_add]; exact slopeOf_affine_fst f T a κ hn)
    (by rw [Prod.snd_add]; exact slopeOf_affine_snd f T a κ hn)

end FLatticePaper.Tiles
