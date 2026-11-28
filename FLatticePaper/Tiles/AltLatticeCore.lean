import FLatticePaper.Tiles.JointFamily

/-! # Item (b) of `lemma:weak_alternate_odometer_properties`: the reduction through the half-turn

For a partial odometer `o` and a period `v` with affine factor `a`, the defect `g(x) = o(x + v) - o(x) - aᵀx` on
`O_v = {x : x, x + v ∈ dom o}` is constant exactly when `o` is `LatticeSelfCompatible` along `v`. If `o` has a half-turn
identity `2(o(D - y) - o(y)) = Lᵀy + M` on its domain (as (b) of `lemma:tile-odometer-existence`), then `x ↦ D - v - x` maps
`O_v` to itself and `2 g(D - v - x) = -2 g(x) + K₀` with `K₀ = -Lᵀv - 2aᵀ(D - v)` (`defect_halfTurn`). This is the route of the
proof of Case 4 in the text (surgical 7712fe2): the constant on a completely shared subtile, which the half-turn maps to itself,
is `K₀ / 4`, and it suffices to show `4 g = K₀` at the remaining sites (`latticeSelfCompatible_of_four`). -/

namespace FLatticePaper.Tiles.AltLatticeCore

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily (LatticeSelfCompatible)

/-- The defect of `o` along `v` with the affine factor `a`. -/
def defect (o : PartialOdometer) (v a x : Site) : ℤ := o.val (x + v) - o.val x - dotS a x

/-- A half-turn identity of `o` about `D`, with the affine part `Lᵀy + M` (doubled). -/
def HalfTurnId (o : PartialOdometer) (D L : Site) (M : ℤ) : Prop :=
  ∀ y ∈ o.dom, D - y ∈ o.dom ∧ 2 * (o.val (D - y) - o.val y) = dotS L y + M

theorem dotS_add (u x y : Site) : dotS u (x + y) = dotS u x + dotS u y := by
  unfold dotS; simp only [Prod.fst_add, Prod.snd_add]; ring

theorem dotS_sub (u x y : Site) : dotS u (x - y) = dotS u x - dotS u y := by
  unfold dotS; simp only [Prod.fst_sub, Prod.snd_sub]; ring

/-- **The half-turn on the defect.** -/
theorem defect_halfTurn (o : PartialOdometer) (D L v a : Site) (M : ℤ) (h : HalfTurnId o D L M) (x : Site)
    (hx : x ∈ o.dom) (hxv : x + v ∈ o.dom) :
    D - v - x ∈ o.dom ∧ D - v - x + v ∈ o.dom ∧
      2 * defect o v a (D - v - x) = -2 * defect o v a x - dotS L v - 2 * dotS a (D - v) := by
  obtain ⟨h1, e1⟩ := h x hx
  obtain ⟨h2, e2⟩ := h (x + v) hxv
  have k1 : D - v - x + v = D - x := by abel
  have k2 : D - (x + v) = D - v - x := by abel
  rw [k2] at h2 e2
  refine ⟨h2, by rw [k1]; exact h1, ?_⟩
  unfold defect
  rw [k1]
  rw [dotS_add] at e2
  have e3 : dotS a (D - v - x) = dotS a (D - v) - dotS a x := dotS_sub a (D - v) x
  rw [e3]
  linarith

/-- If `4 g = K` on all of `O_v`, the defect is constant. -/
theorem latticeSelfCompatible_of_four (o : PartialOdometer) (v a : Site) (K : ℤ)
    (h : ∀ x ∈ o.dom, x + v ∈ o.dom → 4 * defect o v a x = K) : LatticeSelfCompatible o v a := by
  by_cases hne : ∃ x, x ∈ o.dom ∧ x + v ∈ o.dom
  · obtain ⟨x0, h0, h0v⟩ := hne
    refine ⟨defect o v a x0, fun x hx hxv => ?_⟩
    have a1 := h x hx hxv
    have a2 := h x0 h0 h0v
    have : defect o v a x = defect o v a x0 := by omega
    unfold defect at this
    exact this
  · refine ⟨0, fun x hx hxv => absurd ⟨x, hx, hxv⟩ hne⟩

/-- On a region of `O_v` mapped to itself by `x ↦ D - v - x` and on which the defect is constant, `4 g = K₀`. -/
theorem four_of_invariant (o : PartialOdometer) (D L v a : Site) (M : ℤ) (h : HalfTurnId o D L M) (R : Set Site)
    (hR : ∀ x ∈ R, x ∈ o.dom ∧ x + v ∈ o.dom) (hinv : ∀ x ∈ R, D - v - x ∈ R) (c : ℤ)
    (hc : ∀ x ∈ R, defect o v a x = c) (x : Site) (hx : x ∈ R) :
    4 * defect o v a x = -dotS L v - 2 * dotS a (D - v) := by
  obtain ⟨hx1, hx2⟩ := hR x hx
  have e := (defect_halfTurn o D L v a M h x hx1 hx2).2.2
  rw [hc _ (hinv x hx), hc x hx] at e
  rw [hc x hx]
  linarith

end FLatticePaper.Tiles.AltLatticeCore
