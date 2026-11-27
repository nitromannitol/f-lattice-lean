import FLatticePaper.Tiles.JointFamily

/-! # (a) of `lemma:tile-odometer-existence` from the corner values

Surgical edition 274ad18, proof of `lemma:tile-odometer-existence`, first paragraph: a standard tile odometer is a weak standard
odometer, so, normalised (`o = o_{1/1}` on the first tile `A` at `c(T) = 0`), the boundary-string formulas of Step 1 of
`lemma:weak_standard_odometer_properties` give its values at the corners (`eq:std_corner_values`, with `X = v_{n/d,1}`,
`Y = v_{n/d,2}`, `e = a_{n/d,2}`, `F = -h_0`): `o(0) = o(1) = o(X - i) = o(X) = 0` and `o(Y + 1) = F(Y) + e_1`,
`o(Y + 1 - i) = o(D) = F(Y) + e_1 - e_2`, `o(D - 1) = F(Y) - e_2`. With the compatibility of lattice adjacent copies ((c) of the
weak lemma, `LatticeSelfCompatible`), the value at one point of each intersection gives the constants of (a): `o(x + X) = o(x)` and
`o(x + Y) = o(x) + e^T x - h_0(Y)` (`tileTranslation_of_corners`). The corner values themselves are an input here. -/

namespace FLatticePaper.Tiles.TileTranslation

open FLatticePaper.Farey
open FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily

/-- `eq:std_corner_values` for the normalised odometer `o - α^T x - β`, with `D = X + Y + 1 - i`, `F = -h_0`, `e = a_{n/d,2}`, and
the corner points in the domain. -/
def StdCornerValues (o : PartialOdometer) (α : Site) (β : ℤ) (X Y e : Site) : Prop :=
  let N := normed o α β
  let D : Site := X + Y + ((1 : ℤ), (-1 : ℤ))
  ((0 : Site) ∈ o.dom ∧ N 0 = 0) ∧ (((1 : ℤ), (0 : ℤ)) ∈ o.dom ∧ N (1, 0) = 0) ∧
    (X - ((0 : ℤ), (1 : ℤ)) ∈ o.dom ∧ N (X - (0, 1)) = 0) ∧ (X ∈ o.dom ∧ N X = 0) ∧
    (Y + ((1 : ℤ), (0 : ℤ)) ∈ o.dom ∧ N (Y + (1, 0)) = -h0 Y + e.1) ∧
    (Y + ((1 : ℤ), (-1 : ℤ)) ∈ o.dom ∧ N (Y + (1, -1)) = -h0 Y + e.1 - e.2) ∧
    (D ∈ o.dom ∧ N D = -h0 Y + e.1 - e.2) ∧
    (D - ((1 : ℤ), (0 : ℤ)) ∈ o.dom ∧ N (D - (1, 0)) = -h0 Y - e.2)

/-- (a) of `lemma:tile-odometer-existence`, from the normalisation, the corner values and the compatibility of lattice adjacent
copies in both directions. -/
theorem tileTranslation_of_corners (o : PartialOdometer) (X Y e : Site) (α : Site) (β : ℤ)
    (hN : FirstTileNormal o α β) (hV : StdCornerValues o α β X Y e)
    (hcX : LatticeSelfCompatible o X 0) (hcY : LatticeSelfCompatible o Y e) :
    TileTranslation o X Y e := by
  obtain ⟨⟨h0m, h0v⟩, ⟨h1m, h1v⟩, -, ⟨hXm, hXv⟩, ⟨hYm, hYv⟩, -⟩ := hV
  obtain ⟨c, hc⟩ := hcX
  obtain ⟨c', hc'⟩ := hcY
  have hadd : ∀ a u v : Site, dotS a (u + v) = dotS a u + dotS a v := fun a u v => by
    simp only [dotS, Prod.fst_add, Prod.snd_add]; ring
  have hzl : ∀ u : Site, dotS 0 u = 0 := fun u => by simp [dotS]
  have hzr : ∀ a : Site, dotS a 0 = 0 := fun a => by simp [dotS]
  refine ⟨α, β, hN, fun x hx hxv => ?_, fun x hx hxv => ?_⟩
  · have e1 := hc x hx hxv
    have e0 := hc 0 h0m (by simpa using hXm)
    rw [zero_add] at e0
    unfold normed at h0v hXv ⊢
    rw [hzl] at e1 e0
    rw [hzr] at h0v
    rw [hadd α x X]
    linarith
  · have e1 := hc' x hx hxv
    have e0 := hc' (1, 0) h1m (by rw [add_comm]; exact hYm)
    rw [add_comm (1, 0) Y] at e0
    unfold normed at h1v hYv ⊢
    rw [hadd α Y (1, 0)] at hYv
    rw [hadd α x Y]
    have he : dotS e ((1 : ℤ), (0 : ℤ)) = e.1 := by simp [dotS]
    rw [he] at e0
    linarith

end FLatticePaper.Tiles.TileTranslation
