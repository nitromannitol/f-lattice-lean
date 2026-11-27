import FLatticePaper.Tiles.SurgicalDict

/-! # The shifted doubling of an alternate tile (`def:alternate_doubled_tile`, surgical text at 274ad18, lines 3800-3815)

For `n/d`, the shifted doubling `T^{ds,h/v,±}(n/d)` is `T^b(n/d) ∪ (T^{h/v,±}(n/d) + S_{n/d})`, where `T^b` is the boundary
tile, `T^{h/v,±}` the partial tile (`def:partial_tile`) and `S_{n/d}` the doubling shift of `eq:alt_doubled`, which is
`altShifts` (`S_p`, `S_q` by the parity of `W_1`). Two rules of the text are encoded:

* the sign of the partial tile's vertical side is flipped when `n/d = p` and `W_1` is odd, or `n/d = q` and `W_1` is even
  (`partialSideSign`);
* for `T^{ds}(p)^-` and `T^{ds}(q)^+` the partial tile is the standard copy `T(n/d)^{±,1}` instead, and the doubling is
  `T^{h/v,±}(n/d) ∪ (T^b(n/d) + S_{n/d})` (`altDoubledTile`, the `special` branch).

The alternate boundary condition (`T̂^b ∩ T̂ = ⋃ T^b(n'/d')`) is a property of the alternate tile, not a definition, and is not
stated here. The partial tile and the boundary tile are arguments (their definitions are `WeakData.partialT` and `WeakData.bdry`
in `SurgicalWeakOdometers`). -/

namespace FLatticePaper.Tiles.AltDoubled

open FLatticePaper.Tiles.SurgicalDict

/-- The special case of the doubling: `T^{ds}(p)^-` (`isP`, sign `-`) and `T^{ds}(q)^+` (`¬isP`, sign `+`). `sign = true` is `+`. -/
def isSpecial (isP sign : Bool) : Bool := (isP && !sign) || (!isP && sign)

/-- The sign of the partial tile's side: `+` and `-` are flipped in the vertical side `v^±` when `n/d = p` and `W_1` is odd,
or `n/d = q` and `W_1` is even. The horizontal side keeps its sign. -/
def partialSideSign (isP w1Odd vert sign : Bool) : Bool :=
  if vert && ((isP && w1Odd) || (!isP && !w1Odd)) then !sign else sign

/-- The doubling shift `S_{n/d}` of `eq:alt_doubled`: `S_p` (`isP`) or `S_q`, from `altShifts`. -/
def doubleShift (isP w1Odd : Bool) (vp2 vq1 : Site) : Site :=
  if isP then (altShifts w1Odd vp2 vq1).1 else (altShifts w1Odd vp2 vq1).2

/-- The shifted doubling `T^{ds,h/v,±}(n/d)` of `def:alternate_doubled_tile`: `T^b ∪ (T^{h/v,±} + S)`, or in the special case
`T^{h/v,±} ∪ (T^b + S)`. `Tb` is the boundary tile, `Tpart` the partial tile on the side selected by `partialSideSign`. -/
def altDoubledTile (isP w1Odd sign : Bool) (Tb Tpart : Finset Site) (vp2 vq1 : Site) : Finset Site :=
  let S := doubleShift isP w1Odd vp2 vq1
  if isSpecial isP sign then Tpart ∪ Tb.image (· + S) else Tb ∪ Tpart.image (· + S)

theorem isSpecial_p_minus : isSpecial true false = true := rfl

theorem isSpecial_q_plus : isSpecial false true = true := rfl

theorem isSpecial_p_plus : isSpecial true true = false := rfl

theorem isSpecial_q_minus : isSpecial false false = false := rfl

theorem partialSideSign_p_odd_vert (sign : Bool) : partialSideSign true true true sign = !sign := rfl

theorem partialSideSign_q_even_vert (sign : Bool) : partialSideSign false false true sign = !sign := rfl

theorem partialSideSign_horizontal (isP w1Odd sign : Bool) : partialSideSign isP w1Odd false sign = sign := rfl

theorem doubleShift_p_even (vp2 vq1 : Site) : doubleShift true false vp2 vq1 = vq1 + vp2 := rfl

theorem doubleShift_q_even (vp2 vq1 : Site) : doubleShift false false vp2 vq1 = -vq1 + vp2 := rfl

theorem doubleShift_p_odd (vp2 vq1 : Site) : doubleShift true true vp2 vq1 = -vq1 + vp2 := rfl

theorem doubleShift_q_odd (vp2 vq1 : Site) : doubleShift false true vp2 vq1 = vq1 + vp2 := rfl

theorem altDoubledTile_generic (isP w1Odd sign : Bool) (Tb Tpart : Finset Site) (vp2 vq1 : Site)
    (h : isSpecial isP sign = false) :
    altDoubledTile isP w1Odd sign Tb Tpart vp2 vq1 = Tb ∪ Tpart.image (· + doubleShift isP w1Odd vp2 vq1) := by
  unfold altDoubledTile
  rw [h]
  rfl

theorem altDoubledTile_special (isP w1Odd sign : Bool) (Tb Tpart : Finset Site) (vp2 vq1 : Site)
    (h : isSpecial isP sign = true) :
    altDoubledTile isP w1Odd sign Tb Tpart vp2 vq1 = Tpart ∪ Tb.image (· + doubleShift isP w1Odd vp2 vq1) := by
  unfold altDoubledTile
  rw [h]
  rfl

end FLatticePaper.Tiles.AltDoubled
