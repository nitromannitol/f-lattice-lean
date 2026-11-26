import FLatticePaper.Plane.Induction.HPaidInputs
import FLatticePaper.Plane.Induction.PairTranslate

/-! # Pair forcing of the deck multiplicity

At the fixed pair `(P, J) = (c₀, 0)`, a site that is a deck translate `h + m V` of a free H site (where `J = 0`), or `v + m U` of a
free V site (where `P = c₀`), has multiplicity `m = 0`: `J (h + m V) = m η` and `P (v + m U) = P v − m`. -/

namespace FLatticePaper.PairForcing

open FLatticePaper FLatticePaper.Induction

/-- The rounded slip along `m V`: `J (z + m V) = J z + m η`. -/
theorem roundedSlip_zsmul_V (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (η : ℤ) (m : ℤ) (z : Site) :
    frame.roundedSlip F η (z + m • ((frame.child.num - frame.child.den, frame.child.num + frame.child.den) : Site)) =
      frame.roundedSlip F η z + m * η :=
  PairTranslate.drift_zsmul (frame.roundedSlip F η) _ η
    (fun w => HPaidInputs.roundedSlip_V frame F hP η w) m z

/-- The price along `m U`: `P (z + m U) = P z − m`. -/
theorem price_zsmul_U (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (m : ℤ) (z : Site) :
    frame.price F (z + m • ((frame.child.den, frame.child.num) : Site)) = frame.price F z - m := by
  have h := PairTranslate.drift_zsmul (frame.price F) _ (-1)
    (fun w => HPaidInputs.price_U frame F hP w) m z
  rw [h]
  ring

/-- **Multiplicity of a V translate at the pair.** If `h` and `h + m V` both have rounded slip `0`, then `m = 0` (since `η = ±1`). -/
theorem zero_of_pair_V (frame : ChildFrame) (F : Field) (hP : frame.Packet F) {η : ℤ} (hη : η = 1 ∨ η = -1)
    (h : Site) (m : ℤ) (hJh : frame.roundedSlip F η h = 0)
    (hJz : frame.roundedSlip F η (h + m • ((frame.child.num - frame.child.den, frame.child.num + frame.child.den) : Site)) = 0) :
    m = 0 := by
  have e := roundedSlip_zsmul_V frame F hP η m h
  rw [hJz, hJh] at e
  rcases hη with rfl | rfl <;> omega

/-- **Multiplicity of a U translate at the pair.** If `v` and `v + m U` both have price `c₀`, then `m = 0`. -/
theorem zero_of_pair_U (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (c0 : ℤ) (v : Site) (m : ℤ)
    (hPv : frame.price F v = c0)
    (hPz : frame.price F (v + m • ((frame.child.den, frame.child.num) : Site)) = c0) :
    m = 0 := by
  have e := price_zsmul_U frame F hP m v
  rw [hPz, hPv] at e
  omega

end FLatticePaper.PairForcing
