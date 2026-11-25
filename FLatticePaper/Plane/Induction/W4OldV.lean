import FLatticePaper.Plane.Induction.W4OldH
import FLatticePaper.Plane.Induction.PriceAtI
import FLatticePaper.Plane.Induction.StrongPriceInputs
import FLatticePaper.Plane.Induction.W1Lower
import FLatticePaper.Plane.Induction.MatchedPolicy

/-! # W4 (Q35): the old V star, the bottom case `j = 0`, in the conjugate frame

Q35 classifies the 18 turned-H roots: `ζx = H'_{r−1−j} + c₁U' + c₂V'` in the conjugate frame. The index `j` is the old V label
(`Y V^p_j = H'_j`), and `j = 0` is the bottom case `ζx = hLast + c₁U' + c₂V'` with `hLast = H'_{r−1} = (d', n' − 1)`.
Here `(d', n') = (D+N, D−N)` is the conjugate child, `U' = (D+N, D−N)`, `V' = (−2N, 2D)`.

Facts used:
* `price_hFirst_of_packet`: the conjugate price at `H'_0 = (1,0)` is `c₀'` (the proof of `W1BottomValue.price_hFirst` uses only the
  packet of the field; here the packet is `hSE.packet` of the conjugate).
* `PriceAtI.price_reflectI_origin`: `P'(I) = c₀'`.
* The drifts of the conjugate price along its kernel `U'` (`−1`) and transverse `V'` (`0`) (`priceDrift`).

The jump is `a(x) = c₀' − P'(I − ζx)` (`jumpA_eq_cutPrice`, `zTurn_reflect`). For `j = 0` the root has `I − hLast = H'_0 − U'`, so
`I − ζx = H'_0 − (c₁+1)U' − c₂V'` and `a(x) = −c₁ − 1`. The target `x' = x + (1,0)` (the east prescription at the bottom free
point, `zTurn` shifts by `(0,1)`) has `I − ζx' = I − (c₁+1)U' − c₂V'`, with the same price. So `a(x') = a(x)`.

The cases `j > 0` (the floating geometry of Q35) are not here. -/

namespace FLatticePaper.W4OldV

open Farey FLatticePaper FLatticePaper.Induction

section OldV

variable {word : Word}

/-- The `s`-grade is linear along differences (a copy of the W1Bottom helper). -/
theorem sGrade_sub_lin (frame : ChildFrame) (a b : Site) :
    frame.sGrade (a - b) = frame.sGrade a - frame.sGrade b := by
  unfold ChildFrame.sGrade
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- **The bottom H value (packet form).** `P(1,0) = c₀` for any frame with a packet, as in `W1BottomValue.price_hFirst`. -/
theorem price_hFirst_of_packet (frame : ChildFrame) (F : Field) (hpk : frame.Packet F) :
    frame.price F (1, 0) = frame.cutPrice := by
  have hstr := hpk.strips
  obtain ⟨hn0, hnd, -, hd3, -⟩ := frame.child_facts
  have hF0 : F (1, 0) = 0 :=
    hstr.1 (1, 0) (by simp only [ChildFrame.tGrade]; omega) (by simp only [ChildFrame.tGrade]; omega)
  have hs : frame.sGrade ((1, 0) - frame.parentShift) = frame.child.den + frame.child.num - 2 := by
    rw [sGrade_sub_lin, FLatticePaper.W1Lower.sGrade_parentShift]
    unfold ChildFrame.sGrade
    simp only
    ring
  have h1 : F ((1, 0) - frame.parentShift) = harmonicGrid ((1, 0) - frame.parentShift) :=
    hstr.2 _ (by rw [hs]; omega) (by rw [hs]; omega)
  have hv := FLatticePaper.StrongPriceInputs.price_eq_cutPrice_sub_harmonic_of_zero frame F (1, 0) hF0 h1
  have hh : harmonicGrid (1, 0) = 0 := by
    unfold harmonicGrid
    norm_num
  rw [hv, hh, sub_zero]

/-- The conjugate price along the span of its kernel `U' = (D+N, D−N)`: `P'(z + kU') = P'(z) − k`. -/
theorem priceU_add_smul (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (z : Site) (k : ℤ) :
    (frameAt (conjWord word)).price (standardField (conjWord word))
        (z + (k * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num),
          k * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num))) =
      (frameAt (conjWord word)).price (standardField (conjWord word)) z - k := by
  induction k using Int.induction_on with
  | zero =>
    have e0 : z + ((0 : ℤ) * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num),
        (0 : ℤ) * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num)) = z := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [e0]
    simp
  | succ i ih =>
    have e : z + (((i : ℤ) + 1) * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num),
        ((i : ℤ) + 1) * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num)) =
        (z + ((i : ℤ) * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num),
          (i : ℤ) * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num)))
          + ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num,
            (frameAt word).parents.odd.den - (frameAt word).parents.odd.num) := by
      refine Prod.ext ?_ ?_ <;> simp <;> ring
    rw [e]
    have hd := (hSE.priceDrift (z + ((i : ℤ) * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num),
        (i : ℤ) * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num)))).1
    rw [W4OldH.conj_kernel_eq h] at hd
    linarith [ih]
  | pred i ih =>
    have e : z + ((-(i : ℤ) - 1) * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num),
        (-(i : ℤ) - 1) * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num)) +
        ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num,
          (frameAt word).parents.odd.den - (frameAt word).parents.odd.num) =
        z + (-(i : ℤ) * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num),
          -(i : ℤ) * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num)) := by
      refine Prod.ext ?_ ?_ <;> simp <;> ring
    have hd := (hSE.priceDrift (z + ((-(i : ℤ) - 1) * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num),
        (-(i : ℤ) - 1) * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num)))).1
    rw [W4OldH.conj_kernel_eq h] at hd
    rw [e] at hd
    linarith [ih]

/-- The conjugate price is invariant along its transverse `V' = (−2N, 2D)`. -/
theorem priceV_add_smul (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (z : Site) (k : ℤ) :
    (frameAt (conjWord word)).price (standardField (conjWord word))
        (z + (k * (-2 * (frameAt word).parents.odd.num), k * (2 * (frameAt word).parents.odd.den))) =
      (frameAt (conjWord word)).price (standardField (conjWord word)) z := by
  induction k using Int.induction_on with
  | zero =>
    have e0 : z + ((0 : ℤ) * (-2 * (frameAt word).parents.odd.num), (0 : ℤ) * (2 * (frameAt word).parents.odd.den)) = z := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [e0]
  | succ i ih =>
    have e : z + (((i : ℤ) + 1) * (-2 * (frameAt word).parents.odd.num),
        ((i : ℤ) + 1) * (2 * (frameAt word).parents.odd.den)) =
        (z + ((i : ℤ) * (-2 * (frameAt word).parents.odd.num), (i : ℤ) * (2 * (frameAt word).parents.odd.den)))
          + (-2 * (frameAt word).parents.odd.num, 2 * (frameAt word).parents.odd.den) := by
      refine Prod.ext ?_ ?_ <;> simp <;> ring
    rw [e]
    have hd := (hSE.priceDrift (z + ((i : ℤ) * (-2 * (frameAt word).parents.odd.num),
        (i : ℤ) * (2 * (frameAt word).parents.odd.den)))).2
    rw [W4OldH.conj_transverse_eq h] at hd
    linarith [ih]
  | pred i ih =>
    have e : z + ((-(i : ℤ) - 1) * (-2 * (frameAt word).parents.odd.num),
        (-(i : ℤ) - 1) * (2 * (frameAt word).parents.odd.den)) +
        (-2 * (frameAt word).parents.odd.num, 2 * (frameAt word).parents.odd.den) =
        z + (-(i : ℤ) * (-2 * (frameAt word).parents.odd.num), -(i : ℤ) * (2 * (frameAt word).parents.odd.den)) := by
      refine Prod.ext ?_ ?_ <;> simp <;> ring
    have hd := (hSE.priceDrift (z + ((-(i : ℤ) - 1) * (-2 * (frameAt word).parents.odd.num),
        (-(i : ℤ) - 1) * (2 * (frameAt word).parents.odd.den)))).2
    rw [W4OldH.conj_transverse_eq h] at hd
    rw [e] at hd
    linarith [ih]

/-- **The bottom case `j = 0` of the old V star (Q35).** If `ζx = hLast + c₁U' + c₂V'` (`hLast = (D+N, D−N−1)`) and the target is the
east input `x' = x + (1, 0)`, then `a(x) = a(x') = −c₁ − 1`. -/
theorem oldV_bottom_jumpA (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (c1 c2 : ℤ) (x : Site)
    (hx : zTurn x = ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num,
        (frameAt word).parents.odd.den - (frameAt word).parents.odd.num - 1) +
      (c1 * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) +
          c2 * (-2 * (frameAt word).parents.odd.num),
        c1 * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) +
          c2 * (2 * (frameAt word).parents.odd.den))) :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = -c1 - 1 ∧
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word)))
        (x + (1, 0)) = -c1 - 1 := by
  have hc0 : (frameAt (conjWord word)).price (standardField (conjWord word)) (1, 0) =
      (frameAt (conjWord word)).cutPrice :=
    price_hFirst_of_packet (frameAt (conjWord word)) (standardField (conjWord word)) hSE.packet
  have hI : (frameAt (conjWord word)).price (standardField (conjWord word)) reflectionI =
      (frameAt (conjWord word)).cutPrice :=
    PriceAtI.price_reflectI_origin hSE
  have hj : ∀ y : Site, jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) y =
      (frameAt (conjWord word)).cutPrice -
        (frameAt (conjWord word)).price (standardField (conjWord word)) (reflectionI - zTurn y) := by
    intro y
    rw [jumpA_eq_cutPrice h hSE, zTurn_reflect]
  -- the Y-image of the root: `I − ζx = (1,0) + (−(c₁+1))U' + (−c₂)V'`
  have hW : reflectionI - zTurn x =
      (((1 : ℤ), (0 : ℤ)) + ((-(c1 + 1)) * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num),
          (-(c1 + 1)) * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num))) +
        ((-c2) * (-2 * (frameAt word).parents.odd.num), (-c2) * (2 * (frameAt word).parents.odd.den)) := by
    rw [hx]
    unfold reflectionI
    refine Prod.ext ?_ ?_ <;> simp <;> ring
  have hP1 : (frameAt (conjWord word)).price (standardField (conjWord word)) (reflectionI - zTurn x) =
      (frameAt (conjWord word)).cutPrice + (c1 + 1) := by
    rw [hW, priceV_add_smul h hSE _ (-c2), priceU_add_smul h hSE (1, 0) (-(c1 + 1)), hc0]
    ring
  have hz1 : zTurn (x + (1, 0)) = zTurn x + (0, 1) := by
    unfold zTurn
    refine Prod.ext ?_ ?_ <;> simp
  have hW' : reflectionI - zTurn (x + (1, 0)) =
      (reflectionI + ((-(c1 + 1)) * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num),
          (-(c1 + 1)) * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num))) +
        ((-c2) * (-2 * (frameAt word).parents.odd.num), (-c2) * (2 * (frameAt word).parents.odd.den)) := by
    rw [hz1, hx]
    unfold reflectionI
    refine Prod.ext ?_ ?_ <;> simp <;> ring
  have hP2 : (frameAt (conjWord word)).price (standardField (conjWord word)) (reflectionI - zTurn (x + (1, 0))) =
      (frameAt (conjWord word)).cutPrice + (c1 + 1) := by
    rw [hW', priceV_add_smul h hSE _ (-c2), priceU_add_smul h hSE reflectionI (-(c1 + 1)), hI]
    ring
  constructor
  · rw [hj x, hP1]
    ring
  · rw [hj (x + (1, 0)), hP2]
    ring

end OldV

end FLatticePaper.W4OldV
