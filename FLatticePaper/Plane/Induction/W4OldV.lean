import FLatticePaper.Plane.Induction.W4OldH
import FLatticePaper.Plane.Induction.PriceAtI
import FLatticePaper.Plane.Induction.StrongPriceInputs
import FLatticePaper.Plane.Induction.W1Lower
import FLatticePaper.Plane.Induction.MatchedPolicy
import FLatticePaper.Plane.Induction.TraceFromPsi
import FLatticePaper.Plane.Induction.ReflectedFan

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

/-- The last H label `hLast = (d, n − 1)` is a free H point of any child frame (`child_odd`, `child_even`). -/
theorem hLast_mem_freeH (frame : ChildFrame) : frame.hLast ∈ frame.freeH := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hcodd := frame.child_odd
  have hev := frame.child_even
  have hTpos : 2 ≤ frame.child.periodDenominator := by rw [hT]; nlinarith
  have hodd : ¬ EvenSite frame.hLast := by
    unfold EvenSite ChildFrame.hLast
    simp only
    omega
  have heven2 : EvenSite (frame.hLast.1, frame.hLast.2 - 1) := by
    unfold EvenSite ChildFrame.hLast
    simp only
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [FreeVWindow.mem_closedPolygon_odd frame hodd]
    have ht : frame.tGrade frame.hLast = frame.child.den := by
      unfold ChildFrame.tGrade ChildFrame.hLast; ring
    have hs : frame.sGrade frame.hLast = frame.child.periodDenominator - (frame.child.den - frame.child.num) := by
      unfold ChildFrame.sGrade ChildFrame.hLast
      rw [hT]
      ring
    rw [ht, hs]
    omega
  · intro hmem
    rw [FreeVWindow.mem_closedPolygon_even frame heven2] at hmem
    have ht : frame.tGrade (frame.hLast.1, frame.hLast.2 - 1) = 2 * frame.child.den := by
      unfold ChildFrame.tGrade ChildFrame.hLast
      ring
    rw [ht] at hmem
    omega
  · unfold ChildFrame.hSpectrum
    have ht : frame.tGrade frame.hLast = frame.child.den := by
      unfold ChildFrame.tGrade ChildFrame.hLast; ring
    rw [ht]
    right
    exact ⟨hcodd.right, by omega, le_refl _⟩

/-- `prescribedH η hLast = (0,1)` (the north direction at the last H label). -/
theorem prescribedH_hLast (frame : ChildFrame) (η : ℤ) : frame.prescribedH η frame.hLast = (0, 1) := by
  have hne : frame.hLast ≠ hFirst := by
    obtain ⟨-, -, -, hd3, -⟩ := frame.child_facts
    intro h
    unfold ChildFrame.hLast FLatticePaper.Induction.hFirst at h
    have := congrArg Prod.fst h
    simp only at this
    omega
  unfold ChildFrame.prescribedH
  rw [if_neg hne, if_pos rfl]

/-- **The east target from the free policy's prescription (Q35 bottom case).** If the retained inputs at free-closure whites are the
prescribed ones (`FreePresc`, the canonical policy), and `ζx` is a conjugate free-closure white with `ζx = hLast + c₁U' + c₂V'`, then
the retained target `x'` is the east input `x + (1,0)`: `ζx' = ζx + (0,1)`, the prescription at `hLast`. The uniqueness of the
prescribed input is `FreePolicy.freePresc_single`. -/
theorem east_of_prescription (word : Word) (_h : ∃ x ∈ word, x ≠ Digit.three)
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hPres : ∀ c : Site, FreeClosure.freeClosure (frameAt (conjWord word)) c →
      laplacian (standardField (conjWord word)) c = 0 →
      ∀ j : Site, P.retained c j ↔ FreePolicy.FreePresc (frameAt (conjWord word)) (frameAt word).eps c j)
    (c1 c2 : ℤ) (x x' : Site)
    (hx : zTurn x = (frameAt (conjWord word)).hLast +
      (c1 * (frameAt (conjWord word)).child.modifiedDeck.kernel.1 + c2 * (frameAt (conjWord word)).child.modifiedDeck.transverse.1,
        c1 * (frameAt (conjWord word)).child.modifiedDeck.kernel.2 + c2 * (frameAt (conjWord word)).child.modifiedDeck.transverse.2))
    (hwhite : laplacian (standardField (conjWord word)) (zTurn x) = 0)
    (hpol : parentPolicy P x x') :
    x' = x + (1, 0) := by
  set C := frameAt (conjWord word) with hC
  set η := (frameAt word).eps with hη
  have hlast : zTurn x + C.child.modifiedDeck.combine (-c1) (-c2) = C.hLast := by
    rw [hx]
    unfold PeriodDeck.combine
    refine Prod.ext ?_ ?_ <;> simp <;> ring
  have hfree : C.hLast ∈ C.freeH := hLast_mem_freeH C
  have hfc : FreeClosure.freeClosure C (zTurn x) :=
    ⟨C.child.modifiedDeck.combine (-c1) (-c2), ⟨-c1, -c2, rfl⟩, Or.inl (by rw [hlast]; exact hfree)⟩
  have hpres1 : FreePolicy.FreePresc C η (zTurn x) (zTurn x + (0, 1)) :=
    ⟨C.child.modifiedDeck.combine (-c1) (-c2), ⟨-c1, -c2, rfl⟩,
      Or.inl ⟨by rw [hlast]; exact hfree, by rw [hlast, prescribedH_hLast]⟩⟩
  have hPf := (hPres (zTurn x) hfc hwhite (zTurn x')).mp hpol
  have heq : zTurn x' = zTurn x + (0, 1) := FreePolicy.freePresc_single C η hPf hpres1
  have hz1 : zTurn (x + (1, 0)) = zTurn x + (0, 1) := by
    unfold zTurn
    refine Prod.ext ?_ ?_ <;> simp
  apply W4OldH.zTurn_injective
  rw [heq, hz1]

/-- The conjugate `hLast` and the kernel/transverse in explicit coordinates. -/
theorem conj_hLast_eq (h : ∃ x ∈ word, x ≠ Digit.three) :
    (frameAt (conjWord word)).hLast =
      ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num,
        (frameAt word).parents.odd.den - (frameAt word).parents.odd.num - 1) := by
  obtain ⟨h1, h2⟩ := UnitBound.conj_child_sums h
  unfold ChildFrame.hLast
  rw [h1, h2]

/-- **The bottom case `j = 0` of the old V star, with the east target from the free policy.** The retained target is the east input
`x + (1, 0)` by `east_of_prescription` (the canonical policy takes the prescription at free-closure whites, `hPres`), and then
`oldV_bottom_jumpA` gives `a(x) = a(x') = −c₁ − 1`. The hypothesis `hwhite` (the conjugate laplacian at `ζx` is zero) is the
white condition of the retained edge. -/
theorem oldV_bottom_jumpA_policy (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hPres : ∀ c : Site, FreeClosure.freeClosure (frameAt (conjWord word)) c →
      laplacian (standardField (conjWord word)) c = 0 →
      ∀ j : Site, P.retained c j ↔ FreePolicy.FreePresc (frameAt (conjWord word)) (frameAt word).eps c j)
    (c1 c2 : ℤ) (x x' : Site)
    (hx : zTurn x = ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num,
        (frameAt word).parents.odd.den - (frameAt word).parents.odd.num - 1) +
      (c1 * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) +
          c2 * (-2 * (frameAt word).parents.odd.num),
        c1 * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) +
          c2 * (2 * (frameAt word).parents.odd.den)))
    (hwhite : laplacian (standardField (conjWord word)) (zTurn x) = 0)
    (hpol : parentPolicy P x x') :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = -c1 - 1 ∧
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x' = -c1 - 1 := by
  have hx' : zTurn x = (frameAt (conjWord word)).hLast +
      (c1 * (frameAt (conjWord word)).child.modifiedDeck.kernel.1 +
          c2 * (frameAt (conjWord word)).child.modifiedDeck.transverse.1,
        c1 * (frameAt (conjWord word)).child.modifiedDeck.kernel.2 +
          c2 * (frameAt (conjWord word)).child.modifiedDeck.transverse.2) := by
    rw [hx, conj_hLast_eq h, W4OldH.conj_kernel_eq h, W4OldH.conj_transverse_eq h]
  have hE := east_of_prescription word h P hPres c1 c2 x x' hx' hwhite hpol
  rw [hE]
  exact oldV_bottom_jumpA h hSE c1 c2 x hx

/-! ### Q35, every H label: the trace price, the reflection identity, and the shift bounds -/

/-- **The H-trace price on the conjugate (the trace input, `TraceAt (conjWord word)`).** `P'(z) = c'₀` at `z = (1,0) = H'_0` and
`P'(z) = c'₀ − 1` at every other conjugate free H point. For `j > 0` the label `H'_j` has first coordinate `j + 1 ≠ 1`. -/
theorem conj_price_freeH (hTr : TraceFromPsi.TraceAt (conjWord word)) {z : Site}
    (hz : z ∈ (frameAt (conjWord word)).freeH) :
    (frameAt (conjWord word)).price (standardField (conjWord word)) z =
      (frameAt (conjWord word)).cutPrice - (if z = ((1 : ℤ), (0 : ℤ)) then 0 else 1) :=
  hTr z hz

/-- The reflection of a conjugate free H label: `I − reflH g = g − U'` with `U' = (D+N, D−N)` (`reflH g = U' + I − g`). -/
theorem reflectionI_sub_reflH (h : ∃ x ∈ word, x ≠ Digit.three) (g : Site) :
    reflectionI - FLatticePaper.ReflectedFan.reflH (frameAt (conjWord word)) g =
      g - ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num,
        (frameAt word).parents.odd.den - (frameAt word).parents.odd.num) := by
  obtain ⟨h1, h2⟩ := UnitBound.conj_child_sums h
  unfold FLatticePaper.ReflectedFan.reflH reflectionI
  rw [h1, h2]
  refine Prod.ext ?_ ?_ <;> simp <;> ring

/-- **The old V star at every H label (Q35, `a = [g ≠ H'_0] − c₁ − 1`).** Let `g` be a conjugate free H point and let the root be
`ζx = reflH g + c₁U' + c₂V'`; the reflection `reflH g = U' + I − g` is the label `H'_{r−1−j}` of the old V root. Then
`a(x) = [g ≠ (1,0)] − c₁ − 1`, which is Q35's `a = m + [j > 0]` with `m = −c₁ − 1`. The trace `TraceAt (conjWord word)` supplies
`P'(g)`. -/
theorem oldV_jumpA_of_trace (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hTr : TraceFromPsi.TraceAt (conjWord word)) (c1 c2 : ℤ) (x : Site) {g : Site}
    (hg : g ∈ (frameAt (conjWord word)).freeH)
    (hx : zTurn x = FLatticePaper.ReflectedFan.reflH (frameAt (conjWord word)) g +
      (c1 * (frameAt (conjWord word)).child.modifiedDeck.kernel.1 +
          c2 * (frameAt (conjWord word)).child.modifiedDeck.transverse.1,
        c1 * (frameAt (conjWord word)).child.modifiedDeck.kernel.2 +
          c2 * (frameAt (conjWord word)).child.modifiedDeck.transverse.2)) :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x =
      (if g = ((1 : ℤ), (0 : ℤ)) then 0 else 1) - c1 - 1 := by
  rw [W4OldH.conj_kernel_eq h, W4OldH.conj_transverse_eq h] at hx
  have hj : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x =
      (frameAt (conjWord word)).cutPrice -
        (frameAt (conjWord word)).price (standardField (conjWord word)) (reflectionI - zTurn x) := by
    rw [jumpA_eq_cutPrice h hSE, zTurn_reflect]
  have hW : reflectionI - zTurn x =
      (g + ((-c1 - 1) * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num),
          (-c1 - 1) * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num))) +
        ((-c2) * (-2 * (frameAt word).parents.odd.num), (-c2) * (2 * (frameAt word).parents.odd.den)) := by
    rw [hx]
    have h1 := (UnitBound.conj_child_sums h).1
    have h2 := (UnitBound.conj_child_sums h).2
    unfold FLatticePaper.ReflectedFan.reflH reflectionI
    rw [h1, h2]
    refine Prod.ext ?_ ?_ <;> simp <;> ring
  have hP : (frameAt (conjWord word)).price (standardField (conjWord word)) (reflectionI - zTurn x) =
      (frameAt (conjWord word)).price (standardField (conjWord word)) g + c1 + 1 := by
    rw [hW, priceV_add_smul h hSE _ (-c2), priceU_add_smul h hSE g (-c1 - 1)]
    ring
  rw [hj, hP, conj_price_freeH hTr hg]
  ring

/-- The `j = 0` case (`g = H'_0 = (1,0)`): `a = −c₁ − 1`, as in `oldV_bottom_jumpA`. -/
theorem oldV_jumpA_zero (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hTr : TraceFromPsi.TraceAt (conjWord word)) (c1 c2 : ℤ) (x : Site) {g : Site}
    (hg : g ∈ (frameAt (conjWord word)).freeH) (hg0 : g = ((1 : ℤ), (0 : ℤ)))
    (hx : zTurn x = FLatticePaper.ReflectedFan.reflH (frameAt (conjWord word)) g +
      (c1 * (frameAt (conjWord word)).child.modifiedDeck.kernel.1 +
          c2 * (frameAt (conjWord word)).child.modifiedDeck.transverse.1,
        c1 * (frameAt (conjWord word)).child.modifiedDeck.kernel.2 +
          c2 * (frameAt (conjWord word)).child.modifiedDeck.transverse.2)) :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = -c1 - 1 := by
  rw [oldV_jumpA_of_trace h hSE hTr c1 c2 x hg hx, if_pos hg0]
  ring

/-- The `j > 0` case (`g.1 ≠ 1`, so `g = H'_j ≠ H'_0`): `a = −c₁`, which is `m + 1` with `m = −c₁ − 1` (Q35). -/
theorem oldV_jumpA_pos (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hTr : TraceFromPsi.TraceAt (conjWord word)) (c1 c2 : ℤ) (x : Site) {g : Site}
    (hg : g ∈ (frameAt (conjWord word)).freeH) (hg1 : g.1 ≠ 1)
    (hx : zTurn x = FLatticePaper.ReflectedFan.reflH (frameAt (conjWord word)) g +
      (c1 * (frameAt (conjWord word)).child.modifiedDeck.kernel.1 +
          c2 * (frameAt (conjWord word)).child.modifiedDeck.transverse.1,
        c1 * (frameAt (conjWord word)).child.modifiedDeck.kernel.2 +
          c2 * (frameAt (conjWord word)).child.modifiedDeck.transverse.2)) :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = -c1 := by
  have hne : ¬ g = ((1 : ℤ), (0 : ℤ)) := by
    intro e
    apply hg1
    simp [e]
  rw [oldV_jumpA_of_trace h hSE hTr c1 c2 x hg hx, if_neg hne]
  ring

/-- **The old V shift bounds (Q35: `k ∈ {0, 1}`).** With `s ∈ [α, β]`, `β − α < K`, and the two polygon inequalities
`α − s ≤ kK ≤ K + β − s` (at `x = v + kU_p` and `x + U_q`), the shift `k` is `0` or `1`. -/
theorem k_mem_zero_one (k K α β s : ℤ) (hK : 0 < K) (hαβ : β - α < K) (hs1 : α ≤ s) (hs2 : s ≤ β)
    (hlo : α - s ≤ k * K) (hhi : k * K ≤ K + β - s) : 0 ≤ k ∧ k ≤ 1 := by
  constructor
  · by_contra hneg
    have hk : k ≤ -1 := by omega
    have : k * K ≤ -K := by nlinarith
    linarith
  · by_contra hbig
    have hk : 2 ≤ k := by omega
    have : 2 * K ≤ k * K := by nlinarith
    linarith

/-- **The offer `B` fixes the shift (Q35, display (1)).** With `ε = 2W − 1` (so `W = 1 ↔ ε = 1`), `k ∈ {0,1}` and `B = 2W − 2εk ≥ 1`:
`W = 1` forces `k = 0` and `W = 0` forces `k = 1`. -/
theorem B_forces_k (W ε k : ℤ) (hW : W = 0 ∨ W = 1) (hε : ε = 2 * W - 1) (hk : 0 ≤ k ∧ k ≤ 1)
    (hB : 1 ≤ 2 * W - 2 * ε * k) : (W = 1 → k = 0) ∧ (W = 0 → k = 1) := by
  rcases hW with rfl | rfl
  · have hε' : ε = -1 := by omega
    subst hε'
    constructor
    · intro h; norm_num at h
    · intro _; nlinarith [hk.1, hk.2]
  · have hε' : ε = 1 := by omega
    subst hε'
    constructor
    · intro _; nlinarith [hk.1, hk.2]
    · intro h; norm_num at h

end OldV


end FLatticePaper.W4OldV
