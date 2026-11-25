import FLatticePaper.Plane.Induction.ConjFreeRoot
import FLatticePaper.Plane.Induction.UnitBound
import FLatticePaper.Plane.Induction.FreeOrbit
import FLatticePaper.Plane.Induction.W1Phase
import FLatticePaper.Plane.Induction.FreePolicy
import FLatticePaper.Plane.Induction.ForcedArrows
import FLatticePaper.Plane.Induction.Q3Paragraph8

/-! # W4 (Q35): the old H star of the odd parent, in the conjugate frame

Q35 classifies the 50 turned-V roots: `ζx = V'_j + c₁U' + c₂V'` in the conjugate frame, where `ζ = zTurn`, `U' = (D+N, D−N)`,
`V' = (−2N, 2D)`, and `p = N/D` is the odd parent. The native old H point is `H = ζ⁻¹ q` (`zTurnInv q`), with
`t_p(H) = N + s'(q)/2` (the conjugate `s`-grade, `UnitBound.sGrade_conj_zTurn`). The star is `x = H + c₂U_p − c₁V_p`
(`U_p = (2D, 2N)`, `V_p = (N−D, N+D)`), and the drifts of the jump are
`a(x + U_p) = a(x)`, `a(x + V_p) = a(x) + 1` (from `priceDrift` and `jumpA_eq_cutPrice`).

Main results:
* `jumpA_add_span`: `a(z + c U_p + m V_p) = a(z) + m`.
* `tp_bounds_of_freeV`: `1 ≤ t_p(H) ≤ N + D − 1` for a conjugate free V point (`freeV_s_range`, the parity of `s`).
* `zero_at_inputs`: the root and both inputs of `H` have `a = 0`, given the odd-root grade bound `hRef` and the even top line
  `hTop` (used only when `N = 1`).
* `oldH_star_jumpA`: for `x` in the star, `a(x) = −c₁` and the retained target `x' ∈ {incomingNeg x, incomingPos x}` has
  `a(x') = a(x)`.

The two hypotheses are explicit: `hRef` (the odd root grade `t_p(H) ≤ D`, numerically true, symbolic proof pending) and `hTop`
(Q35's even line at `N = 1`, "the strengthened even strip when N = 1"). Neither is used for `N ≥ 2` except `hRef`. -/

namespace FLatticePaper.W4OldH

open Farey FLatticePaper FLatticePaper.Induction

section OldH

variable {word : Word}

theorem conj_kernel_eq (h : ∃ x ∈ word, x ≠ Digit.three) :
    (frameAt (conjWord word)).child.modifiedDeck.kernel =
      ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num,
        (frameAt word).parents.odd.den - (frameAt word).parents.odd.num) := by
  obtain ⟨h1, h2⟩ := UnitBound.conj_child_sums h
  rw [ChildFrame.child_modifiedDeck_kernel, h1, h2]

theorem conj_transverse_eq (h : ∃ x ∈ word, x ≠ Digit.three) :
    (frameAt (conjWord word)).child.modifiedDeck.transverse =
      (-2 * (frameAt word).parents.odd.num, 2 * (frameAt word).parents.odd.den) := by
  obtain ⟨h1, h2⟩ := UnitBound.conj_child_sums h
  rw [ChildFrame.child_modifiedDeck_transverse, h1, h2]
  refine Prod.ext ?_ ?_ <;> simp <;> ring

/-- `ζ(x + (2D, 2N)) = ζ x + (−2N, 2D)` after the reflection `I`: the identity in `Y = I − ζ`. -/
theorem zTurn_add_Up (x : Site) (D N : ℤ) :
    zTurn ((1, -1) - (x + (2 * D, 2 * N))) = zTurn ((1, -1) - x) - (-2 * N, 2 * D) := by
  unfold zTurn
  refine Prod.ext ?_ ?_ <;> simp <;> ring

theorem zTurn_add_Vp (x : Site) (D N : ℤ) :
    zTurn ((1, -1) - (x + (N - D, N + D))) = zTurn ((1, -1) - x) + (D + N, D - N) := by
  unfold zTurn
  refine Prod.ext ?_ ?_ <;> simp <;> ring

/-- The drift of the jump along `U_p = (2D, 2N)`: `a` is invariant. -/
theorem jumpA_add_Up (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) (x : Site) :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word)))
        (x + (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num)) =
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x := by
  rw [jumpA_eq_cutPrice h hSE, jumpA_eq_cutPrice h hSE,
    zTurn_add_Up x (frameAt word).parents.odd.den (frameAt word).parents.odd.num]
  have hd := (hSE.priceDrift (zTurn ((1, -1) - x) -
      (-2 * (frameAt word).parents.odd.num, 2 * (frameAt word).parents.odd.den))).2
  rw [conj_transverse_eq h, sub_add_cancel] at hd
  linarith

/-- The drift of the jump along `V_p = (N−D, N+D)`: `a` increases by one. -/
theorem jumpA_add_Vp (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) (x : Site) :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word)))
        (x + ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den,
          (frameAt word).parents.odd.num + (frameAt word).parents.odd.den)) =
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x + 1 := by
  rw [jumpA_eq_cutPrice h hSE, jumpA_eq_cutPrice h hSE,
    zTurn_add_Vp x (frameAt word).parents.odd.den (frameAt word).parents.odd.num]
  have hd := (hSE.priceDrift (zTurn ((1, -1) - x))).1
  rw [conj_kernel_eq h] at hd
  linarith

/-- The span drift along `U_p`, over the integers. -/
theorem jumpA_add_Up_smul (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (z : Site) (k : ℤ) :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word)))
        (z + (k * (2 * (frameAt word).parents.odd.den), k * (2 * (frameAt word).parents.odd.num))) =
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) z := by
  induction k using Int.induction_on with
  | zero =>
    have e0 : z + ((0 : ℤ) * (2 * (frameAt word).parents.odd.den), (0 : ℤ) * (2 * (frameAt word).parents.odd.num)) = z := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [e0]
  | succ i ih =>
    have e : z + (((i : ℤ) + 1) * (2 * (frameAt word).parents.odd.den),
        ((i : ℤ) + 1) * (2 * (frameAt word).parents.odd.num)) =
        (z + ((i : ℤ) * (2 * (frameAt word).parents.odd.den), (i : ℤ) * (2 * (frameAt word).parents.odd.num)))
          + (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num) := by
      refine Prod.ext ?_ ?_ <;> simp <;> ring
    rw [e, jumpA_add_Up h hSE, ih]
  | pred i ih =>
    have e : z + ((-(i : ℤ) - 1) * (2 * (frameAt word).parents.odd.den),
        (-(i : ℤ) - 1) * (2 * (frameAt word).parents.odd.num)) +
        (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num) =
        z + (-(i : ℤ) * (2 * (frameAt word).parents.odd.den), -(i : ℤ) * (2 * (frameAt word).parents.odd.num)) := by
      refine Prod.ext ?_ ?_ <;> simp <;> ring
    have key := jumpA_add_Up h hSE (z + ((-(i : ℤ) - 1) * (2 * (frameAt word).parents.odd.den),
        (-(i : ℤ) - 1) * (2 * (frameAt word).parents.odd.num)))
    rw [e, ih] at key
    exact key.symm

/-- The span drift along `V_p`, over the integers. -/
theorem jumpA_add_Vp_smul (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (z : Site) (m : ℤ) :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word)))
        (z + (m * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
          m * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den))) =
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) z + m := by
  induction m using Int.induction_on with
  | zero =>
    have e0 : z + ((0 : ℤ) * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
        (0 : ℤ) * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den)) = z := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [e0]; simp
  | succ i ih =>
    have e : z + (((i : ℤ) + 1) * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
        ((i : ℤ) + 1) * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den)) =
        (z + ((i : ℤ) * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
          (i : ℤ) * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den))) +
          ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den,
            (frameAt word).parents.odd.num + (frameAt word).parents.odd.den) := by
      refine Prod.ext ?_ ?_ <;> simp <;> ring
    rw [e, jumpA_add_Vp h hSE]
    linarith [ih]
  | pred i ih =>
    have e : z + ((-(i : ℤ) - 1) * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
        (-(i : ℤ) - 1) * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den)) +
        ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den,
          (frameAt word).parents.odd.num + (frameAt word).parents.odd.den) =
        z + (-(i : ℤ) * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
          -(i : ℤ) * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den)) := by
      refine Prod.ext ?_ ?_ <;> simp <;> ring
    have key := jumpA_add_Vp h hSE (z + ((-(i : ℤ) - 1) * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
        (-(i : ℤ) - 1) * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den)))
    rw [e, ih] at key
    linarith

/-- **The span drift of the jump**: `a(z + (k U_p + m V_p)) = a(z) + m`. -/
theorem jumpA_add_span (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (z : Site) (k m : ℤ) :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word)))
        (z + (k * (2 * (frameAt word).parents.odd.den) + m * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
          k * (2 * (frameAt word).parents.odd.num) + m * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den))) =
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) z + m := by
  have e : z + (k * (2 * (frameAt word).parents.odd.den) + m * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
      k * (2 * (frameAt word).parents.odd.num) + m * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den)) =
      (z + (m * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
        m * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den))) +
        (k * (2 * (frameAt word).parents.odd.den), k * (2 * (frameAt word).parents.odd.num)) := by
    refine Prod.ext ?_ ?_ <;> simp <;> ring
  rw [e, jumpA_add_Up_smul h hSE, jumpA_add_Vp_smul h hSE]

theorem zTurn_zTurnInv (q : Site) : zTurn (W1Phase.zTurnInv q) = q := by
  unfold zTurn W1Phase.zTurnInv
  refine Prod.ext ?_ ?_ <;> simp

theorem zTurn_injective {a b : Site} (hab : zTurn a = zTurn b) : a = b := by
  unfold zTurn at hab
  have h1 := congrArg Prod.fst hab
  have h2 := congrArg Prod.snd hab
  simp only at h1 h2
  exact Prod.ext (by omega) (by omega)

/-- The conjugate `t_p`-range of the native point: `1 ≤ t_p(H) ≤ N + D − 1` for a conjugate free V point `q`, `H = ζ⁻¹ q`. -/
theorem tp_bounds_of_freeV (h : ∃ x ∈ word, x ≠ Digit.three) {q : Site}
    (hq : q ∈ (frameAt (conjWord word)).freeV) :
    1 ≤ (frameAt word).parentTGrade (W1Phase.zTurnInv q) ∧
      (frameAt word).parentTGrade (W1Phase.zTurnInv q) ≤
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1 := by
  obtain ⟨h1, h2⟩ := UnitBound.conj_child_sums h
  have hv : (frameAt (conjWord word)).vSpectrum ((frameAt (conjWord word)).sGrade q) := hq.2.2
  unfold ChildFrame.vSpectrum at hv
  rw [h1, h2] at hv
  have hs := FreeOrbit.freeV_s_range (frameAt (conjWord word)) hq
  rw [h1, h2] at hs
  have e := UnitBound.sGrade_conj_zTurn h (W1Phase.zTurnInv q)
  rw [zTurn_zTurnInv] at e
  have e' : (frameAt (conjWord word)).sGrade q =
      2 * (frameAt word).parentTGrade (W1Phase.zTurnInv q) - 2 * (frameAt word).parents.odd.num := by
    rw [e]; unfold ChildFrame.parentTGrade; ring
  omega

/-- The conjugate `(n,d)` relations give `1 ≤ N < D` (from the conjugate child: `0 < D − N < D + N`). -/
theorem odd_bounds_of_conj (h : ∃ x ∈ word, x ≠ Digit.three) :
    1 ≤ (frameAt word).parents.odd.num ∧ (frameAt word).parents.odd.num < (frameAt word).parents.odd.den := by
  obtain ⟨h1, h2⟩ := UnitBound.conj_child_sums h
  obtain ⟨hpos, hnlt, -, -, -⟩ := (frameAt (conjWord word)).child_facts
  omega

theorem evenSite_add_of {a b : Site} (ha : EvenSite a) (hb : EvenSite b) : EvenSite (a + b) := by
  unfold EvenSite at *
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- The even shift `ε U_q` (`U_q = (d_q, n_q)`) is an even site: the even parent has even `n + d`. -/
theorem evenSite_eps_uq (word : Word) :
    EvenSite ((frameAt word).eps * (frameAt word).parents.even.den,
      (frameAt word).eps * (frameAt word).parents.even.num) := by
  have hev := (frameAt word).valid.even_parity
  unfold Fraction.Even at hev
  unfold EvenSite
  simp only
  rw [← mul_add, Int.mul_emod, show ((frameAt word).parents.even.den + (frameAt word).parents.even.num) % 2 = 0 by
    rw [add_comm]; exact hev]
  simp

/-- The jump is zero when both of its values vanish. -/
theorem jumpA_zero_of_F (word : Word) (y : Site)
    (h1 : quarterTurnField (standardField (conjWord word)) y = 0)
    (h2 : quarterTurnField (standardField (conjWord word))
      (y + ((frameAt word).eps * (frameAt word).parents.even.den,
        (frameAt word).eps * (frameAt word).parents.even.num)) = 0) :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) y = 0 := by
  unfold jumpA
  rw [h1, h2]
  ring

/-- **The inputs of the native old H point have zero jump.** For a site `z` with `1 ≤ t_p(z) ≤ N + D − 1` (and, for the odd
input `incomingNeg z`, the grade bound `t_p(z) ≤ D` of `hodd`), the root and both inputs have `a = 0`. The only case needing the even
top line `hTop` is `N = 1`, the odd root with `t_p(z) = D` and the input `(z₁, z₂ − 1)` (grade `2D`, uq-shift `2D + 1 = N + 2D`). -/
theorem zero_at_inputs (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (z : Site)
    (hN1 : 1 ≤ (frameAt word).parents.odd.num)
    (hND : (frameAt word).parents.odd.num < (frameAt word).parents.odd.den)
    (hb1 : 1 ≤ (frameAt word).parentTGrade z)
    (hb2 : (frameAt word).parentTGrade z ≤ (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1)
    (hodd : ¬ EvenSite z → (frameAt word).parentTGrade z ≤ (frameAt word).parents.odd.den)
    (hTop : (frameAt word).parents.odd.num = 1 → ∀ w : Site, EvenSite w →
      (frameAt word).parentTGrade w = (frameAt word).parents.odd.num + 2 * (frameAt word).parents.odd.den →
      quarterTurnField (standardField (conjWord word)) w = 0) :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) z = 0 ∧
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) (FLatticePaper.incomingNeg z) = 0 ∧
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) (FLatticePaper.incomingPos z) = 0 := by
  by_cases hz : EvenSite z
  · have hn : FLatticePaper.incomingNeg z = (z.1 - 1, z.2) := FreePolicy.inNeg_even hz
    have hp : FLatticePaper.incomingPos z = (z.1 + 1, z.2) := FreePolicy.inPos_even hz
    refine ⟨jumpA_zero_of_strip h hSE z (by omega) (by omega), ?_, ?_⟩
    · have hpn : (frameAt word).parentTGrade (z.1 - 1, z.2) = (frameAt word).parentTGrade z - (frameAt word).parents.odd.num := by
        unfold ChildFrame.parentTGrade; simp only; ring
      rw [hn]
      exact jumpA_zero_of_strip h hSE (z.1 - 1, z.2) (by omega) (by omega)
    · have hpp : (frameAt word).parentTGrade (z.1 + 1, z.2) = (frameAt word).parentTGrade z + (frameAt word).parents.odd.num := by
        unfold ChildFrame.parentTGrade; simp only; ring
      rw [hp]
      exact jumpA_zero_of_strip h hSE (z.1 + 1, z.2) (by omega) (by omega)
  · have hn : FLatticePaper.incomingNeg z = (z.1, z.2 - 1) := FreePolicy.inNeg_odd hz
    have hp : FLatticePaper.incomingPos z = (z.1, z.2 + 1) := FreePolicy.inPos_odd hz
    have hz' := hodd hz
    refine ⟨jumpA_zero_of_strip h hSE z (by omega) (by omega), ?_, ?_⟩
    · rw [hn]
      have hpn : (frameAt word).parentTGrade (z.1, z.2 - 1) = (frameAt word).parentTGrade z + (frameAt word).parents.odd.den := by
        unfold ChildFrame.parentTGrade; simp only; ring
      have hye : EvenSite (z.1, z.2 - 1) := by
        unfold EvenSite at *; simp only; omega
      by_cases hc : (frameAt word).parentTGrade z + (frameAt word).parents.odd.den + 1 ≤
          (frameAt word).parents.odd.num + 2 * (frameAt word).parents.odd.den - 1
      · exact jumpA_zero_of_strip h hSE (z.1, z.2 - 1) (by omega) (by omega)
      · have hnum : (frameAt word).parents.odd.num = 1 := by omega
        have hzD : (frameAt word).parentTGrade z = (frameAt word).parents.odd.den := by omega
        apply jumpA_zero_of_F word (z.1, z.2 - 1)
        · exact zeroStrip_of_strong h hSE (z.1, z.2 - 1) (by omega) (by omega)
        · apply hTop hnum
          · exact evenSite_add_of hye (evenSite_eps_uq word)
          · rw [parentTGrade_add_eps_uq]; omega
    · rw [hp]
      have hpp : (frameAt word).parentTGrade (z.1, z.2 + 1) = (frameAt word).parentTGrade z - (frameAt word).parents.odd.den := by
        unfold ChildFrame.parentTGrade; simp only; ring
      have hye : EvenSite (z.1, z.2 + 1) := by
        unfold EvenSite at *; simp only; omega
      exact jumpA_zero_of_strip h hSE (z.1, z.2 + 1) (by omega) (by omega)

/-- **The old H star (Q35, 50 turned-V roots).** For a conjugate free V point `q`, `ζ x = q + c₁U' + c₂V'`, the jump is `a(x) = −c₁`,
and the retained target `x'` (an input of `x`) has `a(x') = a(x)`. Hypotheses: `hRef` (the odd root grade bound `t_p(H) ≤ D`, numerically
true, symbolic proof pending) and `hTop` (Q35's even line at `N = 1`, "the strengthened even strip when N = 1"). -/
theorem oldH_star_jumpA (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hRef : ∀ q : Site, q ∈ (frameAt (conjWord word)).freeV → ¬ EvenSite (W1Phase.zTurnInv q) →
      (frameAt word).parentTGrade (W1Phase.zTurnInv q) ≤ (frameAt word).parents.odd.den)
    (hTop : (frameAt word).parents.odd.num = 1 → ∀ w : Site, EvenSite w →
      (frameAt word).parentTGrade w = (frameAt word).parents.odd.num + 2 * (frameAt word).parents.odd.den →
      quarterTurnField (standardField (conjWord word)) w = 0)
    {q : Site} (hq : q ∈ (frameAt (conjWord word)).freeV) (c1 c2 : ℤ) (x : Site)
    (hx : zTurn x = q + (c1 * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) +
        c2 * (-2 * (frameAt word).parents.odd.num),
      c1 * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) +
        c2 * (2 * (frameAt word).parents.odd.den)))
    (x' : Site) (hx' : x' = FLatticePaper.incomingNeg x ∨ x' = FLatticePaper.incomingPos x) :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = -c1 ∧
      jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x' = -c1 := by
  obtain ⟨hN1, hND⟩ := odd_bounds_of_conj h
  obtain ⟨hb1, hb2⟩ := tp_bounds_of_freeV h hq
  obtain ⟨hH0, hHN, hHP⟩ := zero_at_inputs h hSE (W1Phase.zTurnInv q) hN1 hND hb1 hb2 (hRef q hq) hTop
  have hxw : x = W1Phase.zTurnInv q + (c2 * (2 * (frameAt word).parents.odd.den) +
      (-c1) * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
      c2 * (2 * (frameAt word).parents.odd.num) + (-c1) * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den)) := by
    apply zTurn_injective
    rw [hx]
    unfold zTurn W1Phase.zTurnInv
    refine Prod.ext ?_ ?_ <;> simp <;> ring
  have hw : EvenSite (c2 * (2 * (frameAt word).parents.odd.den) +
      (-c1) * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
      c2 * (2 * (frameAt word).parents.odd.num) + (-c1) * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den)) := by
    unfold EvenSite
    simp only
    have e : c2 * (2 * (frameAt word).parents.odd.den) + (-c1) * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den) +
        (c2 * (2 * (frameAt word).parents.odd.num) + (-c1) * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den)) =
        2 * (c2 * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) - c1 * (frameAt word).parents.odd.num) := by
      ring
    rw [e]
    simp
  have hxa : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = -c1 := by
    rw [hxw, jumpA_add_span h hSE, hH0]
    ring
  rcases hx' with rfl | rfl
  · refine ⟨hxa, ?_⟩
    rw [hxw, ForcedArrows.incomingNeg_add_even hw, jumpA_add_span h hSE, hHN]
    ring
  · refine ⟨hxa, ?_⟩
    rw [hxw, ForcedArrows.incomingPos_add_even hw, jumpA_add_span h hSE, hHP]
    ring

end OldH

end FLatticePaper.W4OldH
