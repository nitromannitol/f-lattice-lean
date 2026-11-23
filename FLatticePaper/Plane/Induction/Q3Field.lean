import FLatticePaper.Plane.Induction.Q3Strong

/-! Task 59, paragraphs 6 and 7: the field identities of the negative chart and the reflection (PROVISIONAL readings).

Write `f = quarterTurnField G`, `Z x = (−x₂, x₁ − 1)` (`mapSite_quarterTurn_eq`), `I = (1, −1)`, `U_q = (d_q, n_q)`,
`V_q = (n_q − d_q, n_q + d_q)`, `a_q = (n_q, −d_q)`, `c_e = (T_q − d_q − n_q)/2 + 2W`, `W = (1+ε)/2`, and `σ_c` the
shortShift of the conjugate. Facts proved here:
* `harmonicGrid (I − y) = harmonicGrid y`, and `harmonicGrid (x − V_q) = harmonicGrid x + (−n_q x₁ + d_q x₂ + s)` with `2s = n_q+d_q−T_q`;
* `coherentConstantU = 0` (the kernel of the earlier child is an exact period of its field);
* `G(I − z) = G z` from the packet reflection and the generator periods (the constant `K = c_U + c_V + T + κ` vanishes);
* paragraph 7: `f(I − y) = f(y)`, hence `a(x) = p(I − x)`;
* paragraph 6: `f(x − V_q) − f(x) + a_q·x + c_e = (1 + ε) − (G(Zx) − G(Zx + ε σ_c))`, using the lattice relation
  `w − ε σ_c = k (D+N, D−N)` (`w = (n_q+d_q, d_q−n_q)`) and the zero kernel period. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem harmonicGrid_I_sub_pair (a b : ℤ) : harmonicGrid (1 - a, -1 - b) = harmonicGrid (a, b) := by
  unfold harmonicGrid
  dsimp only
  have hP : (1 - a + (-1 - b)) % 2 = (a + b) % 2 := by omega
  rw [hP]
  congr 1
  ring

theorem harmonicGrid_I_sub (y : Site) : harmonicGrid ((1, -1) - y) = harmonicGrid y := by
  obtain ⟨a, b⟩ := y
  exact harmonicGrid_I_sub_pair a b

theorem harmonicGrid_sub_V (p q a b s : ℤ) (hs : 2 * s = p + q - (q ^ 2 + 2 * q * p - p ^ 2)) :
    harmonicGrid (a - (p - q), b - (p + q)) = harmonicGrid (a, b) + (-p * a + q * b + s) := by
  unfold harmonicGrid
  dsimp only
  have hP : (a - (p - q) + (b - (p + q))) % 2 = (a + b) % 2 := by omega
  rw [hP]
  have key : (a - (p - q)) ^ 2 + 2 * (a - (p - q)) * (b - (p + q)) - (b - (p + q)) ^ 2 - 2 * (b - (p + q))
      - (a + b) % 2 =
      (a ^ 2 + 2 * a * b - b ^ 2 - 2 * b - (a + b) % 2) + (-p * a + q * b + s) * 4 := by
    linear_combination (-2 : ℤ) * hs
  rw [key, Int.add_mul_ediv_right _ _ (by norm_num : (4 : ℤ) ≠ 0)]

/-- `2s = n + d − T` solvable for an even child: `coherentConstantU` vanishes (the kernel period is exact). -/
theorem symmetry_half (fr : ChildFrame) : ∃ r : ℤ,
    fr.child.den + fr.child.num - fr.child.periodDenominator = 2 * r := by
  have hL : (fr.child.num + fr.child.den) % 2 = 0 := fr.child_even
  obtain ⟨m, hm⟩ : ∃ m : ℤ, fr.child.num + fr.child.den = 2 * m := ⟨(fr.child.num + fr.child.den) / 2, by omega⟩
  refine ⟨m * (1 - fr.child.den + fr.child.num) - fr.child.den * fr.child.num, ?_⟩
  unfold Fraction.periodDenominator
  linear_combination (1 - fr.child.den + fr.child.num) * hm

theorem coherentConstantU_eq_zero (fr : ChildFrame) : fr.coherentConstantU = 0 := by
  obtain ⟨r, hr⟩ := symmetry_half fr
  have hV : fr.child.modifiedDeck.transverse + (1, -1) =
      (fr.child.num - fr.child.den + 1, fr.child.num + fr.child.den - 1) := by
    rw [fr.child_modifiedDeck_transverse]
    rfl
  unfold ChildFrame.coherentConstantU ChildFrame.symmetryConstant ChildFrame.tGrade
  rw [hV]
  dsimp only
  have hnum : (fr.child.num - fr.child.den + 1) ^ 2 + 2 * (fr.child.num - fr.child.den + 1) *
      (fr.child.num + fr.child.den - 1) - (fr.child.num + fr.child.den - 1) ^ 2 -
      2 * (fr.child.num + fr.child.den - 1) -
      ((fr.child.num - fr.child.den + 1) + (fr.child.num + fr.child.den - 1)) % 2 =
      2 * (fr.child.den + fr.child.num - fr.child.periodDenominator) := by
    have hp : ((fr.child.num - fr.child.den + 1) + (fr.child.num + fr.child.den - 1)) % 2 = 0 := by omega
    rw [hp]
    unfold Fraction.periodDenominator
    ring
  have ht : fr.child.num * (fr.child.num - fr.child.den + 1) - fr.child.den * (fr.child.num + fr.child.den - 1) =
      fr.child.den + fr.child.num - fr.child.periodDenominator := by
    unfold Fraction.periodDenominator
    ring
  have hh : harmonicGrid (fr.child.num - fr.child.den + 1, fr.child.num + fr.child.den - 1) =
      (fr.child.den + fr.child.num - fr.child.periodDenominator) / 2 := by
    unfold harmonicGrid
    dsimp only
    rw [hnum]
    omega
  rw [hh, ht]
  omega

/-- The kernel period of the earlier field: `G(y + k U) = G y` (zero constant). -/
theorem field_kernel_shift (fr : ChildFrame) {G : Field}
    (hG : HasGeneratorPeriods fr.child G fr.coherentConstantU fr.coherentConstantV) (k : ℤ) (y : Site) :
    G (y + (k * fr.child.den, k * fr.child.num)) = G y := by
  have hU := coherentConstantU_eq_zero fr
  have hK : ∀ z : Site, G (z + (fr.child.den, fr.child.num)) = G z := by
    intro z
    have h := hG.1 z
    rw [fr.child_modifiedDeck_kernel] at h
    rw [h, hU, add_zero]
  induction k using Int.induction_on generalizing y with
  | zero =>
    show G (y + ((0 : ℤ) * fr.child.den, (0 : ℤ) * fr.child.num)) = G y
    rw [zero_mul, zero_mul, Prod.mk_zero_zero, add_zero]
  | succ i ih =>
    have e : y + ((↑i + 1) * fr.child.den, (↑i + 1) * fr.child.num) =
        (y + (↑i * fr.child.den, ↑i * fr.child.num)) + (fr.child.den, fr.child.num) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]
        ring
      · simp only [Prod.snd_add]
        ring
    rw [e, hK, ih]
  | pred i ih =>
    have e : y + ((-↑i - 1) * fr.child.den, (-↑i - 1) * fr.child.num) + (fr.child.den, fr.child.num) =
        y + (-↑i * fr.child.den, -↑i * fr.child.num) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]
        ring
      · simp only [Prod.snd_add]
        ring
    have h1 := hK (y + ((-↑i - 1) * fr.child.den, (-↑i - 1) * fr.child.num))
    rw [e, ih] at h1
    exact h1.symm

/-- The reflection of the earlier field about `I = (1,−1)`: `G(I − z) = G z` (the constant `c_U + c_V + T + κ` vanishes). -/
theorem packet_reflection_I (fr : ChildFrame) {G : Field} (hP : fr.Packet G) (z : Site) :
    G ((1, -1) - z) = G z := by
  obtain ⟨r, hr⟩ := symmetry_half fr
  unfold Fraction.periodDenominator at hr
  have hκ : fr.symmetryConstant = r := by
    unfold ChildFrame.symmetryConstant
    unfold Fraction.periodDenominator
    rw [show fr.child.den + fr.child.num - (fr.child.den ^ 2 + 2 * fr.child.den * fr.child.num - fr.child.num ^ 2) =
      2 * r from hr]
    omega
  have hcV : fr.coherentConstantV = fr.symmetryConstant - (fr.child.den + fr.child.num) := by
    unfold ChildFrame.coherentConstantV ChildFrame.tGrade ChildFrame.centre
    rw [fr.child_modifiedDeck_kernel, fr.child_modifiedDeck_transverse]
    simp only [Prod.fst_add, Prod.snd_add]
    unfold ChildFrame.symmetryConstant
    unfold Fraction.periodDenominator
    ring
  have hU0 := coherentConstantU_eq_zero fr
  have hB : G (z + (fr.child.den, fr.child.num)) = G z := by
    have h := hP.periods.1 z
    rw [fr.child_modifiedDeck_kernel, hU0, add_zero] at h
    exact h
  have hC := hP.periods.2 (z + (fr.child.den, fr.child.num))
  rw [fr.child_modifiedDeck_transverse] at hC
  unfold Fraction.transverseGrade at hC
  simp only [Prod.fst_add, Prod.snd_add] at hC
  have hA := hP.reflection (z + (fr.child.den, fr.child.num) + (fr.child.num - fr.child.den, fr.child.num + fr.child.den))
  have hc : fr.centre - (z + (fr.child.den, fr.child.num) + (fr.child.num - fr.child.den, fr.child.num + fr.child.den)) =
      (1, -1) - z := by
    unfold ChildFrame.centre
    rw [fr.child_modifiedDeck_kernel, fr.child_modifiedDeck_transverse]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
  rw [hc] at hA
  unfold ChildFrame.tGrade at hA
  simp only [Prod.fst_add, Prod.snd_add] at hA
  linear_combination hA + hC + hB + hcV - hr + 2 * hκ

/-- Paragraph 7 (reflection of the quarter-turned field): `f(I − y) = f(y)`. -/
theorem quarterTurn_I_sub (fr : ChildFrame) {G : Field} (hP : fr.Packet G) (y : Site) :
    quarterTurnField G ((1, -1) - y) = quarterTurnField G y := by
  have hZ : (-((1, -1) - y).2, ((1, -1) - y).1 - 1) = (1, -1) - (-y.2, y.1 - 1) := by
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring
  unfold quarterTurnField
  rw [mapSite_quarterTurn_eq, mapSite_quarterTurn_eq, hZ, packet_reflection_I fr hP (-y.2, y.1 - 1),
    harmonicGrid_I_sub]

/-- Paragraph 7: `a(x) = f(x + ε U_q) − f(x)` equals `p(I − x) = f((I − x) − ε U_q) − f(I − x)`. -/
theorem paragraph7_identity (fr : ChildFrame) {G : Field} (hP : fr.Packet G) (frame : ChildFrame) (x : Site) :
    quarterTurnField G (x + (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num)) -
        quarterTurnField G x =
      quarterTurnField G ((1, -1) - x - (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num)) -
        quarterTurnField G ((1, -1) - x) := by
  have h1 := quarterTurn_I_sub fr hP (x + (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num))
  have h2 := quarterTurn_I_sub fr hP x
  rw [show (1, -1) - (x + (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num)) =
      (1, -1) - x - (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num) by abel] at h1
  rw [h1, h2]

/-- The lattice relation `w − ε σ_c = k (D+N, D−N)`, with `w = (n_q+d_q, d_q−n_q)` and `σ_c` the conjugate shortShift. -/
theorem lattice_kernel_rel (frame conj : ChildFrame) (hconj : conj.child = frame.parents.odd.rotate) :
    ∃ k : ℤ, (frame.parents.even.num + frame.parents.even.den - frame.eps * (2 * conj.eps * conj.parents.odd.den),
        frame.parents.even.den - frame.parents.even.num - frame.eps * (2 * conj.eps * conj.parents.odd.num)) =
      (k * (frame.parents.odd.den + frame.parents.odd.num), k * (frame.parents.odd.den - frame.parents.odd.num)) := by
  have hdetU := frame.eps_det_even
  have hX := ChildFrame.conj_child_det frame conj hconj
  have hε := frame.eps_sq_one
  have hεc := conj.eps_sq_one
  set v1 : ℤ := frame.parents.even.num + frame.parents.even.den - frame.eps * (2 * conj.eps * conj.parents.odd.den)
    with hv1
  set v2 : ℤ := frame.parents.even.den - frame.parents.even.num - frame.eps * (2 * conj.eps * conj.parents.odd.num)
    with hv2
  have hv : (frame.parents.odd.den - frame.parents.odd.num) * v1 - (frame.parents.odd.den + frame.parents.odd.num) * v2 = 0 := by
    rw [hv1, hv2]
    linear_combination (-2 : ℤ) * hdetU + 2 * frame.eps * conj.eps * hX + 2 * frame.eps * hεc
  have hbez : (conj.eps * conj.parents.odd.num) * (frame.parents.odd.den + frame.parents.odd.num) +
      (-(conj.eps * conj.parents.odd.den)) * (frame.parents.odd.den - frame.parents.odd.num) = 1 := by
    linear_combination conj.eps * hX + hεc
  refine ⟨(conj.eps * conj.parents.odd.num) * v1 + (-(conj.eps * conj.parents.odd.den)) * v2, ?_⟩
  have hk1 : v1 = (frame.parents.odd.den + frame.parents.odd.num) *
      ((conj.eps * conj.parents.odd.num) * v1 + (-(conj.eps * conj.parents.odd.den)) * v2) := by
    linear_combination (-v1) * hbez + (-(conj.eps * conj.parents.odd.den)) * hv
  have hk2 : v2 = (frame.parents.odd.den - frame.parents.odd.num) *
      ((conj.eps * conj.parents.odd.num) * v1 + (-(conj.eps * conj.parents.odd.den)) * v2) := by
    linear_combination (-v2) * hbez + (-(conj.eps * conj.parents.odd.num)) * hv
  exact Prod.ext (by show v1 = _; linear_combination hk1) (by show v2 = _; linear_combination hk2)

/-- Paragraph 6: `f(x − V_q) − f(x) + a_q·x + c_e = (1 + ε) − (G(Zx) − G(Zx + ε σ_c))`. -/
theorem paragraph6_identity (frame conj : ChildFrame) {G : Field}
    (hconj : conj.child = frame.parents.odd.rotate) (hP : conj.Packet G) (x : Site) :
    quarterTurnField G (x - (frame.parents.even.num - frame.parents.even.den,
        frame.parents.even.num + frame.parents.even.den)) - quarterTurnField G x +
      (frame.parents.even.num * x.1 - frame.parents.even.den * x.2) +
      ((frame.parents.even.den ^ 2 + 2 * frame.parents.even.den * frame.parents.even.num -
          frame.parents.even.num ^ 2 - frame.parents.even.den - frame.parents.even.num) / 2 +
        2 * ((1 + frame.eps) / 2)) =
      (1 + frame.eps) - (G (-x.2, x.1 - 1) -
        G ((-x.2, x.1 - 1) + (frame.eps * (2 * conj.eps * conj.parents.odd.den),
          frame.eps * (2 * conj.eps * conj.parents.odd.num)))) := by
  obtain ⟨a, b⟩ := x
  dsimp only
  obtain ⟨k, hk⟩ := lattice_kernel_rel frame conj hconj
  obtain ⟨hk1, hk2⟩ := Prod.mk.inj hk
  obtain ⟨hnum, hden⟩ := conj_child_num_den hconj
  have heven : (frame.parents.even.num + frame.parents.even.den) % 2 = 0 := frame.valid.even_parity
  obtain ⟨m, hm⟩ : ∃ m : ℤ, frame.parents.even.num + frame.parents.even.den = 2 * m :=
    ⟨(frame.parents.even.num + frame.parents.even.den) / 2, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s : ℤ, 2 * s = frame.parents.even.num + frame.parents.even.den -
      (frame.parents.even.den ^ 2 + 2 * frame.parents.even.den * frame.parents.even.num -
        frame.parents.even.num ^ 2) :=
    ⟨m - m * (frame.parents.even.den - frame.parents.even.num) - frame.parents.even.den * frame.parents.even.num,
      by linear_combination (frame.parents.even.den - frame.parents.even.num - 1) * hm⟩
  have hce : (frame.parents.even.den ^ 2 + 2 * frame.parents.even.den * frame.parents.even.num -
      frame.parents.even.num ^ 2 - frame.parents.even.den - frame.parents.even.num) / 2 = -s := by
    have h2 : frame.parents.even.den ^ 2 + 2 * frame.parents.even.den * frame.parents.even.num -
        frame.parents.even.num ^ 2 - frame.parents.even.den - frame.parents.even.num = -(2 * s) := by
      linear_combination hs
    rw [h2]
    omega
  have hW : 2 * ((1 + frame.eps) / 2) = 1 + frame.eps := by
    rcases frame.eps_unit with h | h <;> rw [h] <;> norm_num
  have hZV : (-(b - (frame.parents.even.num + frame.parents.even.den)),
      a - (frame.parents.even.num - frame.parents.even.den) - 1) =
      (-b, a - 1) + (frame.parents.even.num + frame.parents.even.den, frame.parents.even.den - frame.parents.even.num) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add]
      ring
    · simp only [Prod.snd_add]
      ring
  have hsh : (-b, a - 1) + (frame.parents.even.num + frame.parents.even.den, frame.parents.even.den - frame.parents.even.num) =
      ((-b, a - 1) + (frame.eps * (2 * conj.eps * conj.parents.odd.den), frame.eps * (2 * conj.eps * conj.parents.odd.num))) +
        (k * (frame.parents.odd.den + frame.parents.odd.num), k * (frame.parents.odd.den - frame.parents.odd.num)) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add]
      linear_combination hk1
    · simp only [Prod.snd_add]
      linear_combination hk2
  have hG1 : G ((-b, a - 1) + (frame.parents.even.num + frame.parents.even.den, frame.parents.even.den - frame.parents.even.num)) =
      G ((-b, a - 1) + (frame.eps * (2 * conj.eps * conj.parents.odd.den), frame.eps * (2 * conj.eps * conj.parents.odd.num))) := by
    rw [hsh]
    have h := field_kernel_shift conj hP.periods k
      ((-b, a - 1) + (frame.eps * (2 * conj.eps * conj.parents.odd.den), frame.eps * (2 * conj.eps * conj.parents.odd.num)))
    rw [hden, hnum] at h
    exact h
  have hfV : quarterTurnField G ((a, b) - (frame.parents.even.num - frame.parents.even.den,
      frame.parents.even.num + frame.parents.even.den)) =
      G ((-b, a - 1) + (frame.parents.even.num + frame.parents.even.den, frame.parents.even.den - frame.parents.even.num)) +
        harmonicGrid ((a, b) - (frame.parents.even.num - frame.parents.even.den,
          frame.parents.even.num + frame.parents.even.den)) := by
    unfold quarterTurnField
    rw [mapSite_quarterTurn_eq]
    rw [show (-((a, b) - (frame.parents.even.num - frame.parents.even.den,
        frame.parents.even.num + frame.parents.even.den)).2,
        ((a, b) - (frame.parents.even.num - frame.parents.even.den,
        frame.parents.even.num + frame.parents.even.den)).1 - 1) =
        (-(b - (frame.parents.even.num + frame.parents.even.den)),
          a - (frame.parents.even.num - frame.parents.even.den) - 1) from rfl, hZV]
  have hf0 : quarterTurnField G (a, b) = G (-b, a - 1) + harmonicGrid (a, b) := by
    unfold quarterTurnField
    rw [mapSite_quarterTurn_eq]
  have hH : harmonicGrid ((a, b) - (frame.parents.even.num - frame.parents.even.den,
      frame.parents.even.num + frame.parents.even.den)) =
      harmonicGrid (a, b) + (-frame.parents.even.num * a + frame.parents.even.den * b + s) :=
    harmonicGrid_sub_V frame.parents.even.num frame.parents.even.den a b s hs
  rw [hfV, hf0, hH, hG1]
  linarith [hce, hW]

/-- Paragraph 6 from the strong estimates of the conjugate word alone. -/
theorem paragraph6_of_strong {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site) :
    quarterTurnField (standardField (conjWord word))
        (x - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) -
      quarterTurnField (standardField (conjWord word)) x +
        ((frameAt word).parents.even.num * x.1 - (frameAt word).parents.even.den * x.2) +
        (((frameAt word).parents.even.den ^ 2 + 2 * (frameAt word).parents.even.den * (frameAt word).parents.even.num -
            (frameAt word).parents.even.num ^ 2 - (frameAt word).parents.even.den - (frameAt word).parents.even.num) / 2 +
          2 * ((1 + (frameAt word).eps) / 2)) =
      (1 + (frameAt word).eps) -
        (standardField (conjWord word) (-x.2, x.1 - 1) -
          standardField (conjWord word) ((-x.2, x.1 - 1) +
            ((frameAt word).eps * (2 * (frameAt (conjWord word)).eps * (frameAt (conjWord word)).parents.odd.den),
              (frameAt word).eps * (2 * (frameAt (conjWord word)).eps * (frameAt (conjWord word)).parents.odd.num)))) :=
  paragraph6_identity (frameAt word) (frameAt (conjWord word)) (frameAt_conj_child h) hSE.packet x

/-- Paragraph 7 from the strong estimates of the conjugate word alone: `a(x) = p(I − x)`. -/
theorem paragraph7_of_strong {word : Word}
    (hSE : StrongEstimates (conjWord word)) (x : Site) :
    quarterTurnField (standardField (conjWord word))
        (x + ((frameAt word).eps * (frameAt word).parents.even.den, (frameAt word).eps * (frameAt word).parents.even.num)) -
      quarterTurnField (standardField (conjWord word)) x =
      quarterTurnField (standardField (conjWord word))
          ((1, -1) - x - ((frameAt word).eps * (frameAt word).parents.even.den,
            (frameAt word).eps * (frameAt word).parents.even.num)) -
        quarterTurnField (standardField (conjWord word)) ((1, -1) - x) :=
  paragraph7_identity (frameAt (conjWord word)) hSE.packet (frameAt word) x

end FLatticePaper.Induction
