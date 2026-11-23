import FLatticePaper.Plane.Induction.Q3VPath
import FLatticePaper.Plane.Induction.Q3Paragraph8

/-! Task 60, paragraph 8 (the V star): `a ∈ {0,1}` on the native old V vertices, the translation by `i U_p + j V_p`, and the
drop lemma.

With `f = quarterTurnField G` (`G = standardField (conjWord word)`) and `a(x) = f(x + ε U_q) − f(x)` (`aVal`):
* `aVal_eq_price`: `a(x) = P(Z(x + ε U_q)) − c₀` (the paragraph-5 identity of the strong estimates);
* `V_box_a_zero_or_one`: if `t_p(x) ∈ [N − B, D]` (in particular on the native V box, `t_p ∈ [r − B, 0]`), then `a(x) ∈ {0,1}`;
* `aVal_translate_V`: `a(x + V_p) = a(x) + 1` (price drift along `U_c`); `aVal_translate_U`: `a(x + U_p) = a(x)` (zero period
  along `V_c`); `aVal_translate_UV_int`: `a(x + i U_p + j V_p) = a(x) + j`;
* `drop_forces_j_zero`: a drop `1 → 0` inside `{j, j+1}` forces `j = 0`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The paragraph-8 value `a(x) = f(x + ε U_q) − f(x)` of a frame, for the field `G`. -/
def aVal (frame : ChildFrame) (G : Field) (x : Site) : ℤ :=
  quarterTurnField G (x + (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num)) -
    quarterTurnField G x

theorem aVal_eq_price {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site) :
    aVal (frameAt word) (standardField (conjWord word)) x =
      (frameAt (conjWord word)).price (standardField (conjWord word))
          (-(x + ((frameAt word).eps * (frameAt word).parents.even.den,
            (frameAt word).eps * (frameAt word).parents.even.num)).2,
            (x + ((frameAt word).eps * (frameAt word).parents.even.den,
              (frameAt word).eps * (frameAt word).parents.even.num)).1 - 1) -
        (frameAt (conjWord word)).cutPrice := by
  have hp := paragraph5_field_identity_of_strong h hSE
    (x + ((frameAt word).eps * (frameAt word).parents.even.den, (frameAt word).eps * (frameAt word).parents.even.num))
  have hxx : x + ((frameAt word).eps * (frameAt word).parents.even.den, (frameAt word).eps * (frameAt word).parents.even.num) +
      (-(frameAt word).eps * (frameAt word).parents.even.den, -(frameAt word).eps * (frameAt word).parents.even.num) = x := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add]
      ring
    · simp only [Prod.snd_add]
      ring
  rw [hxx] at hp
  unfold aVal
  linarith

theorem frameAt_conj_num_den {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    (frameAt (conjWord word)).child.num = (frameAt word).parents.odd.den - (frameAt word).parents.odd.num ∧
      (frameAt (conjWord word)).child.den = (frameAt word).parents.odd.den + (frameAt word).parents.odd.num := by
  have hc : (frameAt (conjWord word)).child = (frameAt word).parents.odd.rotate := frameAt_conj_child h
  exact conj_child_num_den hc

/-- Paragraph 8, the V star: `a(x) ∈ {0,1}` when `t_p(x) ∈ [N − B, D]`. -/
theorem V_box_a_zero_or_one {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site)
    (hlo : (frameAt word).parents.odd.num -
        ((frameAt word).parents.odd.den ^ 2 + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num -
          (frameAt word).parents.odd.num ^ 2) ≤ (frameAt word).parentTGrade x)
    (hhi : (frameAt word).parentTGrade x ≤ (frameAt word).parents.odd.den) :
    aVal (frameAt word) (standardField (conjWord word)) x = 0 ∨
      aVal (frameAt word) (standardField (conjWord word)) x = 1 := by
  have hN := frameAt_odd_num_pos h
  obtain ⟨-, -, hNle⟩ := (frameAt word).valid.odd_bounds
  have hodd : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  have hND : (frameAt word).parents.odd.num + 1 ≤ (frameAt word).parents.odd.den := by omega
  have hB : 0 < (frameAt word).parents.odd.den ^ 2 + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num -
      (frameAt word).parents.odd.num ^ 2 := by
    nlinarith
  have hA := aVal_eq_price h hSE x
  have hpf := price_floor_bound_of_strong h hSE
    (x + ((frameAt word).eps * (frameAt word).parents.even.den, (frameAt word).eps * (frameAt word).parents.even.num))
  have hty := parentTGrade_add_eps_uq (frameAt word) x
  have hfl : parentFloor (frameAt word)
      (x + ((frameAt word).eps * (frameAt word).parents.even.den, (frameAt word).eps * (frameAt word).parents.even.num)) =
      ((frameAt word).parentTGrade
        (x + ((frameAt word).eps * (frameAt word).parents.even.den, (frameAt word).eps * (frameAt word).parents.even.num)) -
        (frameAt word).parents.odd.num) /
      ((frameAt word).parents.odd.den ^ 2 + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num -
        (frameAt word).parents.odd.num ^ 2) := rfl
  by_cases hc : (frameAt word).parentTGrade x + 1 ≤ (frameAt word).parents.odd.num - 1
  · -- the primitive range: the floor is −1, so a ∈ [0, 1]
    have hf : parentFloor (frameAt word)
        (x + ((frameAt word).eps * (frameAt word).parents.even.den, (frameAt word).eps * (frameAt word).parents.even.num)) =
        -1 := by
      rw [hfl, hty]
      apply ediv_eq_neg_one_of_range _ _ hB
      · linarith
      · linarith
    rw [hf] at hpf
    omega
  · -- the zero strip: both arguments vanish, so a = 0
    replace hc := not_le.mp hc
    have hz1 := zeroStrip_of_strong h hSE x (by linarith) (by linarith)
    have hz2 := zeroStrip_of_strong h hSE
      (x + ((frameAt word).eps * (frameAt word).parents.even.den, (frameAt word).eps * (frameAt word).parents.even.num))
      (by rw [hty]; linarith) (by rw [hty]; linarith)
    left
    unfold aVal
    rw [hz1, hz2]
    norm_num

/-- The price drifts by one along `−U_c`, `U_c = (D+N, D−N)` (the conjugate's kernel in the parent's coordinates). -/
theorem price_drift_neg_U {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (z : Site) :
    (frameAt (conjWord word)).price (standardField (conjWord word))
        (z - ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num,
          (frameAt word).parents.odd.den - (frameAt word).parents.odd.num)) =
      (frameAt (conjWord word)).price (standardField (conjWord word)) z + 1 := by
  obtain ⟨hn, hd⟩ := frameAt_conj_num_den h
  have hdr := (hSE.priceDrift (z - ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num,
    (frameAt word).parents.odd.den - (frameAt word).parents.odd.num))).1
  rw [(frameAt (conjWord word)).child_modifiedDeck_kernel, hd, hn, sub_add_cancel] at hdr
  linarith

/-- The price is periodic along `V_c = (−2N, 2D)`, the conjugate's transverse in the parent's coordinates. -/
theorem price_drift_V {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (z : Site) :
    (frameAt (conjWord word)).price (standardField (conjWord word))
        (z + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num -
            ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num),
          (frameAt word).parents.odd.den - (frameAt word).parents.odd.num +
            ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num))) =
      (frameAt (conjWord word)).price (standardField (conjWord word)) z := by
  obtain ⟨hn, hd⟩ := frameAt_conj_num_den h
  have hdr := (hSE.priceDrift z).2
  rw [(frameAt (conjWord word)).child_modifiedDeck_transverse, hn, hd] at hdr
  linarith

/-- `a(x + V_p) = a(x) + 1`, `V_p = (N − D, N + D)`: the price drifts by one along `U_c = (D+N, D−N)`. -/
theorem aVal_translate_V {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site) :
    aVal (frameAt word) (standardField (conjWord word))
        (x + ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den,
          (frameAt word).parents.odd.num + (frameAt word).parents.odd.den)) =
      aVal (frameAt word) (standardField (conjWord word)) x + 1 := by
  have e1 := aVal_eq_price h hSE (x + ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den,
    (frameAt word).parents.odd.num + (frameAt word).parents.odd.den))
  have e0 := aVal_eq_price h hSE x
  have hZ : (-((x + ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den)) +
        ((frameAt word).eps * (frameAt word).parents.even.den, (frameAt word).eps * (frameAt word).parents.even.num)).2,
      (x + ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den) +
        ((frameAt word).eps * (frameAt word).parents.even.den, (frameAt word).eps * (frameAt word).parents.even.num)).1 - 1) =
      (-(x + ((frameAt word).eps * (frameAt word).parents.even.den,
        (frameAt word).eps * (frameAt word).parents.even.num)).2,
        (x + ((frameAt word).eps * (frameAt word).parents.even.den,
          (frameAt word).eps * (frameAt word).parents.even.num)).1 - 1) -
        ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num,
          (frameAt word).parents.odd.den - (frameAt word).parents.odd.num) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub]
      ring
    · simp only [Prod.fst_add, Prod.snd_add, Prod.snd_sub]
      ring
  rw [hZ, price_drift_neg_U h hSE] at e1
  rw [e1, e0]
  linarith

/-- `a(x + U_p) = a(x)`, `U_p = (2D, 2N)`: the price is periodic along `V_c = (−2N, 2D)`. -/
theorem aVal_translate_U {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site) :
    aVal (frameAt word) (standardField (conjWord word))
        (x + (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num)) =
      aVal (frameAt word) (standardField (conjWord word)) x := by
  have e1 := aVal_eq_price h hSE (x + (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num))
  have e0 := aVal_eq_price h hSE x
  have hZ : (-((x + (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num)) +
        ((frameAt word).eps * (frameAt word).parents.even.den, (frameAt word).eps * (frameAt word).parents.even.num)).2,
      ((x + (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num)) +
        ((frameAt word).eps * (frameAt word).parents.even.den, (frameAt word).eps * (frameAt word).parents.even.num)).1 - 1) =
      (-(x + ((frameAt word).eps * (frameAt word).parents.even.den,
        (frameAt word).eps * (frameAt word).parents.even.num)).2,
        (x + ((frameAt word).eps * (frameAt word).parents.even.den,
          (frameAt word).eps * (frameAt word).parents.even.num)).1 - 1) +
        ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num -
            ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num),
          (frameAt word).parents.odd.den - (frameAt word).parents.odd.num +
            ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.snd_add]
      ring
    · simp only [Prod.fst_add, Prod.snd_add]
      ring
  rw [hZ, price_drift_V h hSE] at e1
  rw [e1, e0]

/-- `a(x + j V_p) = a(x) + j` for all integers `j`. -/
theorem aVal_translate_V_int {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (j : ℤ) (x : Site) :
    aVal (frameAt word) (standardField (conjWord word))
        (x + (j * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
          j * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den))) =
      aVal (frameAt word) (standardField (conjWord word)) x + j := by
  induction j using Int.induction_on generalizing x with
  | zero => simp [Prod.mk_zero_zero]
  | succ i ih =>
    have e : x + (((i : ℤ) + 1) * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
        ((i : ℤ) + 1) * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den)) =
        (x + ((i : ℤ) * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
          (i : ℤ) * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den))) +
          ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den,
            (frameAt word).parents.odd.num + (frameAt word).parents.odd.den) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]
        ring
      · simp only [Prod.snd_add]
        ring
    rw [e, aVal_translate_V h hSE, ih]
    ring
  | pred i ih =>
    have e : (x + ((-(i : ℤ) - 1) * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
        (-(i : ℤ) - 1) * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den))) +
        ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den,
          (frameAt word).parents.odd.num + (frameAt word).parents.odd.den) =
        x + (-(i : ℤ) * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
          -(i : ℤ) * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den)) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]
        ring
      · simp only [Prod.snd_add]
        ring
    have h1 := aVal_translate_V h hSE (x + ((-(i : ℤ) - 1) * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
        (-(i : ℤ) - 1) * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den)))
    rw [e, ih] at h1
    linarith

/-- `a(x + i U_p) = a(x)` for all integers `i`. -/
theorem aVal_translate_U_int {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (i : ℤ) (x : Site) :
    aVal (frameAt word) (standardField (conjWord word))
        (x + (i * (2 * (frameAt word).parents.odd.den), i * (2 * (frameAt word).parents.odd.num))) =
      aVal (frameAt word) (standardField (conjWord word)) x := by
  induction i using Int.induction_on generalizing x with
  | zero => simp [Prod.mk_zero_zero]
  | succ k ih =>
    have e : x + (((k : ℤ) + 1) * (2 * (frameAt word).parents.odd.den), ((k : ℤ) + 1) * (2 * (frameAt word).parents.odd.num)) =
        (x + ((k : ℤ) * (2 * (frameAt word).parents.odd.den), (k : ℤ) * (2 * (frameAt word).parents.odd.num))) +
          (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]
        ring
      · simp only [Prod.snd_add]
        ring
    rw [e, aVal_translate_U h hSE, ih]
  | pred k ih =>
    have e : (x + ((-(k : ℤ) - 1) * (2 * (frameAt word).parents.odd.den), (-(k : ℤ) - 1) * (2 * (frameAt word).parents.odd.num))) +
        (2 * (frameAt word).parents.odd.den, 2 * (frameAt word).parents.odd.num) =
        x + (-(k : ℤ) * (2 * (frameAt word).parents.odd.den), -(k : ℤ) * (2 * (frameAt word).parents.odd.num)) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]
        ring
      · simp only [Prod.snd_add]
        ring
    have h1 := aVal_translate_U h hSE (x + ((-(k : ℤ) - 1) * (2 * (frameAt word).parents.odd.den),
        (-(k : ℤ) - 1) * (2 * (frameAt word).parents.odd.num)))
    rw [e, ih] at h1
    exact h1.symm

/-- The combined translation `a(x + i U_p + j V_p) = a(x) + j`. -/
theorem aVal_translate_UV {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (i j : ℤ) (x : Site) :
    aVal (frameAt word) (standardField (conjWord word))
        (x + (i * (2 * (frameAt word).parents.odd.den) + j * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
          i * (2 * (frameAt word).parents.odd.num) + j * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den))) =
      aVal (frameAt word) (standardField (conjWord word)) x + j := by
  have e : x + (i * (2 * (frameAt word).parents.odd.den) + j * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
      i * (2 * (frameAt word).parents.odd.num) + j * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den)) =
      (x + (i * (2 * (frameAt word).parents.odd.den), i * (2 * (frameAt word).parents.odd.num))) +
        (j * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
          j * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den)) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add]
      ring
    · simp only [Prod.snd_add]
      ring
  rw [e, aVal_translate_V_int h hSE j, aVal_translate_U_int h hSE i]

/-- Paragraph 8, the native V vertex: on the box `N − D + 1 ≤ x₁ ≤ 0`, `0 ≤ x₂ ≤ D + N − 1` (the path from `0` to `V_p + I`),
`t_p ∈ [r − B, 0]`, the arguments of `d_f(t_p + 1)` lie in `[N − B + 1, D + 1]`, and `a(x) ∈ {0, 1}`. -/
theorem native_V_a_zero_or_one {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site)
    (hx1 : (frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1 ≤ x.1) (hx2 : x.1 ≤ 0)
    (hx3 : 0 ≤ x.2) (hx4 : x.2 ≤ (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1) :
    aVal (frameAt word) (standardField (conjWord word)) x = 0 ∨
      aVal (frameAt word) (standardField (conjWord word)) x = 1 := by
  have hN := frameAt_odd_num_pos h
  have hD : 0 < (frameAt word).parents.odd.den := (frameAt word).valid.odd_bounds.1
  have hb := vbox_tp_bounds (frameAt word).parents.odd.den (frameAt word).parents.odd.num x.1 x.2 hD.le hN.le
    hx1 hx2 hx3 hx4
  have hlo : (frameAt word).parents.odd.num -
      ((frameAt word).parents.odd.den ^ 2 + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num -
        (frameAt word).parents.odd.num ^ 2) ≤ (frameAt word).parentTGrade x := by
    unfold ChildFrame.parentTGrade
    linarith [hb.1]
  have hhi : (frameAt word).parentTGrade x ≤ (frameAt word).parents.odd.den := by
    unfold ChildFrame.parentTGrade
    linarith [hb.2]
  exact V_box_a_zero_or_one h hSE x hlo hhi

/-- The arguments `t_p(x) + 1` of `d_f` on the native box lie in `[N − B + 1, D + 1]`. -/
theorem native_args_in_range {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (x : Site)
    (hx1 : (frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1 ≤ x.1) (hx2 : x.1 ≤ 0)
    (hx3 : 0 ≤ x.2) (hx4 : x.2 ≤ (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1) :
    (frameAt word).parents.odd.num -
        ((frameAt word).parents.odd.den ^ 2 + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num -
          (frameAt word).parents.odd.num ^ 2) + 1 ≤ (frameAt word).parentTGrade x + 1 ∧
      (frameAt word).parentTGrade x + 1 ≤ (frameAt word).parents.odd.den + 1 := by
  have hN := frameAt_odd_num_pos h
  have hD : 0 < (frameAt word).parents.odd.den := (frameAt word).valid.odd_bounds.1
  have hb := vbox_tp_bounds (frameAt word).parents.odd.den (frameAt word).parents.odd.num x.1 x.2 hD.le hN.le
    hx1 hx2 hx3 hx4
  unfold ChildFrame.parentTGrade
  constructor <;> linarith [hb.1, hb.2]


/-- The drop lemma: a drop `1 → 0` inside a pair `{j, j+1}` forces `j = 0`. -/
theorem drop_forces_j_zero (j u v : ℤ) (hu : u = j ∨ u = j + 1) (hv : v = j ∨ v = j + 1) (h1 : u = 1) (h2 : v = 0) :
    j = 0 := by
  omega

end FLatticePaper.Induction
