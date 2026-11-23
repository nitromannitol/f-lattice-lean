import FLatticePaper.Plane.Induction.VArcOffers
import FLatticePaper.Plane.Induction.ParentStep
import FLatticePaper.Plane.Induction.StrongEstimates

/-! Task (Q4-strips, inequality (2)): the discharge of `ParentStepSign` from the earlier primitive price.

Let `(N, D)` be the odd parent of the current word, `(p, q, ε')` the odd parent and the sign of the earlier conjugate `conj`
(so `conj.child = (D − N, D + N)`, with period `T_e = 2B`, `B = D² + 2DN − N²`). With `δ₀ = (−ε'(p + q), ε'(p − q))`:

* `t_p(δ₀) = −1` and `Z(x + δ₀) = Zx − parentShift` (`Z(x) = (−x₂, x₁ − 1)`);
* the harmonic identity `parent_identity` turns the one-step difference of `Fp = quarterTurnField G` into the earlier price:
  `Fp(x) − Fp(x + δ₀) = P(Zx) − c₀` with `c₀ = cutPrice` of `conj`;
* the price drifts by `−1` along the kernel `(D + N, D − N)` and by `0` along the transverse `(−2N, 2D)`, and lies in
  `[c₀ − 1, c₀]` on the closed polygon; reducing `Zx` to the polygon with `a = −⌊(k − N)/B⌋` kernel periods (`k = t_p(x)`)
  gives `P(Zx) − c₀ ∈ [−⌊(k − N)/B⌋ − 1, −⌊(k − N)/B⌋]`, which has the sign of `N − k`;
* two points of the same parity with `t_p` differing by one differ by `δ₀` and a multiple of `U_p = (2D, 2N)`, a period of `Fp`.

The only input is the earlier price range and drift (`StrongEstimates.priceRange`, `priceDrift`) and the earlier packet. -/

namespace FLatticePaper.Induction
open Farey

/-- The integer floor index of the one-step sign: `⌊(k − N)/B⌋` with `k = t_p(x) = N x₁ − D x₂`, `B = D² + 2DN − N²`. -/
def parentFloor (frame : ChildFrame) (x : Site) : ℤ :=
  (frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2 - frame.parents.odd.num) /
    (frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num - frame.parents.odd.num ^ 2)

/-- Integer multiples of a period: the price shifts by `c` per unit of `U`. -/
theorem price_shift_pair {conj : ChildFrame} {G : Field} (U : Site) (c : ℤ)
    (hU : ∀ z, conj.price G (z + U) = conj.price G z + c) (a : ℤ) (z : Site) :
    conj.price G (z + (a * U.1, a * U.2)) = conj.price G z + c * a := by
  induction a using Int.induction_on with
  | zero =>
    have e0 : z + ((0 : ℤ) * U.1, (0 : ℤ) * U.2) = z := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [e0]
    simp
  | succ i ih =>
    have e : z + (((i : ℤ) + 1) * U.1, ((i : ℤ) + 1) * U.2) =
        (z + ((i : ℤ) * U.1, (i : ℤ) * U.2)) + U := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]
        ring
      · simp only [Prod.snd_add]
        ring
    rw [e, hU, ih]
    ring
  | pred i ih =>
    have e : z + ((-(i : ℤ) - 1) * U.1, (-(i : ℤ) - 1) * U.2) + U =
        z + ((-(i : ℤ)) * U.1, (-(i : ℤ)) * U.2) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]
        ring
      · simp only [Prod.snd_add]
        ring
    have h1 := hU (z + ((-(i : ℤ) - 1) * U.1, (-(i : ℤ) - 1) * U.2))
    rw [e, ih] at h1
    linarith

/-- The earlier child's kernel and transverse vectors in the parent data. -/
theorem earlier_kernel_transverse {frame conj : ChildFrame} (hconj : conj.child = frame.parents.odd.rotate) :
    conj.child.modifiedDeck.kernel = (frame.parents.odd.den + frame.parents.odd.num, frame.parents.odd.den - frame.parents.odd.num) ∧
      conj.child.modifiedDeck.transverse = (-2 * frame.parents.odd.num, 2 * frame.parents.odd.den) := by
  obtain ⟨hnum, hden⟩ := conj_child_num_den hconj
  constructor
  · rw [conj.kernel_coords, hnum, hden]
  · rw [conj.child_modifiedDeck_transverse, hnum, hden]
    refine Prod.ext ?_ ?_
    · dsimp only
      ring
    · dsimp only
      ring

/-- The one-step identity of the parent field: `Fp(x) − Fp(x + δ₀) = P(Zx) − c₀`, with `δ₀ = (−ε'(p + q), ε'(p − q))`. -/
theorem quarterTurnField_sub_shift {conj : ChildFrame} {G : Field} (x : Site) :
    quarterTurnField G x - quarterTurnField G (x + (-conj.eps * (conj.parents.odd.num + conj.parents.odd.den),
        conj.eps * (conj.parents.odd.num - conj.parents.odd.den))) =
      conj.price G (-x.2, x.1 - 1) - conj.cutPrice := by
  have hε : conj.eps = 1 ∨ conj.eps = -1 := conj.eps_unit
  obtain ⟨x1, x2⟩ := x
  have hid := FLatticePaper.Induction.ParentStep.parent_identity conj.parents.odd.num conj.parents.odd.den conj.eps x1 x2 hε
  have hc : conj.cutPrice = (conj.parents.odd.den * conj.parents.odd.den + 2 * conj.parents.odd.num * conj.parents.odd.den -
      conj.parents.odd.num * conj.parents.odd.num - conj.eps * (conj.parents.odd.num + conj.parents.odd.den)) / 2 := by
    unfold ChildFrame.cutPrice Fraction.periodDenominator
    congr 1
    ring
  unfold quarterTurnField ChildFrame.price ChildFrame.parentShift ChildFrame.parentSlope
  rw [mapSite_quarterTurn_eq, mapSite_quarterTurn_eq]
  simp only [Prod.mk_add_mk]
  have hsite2 : (-(x2 + conj.eps * (conj.parents.odd.num - conj.parents.odd.den)),
      x1 + -conj.eps * (conj.parents.odd.num + conj.parents.odd.den) - 1) =
      (-x2, x1 - 1) - (conj.eps * (conj.parents.odd.num - conj.parents.odd.den),
        conj.eps * (conj.parents.odd.num + conj.parents.odd.den)) := by
    refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring
  rw [hsite2]
  linarith [hid, hc]


/-- The box shift: some integer multiple of the period `P` brings `t0` into `[L, L + P)`. -/
theorem exists_box_shift (t0 L P : ℤ) (hP : 0 < P) : ∃ b : ℤ, L ≤ t0 - P * b ∧ t0 - P * b < L + P := by
  have h1 := Int.emod_def (t0 - L) P
  have h2 := Int.emod_nonneg (t0 - L) hP.ne'
  have h3 := Int.emod_lt_of_pos (t0 - L) hP
  refine ⟨(t0 - L) / P, ?_, ?_⟩ <;> linarith

/-- The floor index is negative exactly below `N` (`B > 0`). -/
theorem parentFloor_neg {frame : ChildFrame} {x : Site} (hB : 0 < frame.parents.odd.den ^ 2 +
      2 * frame.parents.odd.den * frame.parents.odd.num - frame.parents.odd.num ^ 2)
    (hk : frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2 < frame.parents.odd.num) :
    parentFloor frame x < 0 := by
  have h1 := Int.emod_def (frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2 - frame.parents.odd.num)
    (frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num - frame.parents.odd.num ^ 2)
  have h2 := Int.emod_nonneg (frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2 - frame.parents.odd.num) hB.ne'
  unfold parentFloor
  by_contra hc
  have hc' := not_lt.mp hc
  nlinarith [mul_nonneg hB.le hc']

theorem parentFloor_nonneg {frame : ChildFrame} {x : Site} (hB : 0 < frame.parents.odd.den ^ 2 +
      2 * frame.parents.odd.den * frame.parents.odd.num - frame.parents.odd.num ^ 2)
    (hk : frame.parents.odd.num ≤ frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2) :
    0 ≤ parentFloor frame x := by
  have h1 := Int.emod_def (frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2 - frame.parents.odd.num)
    (frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num - frame.parents.odd.num ^ 2)
  have h3 := Int.emod_lt_of_pos (frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2 - frame.parents.odd.num) hB
  unfold parentFloor
  by_contra hc
  have hc' := not_le.mp hc
  have hc'' : parentFloor frame x + 1 ≤ 0 := by
    unfold parentFloor
    omega
  nlinarith [mul_nonneg hB.le (show (0:ℤ) ≤ -(((frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2 - frame.parents.odd.num) /
    (frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num - frame.parents.odd.num ^ 2)) + 1) by
      unfold parentFloor at hc''; linarith)]

/-- The earlier price at `Zx`, minus its cut price, lies in `[−⌊(k − N)/B⌋ − 1, −⌊(k − N)/B⌋]`, `k = t_p(x)`. -/
theorem price_floor_bound {frame conj : ChildFrame} {G : Field}
    (hconj : conj.child = frame.parents.odd.rotate)
    (hR : ∀ z ∈ conj.closedPolygon, conj.cutPrice - 1 ≤ conj.price G z ∧ conj.price G z ≤ conj.cutPrice)
    (hD : ∀ z, conj.price G (z + conj.child.modifiedDeck.kernel) - conj.price G z = -1 ∧
      conj.price G (z + conj.child.modifiedDeck.transverse) - conj.price G z = 0)
    (hN1 : 1 ≤ frame.parents.odd.num) (hND : frame.parents.odd.num + 1 ≤ frame.parents.odd.den) (x : Site) :
    -parentFloor frame x - 1 ≤ conj.price G (-x.2, x.1 - 1) - conj.cutPrice ∧
      conj.price G (-x.2, x.1 - 1) - conj.cutPrice ≤ -parentFloor frame x := by
  obtain ⟨hnum, hden⟩ := conj_child_num_den hconj
  obtain ⟨hK, hV⟩ := earlier_kernel_transverse hconj
  rw [hK, hV] at hD
  have hB : 0 < frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num -
      frame.parents.odd.num ^ 2 := by
    nlinarith
  have hD2 : 2 ≤ frame.parents.odd.den := by omega
  have hPD : conj.child.periodDenominator = 2 * (frame.parents.odd.den ^ 2 +
      2 * frame.parents.odd.den * frame.parents.odd.num - frame.parents.odd.num ^ 2) := by
    unfold Fraction.periodDenominator
    rw [hnum, hden]
    ring
  have hsG : ∀ z : Site, conj.sGrade z =
      2 * frame.parents.odd.den * z.1 + 2 * frame.parents.odd.num * z.2 := by
    intro z
    unfold ChildFrame.sGrade
    rw [hnum, hden]
    ring
  have htG : ∀ z : Site, conj.tGrade z =
      (frame.parents.odd.den - frame.parents.odd.num) * z.1 - (frame.parents.odd.den + frame.parents.odd.num) * z.2 := by
    intro z
    unfold ChildFrame.tGrade
    rw [hnum, hden]
  have hcden : conj.child.den + conj.child.num = 2 * frame.parents.odd.den := by
    rw [hnum, hden]
    ring
  have hcnum : conj.child.num = frame.parents.odd.den - frame.parents.odd.num := hnum
  have hdiv := Int.emod_def (frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2 - frame.parents.odd.num)
    (frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num - frame.parents.odd.num ^ 2)
  have hr0 := Int.emod_nonneg (frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2 - frame.parents.odd.num) hB.ne'
  have hr1 := Int.emod_lt_of_pos (frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2 - frame.parents.odd.num) hB
  unfold parentFloor
  generalize hm : (frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2 - frame.parents.odd.num) /
    (frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num - frame.parents.odd.num ^ 2) = m at hdiv ⊢
  generalize hr : (frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2 - frame.parents.odd.num) %
    (frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num - frame.parents.odd.num ^ 2) = r0 at hr0 hr1 hdiv
  -- the shifted point: `−m` kernel periods, then `b` transverse periods
  have hstar : ∀ b : ℤ,
      conj.price G (-x.2 + (-m) * (frame.parents.odd.den + frame.parents.odd.num) + b * (-2 * frame.parents.odd.num),
          (x.1 - 1) + (-m) * (frame.parents.odd.den - frame.parents.odd.num) + b * (2 * frame.parents.odd.den)) =
        conj.price G (-x.2, x.1 - 1) + m := by
    intro b
    have e : (-x.2 + (-m) * (frame.parents.odd.den + frame.parents.odd.num) + b * (-2 * frame.parents.odd.num),
          (x.1 - 1) + (-m) * (frame.parents.odd.den - frame.parents.odd.num) + b * (2 * frame.parents.odd.den)) =
        ((-x.2, x.1 - 1) + ((-m) * (frame.parents.odd.den + frame.parents.odd.num),
          (-m) * (frame.parents.odd.den - frame.parents.odd.num))) + (b * (-2 * frame.parents.odd.num), b * (2 * frame.parents.odd.den)) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]
      · simp only [Prod.snd_add]
    have hP1 := price_shift_pair (conj := conj) (G := G) (frame.parents.odd.den + frame.parents.odd.num,
      frame.parents.odd.den - frame.parents.odd.num) (-1) (fun z => by linarith [hD z]) (-m) (-x.2, x.1 - 1)
    have hP2 := price_shift_pair (conj := conj) (G := G) (-2 * frame.parents.odd.num, 2 * frame.parents.odd.den) 0
      (fun z => by linarith [hD z]) b ((-x.2, x.1 - 1) + ((-m) * (frame.parents.odd.den + frame.parents.odd.num),
          (-m) * (frame.parents.odd.den - frame.parents.odd.num)))
    rw [e, hP2, hP1]
    ring
  have hsS : ∀ b : ℤ, conj.sGrade (-x.2 + (-m) * (frame.parents.odd.den + frame.parents.odd.num) + b * (-2 * frame.parents.odd.num),
          (x.1 - 1) + (-m) * (frame.parents.odd.den - frame.parents.odd.num) + b * (2 * frame.parents.odd.den)) = 2 * r0 := by
    intro b
    rw [hsG]
    linear_combination (-2 : ℤ) * hdiv
  have htS : ∀ b : ℤ, conj.tGrade (-x.2 + (-m) * (frame.parents.odd.den + frame.parents.odd.num) + b * (-2 * frame.parents.odd.num),
          (x.1 - 1) + (-m) * (frame.parents.odd.den - frame.parents.odd.num) + b * (2 * frame.parents.odd.den)) =
        conj.tGrade (-x.2, x.1 - 1) - 2 * (frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num -
          frame.parents.odd.num ^ 2) * b := by
    intro b
    rw [htG, htG]
    ring
  have hpar : ∀ b : ℤ, ((-x.2 + (-m) * (frame.parents.odd.den + frame.parents.odd.num) + b * (-2 * frame.parents.odd.num)) +
      ((x.1 - 1) + (-m) * (frame.parents.odd.den - frame.parents.odd.num) + b * (2 * frame.parents.odd.den))) % 2 =
        (-x.2 + (x.1 - 1)) % 2 := by
    intro b
    have e : (-x.2 + (-m) * (frame.parents.odd.den + frame.parents.odd.num) + b * (-2 * frame.parents.odd.num)) +
        ((x.1 - 1) + (-m) * (frame.parents.odd.den - frame.parents.odd.num) + b * (2 * frame.parents.odd.den)) =
        (-x.2 + (x.1 - 1)) + 2 * ((-m) * frame.parents.odd.den + b * (frame.parents.odd.den - frame.parents.odd.num)) := by
      ring
    rw [e]
    omega
  have hB2 : 0 < 2 * (frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num -
      frame.parents.odd.num ^ 2) := by linarith
  by_cases hev : (-x.2 + (x.1 - 1)) % 2 = 0
  · obtain ⟨b, hb1, hb2⟩ := exists_box_shift (conj.tGrade (-x.2, x.1 - 1))
      (2 - 2 * (frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num -
        frame.parents.odd.num ^ 2)) (2 * (frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num -
        frame.parents.odd.num ^ 2)) hB2
    have hmem : (-x.2 + (-m) * (frame.parents.odd.den + frame.parents.odd.num) + b * (-2 * frame.parents.odd.num),
          (x.1 - 1) + (-m) * (frame.parents.odd.den - frame.parents.odd.num) + b * (2 * frame.parents.odd.den)) ∈
        conj.closedPolygon := by
      refine (conj.mem_closedPolygon_iff _).mpr (Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩)
      · show ((-x.2 + (-m) * (frame.parents.odd.den + frame.parents.odd.num) + b * (-2 * frame.parents.odd.num)) +
          ((x.1 - 1) + (-m) * (frame.parents.odd.den - frame.parents.odd.num) + b * (2 * frame.parents.odd.den))) % 2 = 0
        rw [hpar b]
        exact hev
      · rw [hPD, htS]
        linarith
      · rw [hcden, htS]
        linarith
      · rw [hsS]
        linarith
      · rw [hsS, hPD, hnum]
        linarith
    have hRy := hR _ hmem
    have hP := hstar b
    constructor <;> linarith [hRy.1, hRy.2, hP]
  · obtain ⟨b, hb1, hb2⟩ := exists_box_shift (conj.tGrade (-x.2, x.1 - 1))
      ((frame.parents.odd.den - frame.parents.odd.num) - 2 * (frame.parents.odd.den ^ 2 +
        2 * frame.parents.odd.den * frame.parents.odd.num - frame.parents.odd.num ^ 2))
      (2 * (frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num - frame.parents.odd.num ^ 2)) hB2
    have hmem : (-x.2 + (-m) * (frame.parents.odd.den + frame.parents.odd.num) + b * (-2 * frame.parents.odd.num),
          (x.1 - 1) + (-m) * (frame.parents.odd.den - frame.parents.odd.num) + b * (2 * frame.parents.odd.den)) ∈
        conj.closedPolygon := by
      refine (conj.mem_closedPolygon_iff _).mpr (Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩)
      · show ¬ (((-x.2 + (-m) * (frame.parents.odd.den + frame.parents.odd.num) + b * (-2 * frame.parents.odd.num)) +
          ((x.1 - 1) + (-m) * (frame.parents.odd.den - frame.parents.odd.num) + b * (2 * frame.parents.odd.den))) % 2 = 0)
        rw [hpar b]
        exact hev
      · rw [hnum, hPD, htS]
        linarith
      · rw [hden, htS]
        linarith
      · rw [hden, hnum, hsS]
        linarith
      · rw [hsS, hPD, hden, hnum]
        linarith
    have hRy := hR _ hmem
    have hP := hstar b
    constructor <;> linarith [hRy.1, hRy.2, hP]


/-- The quarter-turned earlier field is periodic along all multiples `j U_p`, `U_p = (2D, 2N)`. -/
theorem quarterTurnField_add_mul_up {frame conj : ChildFrame} {G : Field}
    (hconj : conj.child = frame.parents.odd.rotate)
    (hG : HasGeneratorPeriods conj.child G conj.coherentConstantU conj.coherentConstantV) (j : ℤ) (w : Site) :
    quarterTurnField G (w + (j * (2 * frame.parents.odd.den), j * (2 * frame.parents.odd.num))) =
      quarterTurnField G w := by
  obtain ⟨hnum, hden⟩ := conj_child_num_den hconj
  induction j using Int.induction_on with
  | zero =>
    have e0 : w + ((0 : ℤ) * (2 * frame.parents.odd.den), (0 : ℤ) * (2 * frame.parents.odd.num)) = w := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [e0]
  | succ i ih =>
    have e : w + (((i : ℤ) + 1) * (2 * frame.parents.odd.den), ((i : ℤ) + 1) * (2 * frame.parents.odd.num)) =
        (w + ((i : ℤ) * (2 * frame.parents.odd.den), (i : ℤ) * (2 * frame.parents.odd.num))) +
          (2 * frame.parents.odd.den, 2 * frame.parents.odd.num) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]
        ring
      · simp only [Prod.snd_add]
        ring
    rw [e, quarterTurnField_add_two hG hnum hden, ih]
  | pred i ih =>
    have e : w + ((-(i : ℤ) - 1) * (2 * frame.parents.odd.den), (-(i : ℤ) - 1) * (2 * frame.parents.odd.num)) +
        (2 * frame.parents.odd.den, 2 * frame.parents.odd.num) =
        w + ((-(i : ℤ)) * (2 * frame.parents.odd.den), (-(i : ℤ)) * (2 * frame.parents.odd.num)) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]
        ring
      · simp only [Prod.snd_add]
        ring
    have h1 := quarterTurnField_add_two hG hnum hden
      (w + ((-(i : ℤ) - 1) * (2 * frame.parents.odd.den), (-(i : ℤ) - 1) * (2 * frame.parents.odd.num)))
    rw [e, ih] at h1
    exact h1.symm

/-- A lattice vector with `t_p = 0` and even coordinate sum is a multiple of `U_p`. -/
theorem lattice_of_t_zero {frame : ChildFrame} {w : Site}
    (hcop : IsCoprime frame.parents.odd.num frame.parents.odd.den)
    (hodd : (frame.parents.odd.num + frame.parents.odd.den) % 2 = 1) (hD : 0 < frame.parents.odd.den)
    (hw : frame.parents.odd.num * w.1 - frame.parents.odd.den * w.2 = 0) (hpar : (w.1 + w.2) % 2 = 0) :
    ∃ j : ℤ, w = (j * (2 * frame.parents.odd.den), j * (2 * frame.parents.odd.num)) := by
  have h1 : frame.parents.odd.den ∣ frame.parents.odd.num * w.1 := ⟨w.2, by linarith⟩
  have h2 : frame.parents.odd.den ∣ w.1 := (IsCoprime.symm hcop).dvd_of_dvd_mul_left h1
  obtain ⟨j, hj⟩ := h2
  have h3 : w.2 = frame.parents.odd.num * j := by
    have h4 : frame.parents.odd.den * (frame.parents.odd.num * j) = frame.parents.odd.den * w.2 := by
      rw [hj] at hw
      linear_combination hw
    exact (mul_left_cancel₀ (ne_of_gt hD) h4).symm
  rcases Int.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
  · refine ⟨i, ?_⟩
    apply Prod.ext
    · show w.1 = i * (2 * frame.parents.odd.den)
      rw [hj, hi]
      ring
    · show w.2 = i * (2 * frame.parents.odd.num)
      rw [h3, hi]
      ring
  · exfalso
    have hsum : w.1 + w.2 = 2 * ((frame.parents.odd.den + frame.parents.odd.num) * i) +
        (frame.parents.odd.den + frame.parents.odd.num) := by
      rw [hj, h3, hi]
      ring
    rw [hsum] at hpar
    generalize (frame.parents.odd.den + frame.parents.odd.num) * i = X at hpar
    omega

/-- The sign of the one-step difference of the parent field: `ParentStepSign` from the earlier price (the discharge). -/
theorem parentStepSign_of_price {frame conj : ChildFrame} {G : Field}
    (hconj : conj.child = frame.parents.odd.rotate)
    (hG : HasGeneratorPeriods conj.child G conj.coherentConstantU conj.coherentConstantV)
    (hR : ∀ z ∈ conj.closedPolygon, conj.cutPrice - 1 ≤ conj.price G z ∧ conj.price G z ≤ conj.cutPrice)
    (hD : ∀ z, conj.price G (z + conj.child.modifiedDeck.kernel) - conj.price G z = -1 ∧
      conj.price G (z + conj.child.modifiedDeck.transverse) - conj.price G z = 0)
    (hN1 : 1 ≤ frame.parents.odd.num) (hND : frame.parents.odd.num + 1 ≤ frame.parents.odd.den)
    (hcop : IsCoprime frame.parents.odd.num frame.parents.odd.den)
    (hodd : (frame.parents.odd.num + frame.parents.odd.den) % 2 = 1) :
    ParentStepSign frame (quarterTurnField G) := by
  intro x x' hpar ht
  obtain ⟨hnum, hden⟩ := conj_child_num_den hconj
  have hD0 : 0 < frame.parents.odd.den := by omega
  have hεu := conj.eps_unit
  have hA : frame.parents.odd.den + frame.parents.odd.num = 2 * conj.parents.odd.den + conj.parents.even.den := by
    have := conj.child_den_eq
    omega
  have hB : frame.parents.odd.den - frame.parents.odd.num = 2 * conj.parents.odd.num + conj.parents.even.num := by
    have := conj.child_num_eq
    omega
  have he : conj.eps = conj.parents.odd.num * conj.parents.even.den - conj.parents.even.num * conj.parents.odd.den := rfl
  have hkey : (frame.parents.odd.den + frame.parents.odd.num) * conj.parents.odd.num -
      (frame.parents.odd.den - frame.parents.odd.num) * conj.parents.odd.den = conj.eps := by
    linear_combination conj.parents.odd.num * hA - conj.parents.odd.den * hB - he
  have hδt : frame.parents.odd.num * (-conj.eps * (conj.parents.odd.num + conj.parents.odd.den)) -
      frame.parents.odd.den * (conj.eps * (conj.parents.odd.num - conj.parents.odd.den)) = -1 := by
    rcases hεu with h | h <;> rw [h] at hkey ⊢ <;> linarith
  have hδsum : -conj.eps * (conj.parents.odd.num + conj.parents.odd.den) +
      conj.eps * (conj.parents.odd.num - conj.parents.odd.den) = 2 * (-conj.eps * conj.parents.odd.den) := by
    ring
  have hB0 : 0 < frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num -
      frame.parents.odd.num ^ 2 := by
    nlinarith
  -- the lattice coset of `x' − (x + δ₀)`
  have hw : frame.parents.odd.num * (x'.1 - (x.1 + -conj.eps * (conj.parents.odd.num + conj.parents.odd.den))) -
      frame.parents.odd.den * (x'.2 - (x.2 + conj.eps * (conj.parents.odd.num - conj.parents.odd.den))) = 0 := by
    linarith [ht, hδt]
  have hpw : (x'.1 - (x.1 + -conj.eps * (conj.parents.odd.num + conj.parents.odd.den)) +
      (x'.2 - (x.2 + conj.eps * (conj.parents.odd.num - conj.parents.odd.den)))) % 2 = 0 := by
    have e : (x'.1 - (x.1 + -conj.eps * (conj.parents.odd.num + conj.parents.odd.den)) +
        (x'.2 - (x.2 + conj.eps * (conj.parents.odd.num - conj.parents.odd.den)))) =
        (x'.1 + x'.2) - (x.1 + x.2) - 2 * (-conj.eps * conj.parents.odd.den) := by
      linear_combination hδsum
    rw [e]
    generalize (-conj.eps * conj.parents.odd.den) = Y
    omega
  obtain ⟨j, hj⟩ := lattice_of_t_zero (frame := frame) (w := (x'.1 - (x.1 + -conj.eps * (conj.parents.odd.num + conj.parents.odd.den)),
    x'.2 - (x.2 + conj.eps * (conj.parents.odd.num - conj.parents.odd.den)))) hcop hodd hD0 hw hpw
  have hx' : x' = (x.1 + -conj.eps * (conj.parents.odd.num + conj.parents.odd.den) + j * (2 * frame.parents.odd.den),
      x.2 + conj.eps * (conj.parents.odd.num - conj.parents.odd.den) + j * (2 * frame.parents.odd.num)) := by
    have h1 := congrArg Prod.fst hj
    have h2 := congrArg Prod.snd hj
    simp only at h1 h2
    refine Prod.ext ?_ ?_
    · dsimp only
      linarith
    · dsimp only
      linarith
  have hid : quarterTurnField G x - quarterTurnField G (x.1 + -conj.eps * (conj.parents.odd.num + conj.parents.odd.den),
      x.2 + conj.eps * (conj.parents.odd.num - conj.parents.odd.den)) =
      conj.price G (-x.2, x.1 - 1) - conj.cutPrice :=
    quarterTurnField_sub_shift (conj := conj) (G := G) x
  have hfl := price_floor_bound (frame := frame) hconj hR hD hN1 hND x
  have hB' : 0 < frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num -
      frame.parents.odd.num ^ 2 := hB0
  have hper : quarterTurnField G (x.1 + -conj.eps * (conj.parents.odd.num + conj.parents.odd.den) + j * (2 * frame.parents.odd.den),
      x.2 + conj.eps * (conj.parents.odd.num - conj.parents.odd.den) + j * (2 * frame.parents.odd.num)) =
      quarterTurnField G (x.1 + -conj.eps * (conj.parents.odd.num + conj.parents.odd.den),
        x.2 + conj.eps * (conj.parents.odd.num - conj.parents.odd.den)) :=
    quarterTurnField_add_mul_up hconj hG j (x.1 + -conj.eps * (conj.parents.odd.num + conj.parents.odd.den),
      x.2 + conj.eps * (conj.parents.odd.num - conj.parents.odd.den))
  rw [hx', hper]
  constructor
  · intro hk
    have hm := parentFloor_neg hB' hk
    have hm1 : parentFloor frame x ≤ -1 := by omega
    linarith [hid, hfl.1, hm1]
  · intro hk
    have hm := parentFloor_nonneg hB' hk
    linarith [hid, hfl.2, hm]

/-- `ParentStepSign` of the current word, from the strong estimates of the earlier word `conjWord word`. -/
theorem parentStepSign_of_strong {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) :
    ParentStepSign (frameAt word) (quarterTurnField (standardField (conjWord word))) := by
  have hN := frameAt_odd_num_pos h
  obtain ⟨-, -, hNle⟩ := (frameAt word).valid.odd_bounds
  have hodd : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 := (frameAt word).valid.odd_parity
  have hcop : IsCoprime (frameAt word).parents.odd.num (frameAt word).parents.odd.den := (frameAt word).valid.odd_reduced
  exact parentStepSign_of_price (frameAt_conj_child h) hSE.packet.periods hSE.priceRange hSE.priceDrift
    (by omega) (by omega) hcop hodd


/-- The V-arc range `VArcInputs` of the current word from the strong estimates of the earlier word alone: `ParentStepSign` is
discharged (`parentStepSign_of_strong`). -/
theorem vArcInputs_of_strong_discharged {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {F : Field}
    (hSE : StrongEstimates (conjWord word))
    (hS : (frameAt word).StripInputs ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))))
    (hH : (frameAt word).HeightInputs ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))))
    (hagree : ∀ y ∈ (frameAt word).closedPolygon,
      F y = (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) y)
    (hper : HasGeneratorPeriods (frameAt word).child F 0 (frameAt word).coherentConstantV) :
    VArcInputs (frameAt word) F :=
  vArcInputs_of_strong h hSE (parentStepSign_of_strong h hSE) hS hH hagree hper

end FLatticePaper.Induction
