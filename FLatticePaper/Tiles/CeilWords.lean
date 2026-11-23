import FLatticePaper.Tiles.SiteScope

/-! Task 53, item 4 (the mechanical words of the standard tiles): the forward horizontal words are ceiling words.

`CeilWord x k l` says: `x` has length `l`, and for every prefix of length `j ≤ l`, with `c` its number of `q`s, `l c − l < j k ≤ l c`,
i.e. `c = ⌈j k / l⌉`. The Q9 cursor `b_j = ⌈N j / L⌉` is this property with `(k, l) = (N, L)`.

`ceil_append` is the concatenation rule for adjacent slopes (`k1 l2 − k2 l1 = 1`). The word recursion `childWords` concatenates the
two current words in the order given by the parity of the number of ones, so the quad invariant follows by induction over the word
(`quadAt_inv`). -/

namespace FLatticePaper.Tiles.CeilWords

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteScope

/-- The number of `q`s among the first `j` letters. -/
def qPrefix (x : BinaryWord) (j : ℕ) : ℤ := ((x.take j).count Letter.q : ℤ)

/-- The ceiling-word property of slope `k / l`. -/
def CeilWord (x : BinaryWord) (k l : ℤ) : Prop :=
  (x.length : ℤ) = l ∧ ∀ j : ℕ, (j : ℤ) ≤ l → l * qPrefix x j - l < (j : ℤ) * k ∧ (j : ℤ) * k ≤ l * qPrefix x j

/-- The whole word of a ceiling word of slope `k/l` has `k` letters `q`. -/
theorem ceil_total (x : BinaryWord) (k l : ℤ) (hx : CeilWord x k l) (hl : 1 ≤ l) : qPrefix x (x.length) = k := by
  obtain ⟨hxl, hxc⟩ := hx
  have hL : (x.length : ℤ) = l := hxl
  obtain ⟨h1, h2⟩ := hxc (x.length) (by omega)
  rw [hL] at h1 h2
  have hlen : x.take x.length = x := List.take_length
  have hc1 : qPrefix x (x.length) ≤ k := by
    by_contra h
    push Not at h
    nlinarith
  have hc2 : k ≤ qPrefix x (x.length) := by
    by_contra h
    push Not at h
    nlinarith
  omega

/-- The prefix of an append of length `|x| + j` is `x` followed by the prefix of length `j` of the second word. -/
theorem take_append_length_add {α : Type} (x y : List α) (j : ℕ) :
    (x ++ y).take (x.length + j) = x ++ y.take j := by
  induction x with
  | nil => simp
  | cons a x ih =>
    rw [List.cons_append, List.length_cons, show x.length + 1 + j = (x.length + j) + 1 by omega,
      List.take_succ_cons, ih, List.cons_append]

/-- **Concatenation.** Adjacent slopes with `k1 l2 − k2 l1 = 1` concatenate. -/
theorem ceil_append {x y : BinaryWord} {k1 l1 k2 l2 : ℤ} (hx : CeilWord x k1 l1) (hy : CeilWord y k2 l2)
    (hl1 : 1 ≤ l1) (hl2 : 1 ≤ l2) (hdet : k1 * l2 - k2 * l1 = 1) : CeilWord (x ++ y) (k1 + k2) (l1 + l2) := by
  obtain ⟨hxl, hxc⟩ := hx
  obtain ⟨hyl, hyc⟩ := hy
  refine ⟨?_, ?_⟩
  · rw [List.length_append]
    push_cast
    omega
  intro j hj
  by_cases hjx : j ≤ x.length
  · -- the prefix lies inside `x`
    have hjl1 : (j : ℤ) ≤ l1 := by omega
    have htake : (x ++ y).take j = x.take j := List.take_append_of_le_length hjx
    have hq : qPrefix (x ++ y) j = qPrefix x j := by unfold qPrefix; rw [htake]
    obtain ⟨h1, h2⟩ := hxc j (by omega)
    rw [hq]
    have hid : l1 * ((l1 + l2) * qPrefix x j - (j : ℤ) * (k1 + k2)) =
        (l1 + l2) * (l1 * qPrefix x j - (j : ℤ) * k1) + (j : ℤ) := by
      linear_combination (j : ℤ) * hdet
    have hD0 : 0 ≤ (l1 + l2) * qPrefix x j - (j : ℤ) * (k1 + k2) := by
      by_contra hc
      push Not at hc
      nlinarith [mul_pos (show (0 : ℤ) < l1 by omega) (show (0 : ℤ) < -((l1 + l2) * qPrefix x j - (j : ℤ) * (k1 + k2)) by linarith)]
    have hDl : (l1 + l2) * qPrefix x j - (j : ℤ) * (k1 + k2) < l1 + l2 := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ l1 + l2 by omega) (show (0 : ℤ) ≤ l1 - 1 - (l1 * qPrefix x j - (j : ℤ) * k1) by linarith)]
    constructor
    · linarith
    · linarith
  · -- the prefix is all of `x` followed by a prefix of `y`
    push Not at hjx
    obtain ⟨j', hj'⟩ : ∃ j' : ℕ, j = x.length + j' := ⟨j - x.length, by omega⟩
    have hj'l : (j' : ℤ) ≤ l2 := by
      have : (j : ℤ) ≤ l1 + l2 := hj
      rw [hj'] at this
      push_cast at this
      omega
    have hxtot : qPrefix x (x.length) = k1 := ceil_total x k1 l1 ⟨hxl, hxc⟩ hl1
    have htake : (x ++ y).take j = x ++ y.take j' := by
      rw [hj']
      exact take_append_length_add x y j'
    have hcx : ((x.count Letter.q : ℕ) : ℤ) = k1 := by
      rw [← hxtot]
      unfold qPrefix
      rw [List.take_length]
    have hq : qPrefix (x ++ y) j = k1 + qPrefix y j' := by
      unfold qPrefix
      rw [htake, List.count_append, Nat.cast_add, hcx]
    rw [hq]
    obtain ⟨h1, h2⟩ := hyc j' hj'l
    have hjrep : (j : ℤ) = l1 + (j' : ℤ) := by
      rw [hj', ← hxl]
      push_cast
      ring
    rw [hjrep]
    have hid : l2 * ((l1 + l2) * (k1 + qPrefix y j') - (l1 + (j' : ℤ)) * (k1 + k2)) =
        l2 + (l1 + l2) * (l2 * qPrefix y j' - (j' : ℤ) * k2) - (j' : ℤ) := by
      linear_combination (l2 - (j' : ℤ)) * hdet
    have hD0 : 0 ≤ (l1 + l2) * (k1 + qPrefix y j') - (l1 + (j' : ℤ)) * (k1 + k2) := by
      by_contra hc
      push Not at hc
      nlinarith [mul_pos (show (0 : ℤ) < l2 by omega) (show (0 : ℤ) < -((l1 + l2) * (k1 + qPrefix y j') - (l1 + (j' : ℤ)) * (k1 + k2)) by linarith)]
    have hDl : (l1 + l2) * (k1 + qPrefix y j') - (l1 + (j' : ℤ)) * (k1 + k2) < l1 + l2 := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ l1 + l2 by omega) (show (0 : ℤ) ≤ l2 - 1 - (l2 * qPrefix y j' - (j' : ℤ) * k2) by linarith)]
    constructor
    · linarith
    · linarith

/-! ### The two concatenation shapes of `childWords` -/

/-- The child rule of `childWords` in both parities. The first output is `y y x` (resp. `x y y`) and the second `y x` (resp. `x y`),
according to the sign of `kE lO − kO lE`. -/
theorem childWords_ceil (word : Word) {x y : BinaryWord} {kO lO kE lE : ℤ} (hx : CeilWord x kO lO) (hy : CeilWord y kE lE)
    (hlO : 1 ≤ lO) (hlE : 1 ≤ lE) (hdet : kE * lO - kO * lE = 1 ∨ kE * lO - kO * lE = -1)
    (hpar : word.count .one % 2 = 0 ↔ kE * lO - kO * lE = 1) :
    CeilWord (childWords word x y).1 (2 * kE + kO) (2 * lE + lO) ∧
      CeilWord (childWords word x y).2 (kE + kO) (lE + lO) := by
  rcases hdet with h1 | h1
  · have hc : word.count .one % 2 = 0 := hpar.mpr h1
    unfold childWords
    rw [if_pos hc]
    have A : CeilWord (y ++ x) (kE + kO) (lE + lO) := ceil_append hy hx hlE hlO h1
    have B : CeilWord (y ++ (y ++ x)) (kE + (kE + kO)) (lE + (lE + lO)) :=
      ceil_append hy A hlE (by omega) (by linarith)
    refine ⟨?_, A⟩
    have e1 : 2 * kE + kO = kE + (kE + kO) := by ring
    have e2 : 2 * lE + lO = lE + (lE + lO) := by ring
    rw [e1, e2, List.append_assoc]
    exact B
  · have hc : ¬ word.count .one % 2 = 0 := fun h => by
      have := hpar.mp h
      omega
    unfold childWords
    rw [if_neg hc]
    have A : CeilWord (x ++ y) (kO + kE) (lO + lE) := ceil_append hx hy hlO hlE (by linarith)
    have B : CeilWord ((x ++ y) ++ y) (kO + kE + kE) (lO + lE + lE) :=
      ceil_append A hy (by omega) hlE (by linarith)
    refine ⟨?_, ?_⟩
    · have e1 : 2 * kE + kO = kO + kE + kE := by ring
      have e2 : 2 * lE + lO = lO + lE + lE := by ring
      rw [e1, e2]
      exact B
    · have e1 : kE + kO = kO + kE := by ring
      have e2 : lE + lO = lO + lE := by ring
      rw [e1, e2]
      exact A

/-! ### Slopes of the current fractions -/

/-- The ceiling slope of an odd-type fraction: `(2 num, den + num)`. -/
def sOdd (f : Fraction) : ℤ × ℤ := (2 * f.num, f.den + f.num)

/-- The ceiling slope of an even-type fraction: `(num, (den + num)/2)`. -/
def sEven (f : Fraction) : ℤ × ℤ := (f.num, (f.den + f.num) / 2)

/-- The odd current fraction after a digit `one`: `(Parents.mk O E).current .odd = O + E`, with slope the sum of the two slopes. -/
theorem sOdd_cur_one (O E : Fraction) (hE : (E.num + E.den) % 2 = 0) :
    sOdd ((Parents.mk O E).current .odd) = (2 * (sEven E).1 + (sOdd O).1, 2 * (sEven E).2 + (sOdd O).2) := by
  unfold sOdd sEven
  simp only [Parents.current, Parents.combine, one_mul]
  ext
  · simp only
    ring
  · simp only
    omega

/-- The even current fraction `2 O + E` has the slope sum. -/
theorem sEven_cur_two (O E : Fraction) :
    sEven ((Parents.mk O E).current .even) = ((sEven E).1 + (sOdd O).1, (sEven E).2 + (sOdd O).2) := by
  unfold sOdd sEven
  simp only [Parents.current, Parents.combine, one_mul]
  ext
  · simp only
    ring
  · simp only
    omega

/-- The determinant in the digit `one` step equals the determinant of the parents. -/
theorem sig_one (P Q : Fraction) (hQ : (Q.num + Q.den) % 2 = 0) :
    (sEven ((Parents.mk P Q).current .even)).1 * (sOdd ((Parents.mk P Q).current .odd)).2 -
      (sOdd ((Parents.mk P Q).current .odd)).1 * (sEven ((Parents.mk P Q).current .even)).2 = Fraction.det P Q := by
  unfold sOdd sEven Fraction.det
  simp only [Parents.current, Parents.combine, one_mul]
  have hY : 2 * ((2 * P.den + Q.den + (2 * P.num + Q.num)) / 2) = 2 * P.den + Q.den + (2 * P.num + Q.num) := by omega
  linear_combination (-(P.num + Q.num)) * hY

/-- The determinant in the digit `two` and `three` steps is minus the determinant of the parents. -/
theorem sig_two (P Q : Fraction) (hQ : (Q.num + Q.den) % 2 = 0) :
    (sEven Q).1 * (sOdd ((Parents.mk P Q).current .odd)).2 -
      (sOdd ((Parents.mk P Q).current .odd)).1 * (sEven Q).2 = -Fraction.det P Q := by
  unfold sOdd sEven Fraction.det
  simp only [Parents.current, Parents.combine, one_mul]
  have hY : 2 * ((Q.den + Q.num) / 2) = Q.den + Q.num := by omega
  linear_combination (-(P.num + Q.num)) * hY

theorem sig_three (P Q : Fraction) (hQ : (Q.num + Q.den) % 2 = 0) :
    (sEven ((Parents.mk P Q).current .even)).1 * (sOdd P).2 -
      (sOdd P).1 * (sEven ((Parents.mk P Q).current .even)).2 = -Fraction.det P Q := by
  unfold sOdd sEven Fraction.det
  simp only [Parents.current, Parents.combine, one_mul]
  have hY : 2 * ((2 * P.den + Q.den + (2 * P.num + Q.num)) / 2) = 2 * P.den + Q.den + (2 * P.num + Q.num) := by omega
  linear_combination (-P.num) * hY

/-! ### The quad invariant -/

/-- A word has the ceiling slope `s`. -/
def CeilOf (x : BinaryWord) (s : ℤ × ℤ) : Prop := CeilWord x s.1 s.2

theorem lam_odd_pos (f : Fraction) (h1 : 0 < f.den) (h0 : 0 ≤ f.num) : 1 ≤ (sOdd f).2 := by
  unfold sOdd
  simp only
  omega

theorem lam_even_pos (f : Fraction) (h1 : 0 < f.den) (h0 : 0 ≤ f.num) (hp : (f.num + f.den) % 2 = 0) :
    1 ≤ (sEven f).2 := by
  unfold sEven
  simp only
  omega

/-- The bounds of the odd current fraction `P + Q`. -/
theorem cur_odd_bounds (P Q : Fraction) (hP1 : 0 < P.den) (hP0 : 0 ≤ P.num) (hQ1 : 0 < Q.den) (hQ0 : 0 ≤ Q.num) :
    0 < ((Parents.mk P Q).current .odd).den ∧ 0 ≤ ((Parents.mk P Q).current .odd).num := by
  simp only [Parents.current, Parents.combine, one_mul]
  constructor <;> omega

/-- The bounds and the parity of the even current fraction `2 P + Q`. -/
theorem cur_even_bounds (P Q : Fraction) (hP1 : 0 < P.den) (hP0 : 0 ≤ P.num) (hQ1 : 0 < Q.den) (hQ0 : 0 ≤ Q.num)
    (hQp : (Q.num + Q.den) % 2 = 0) :
    0 < ((Parents.mk P Q).current .even).den ∧ 0 ≤ ((Parents.mk P Q).current .even).num ∧
      (((Parents.mk P Q).current .even).num + ((Parents.mk P Q).current .even).den) % 2 = 0 := by
  simp only [Parents.current, Parents.combine]
  refine ⟨by omega, by omega, by omega⟩

theorem quadAt_snoc_nil (v : Word) (d : Digit) : quadAt [] (v ++ [d]) = (quadAt [] v).step v d := by
  rw [quadAt_append_singleton, List.nil_append]

theorem parentsAt_snoc_one (v : Word) :
    parentsAt (v ++ [Digit.one]) = Parents.mk ((parentsAt v).current .odd) ((parentsAt v).current .even) := by
  rw [parentsAt_append_singleton]
  rfl

theorem parentsAt_snoc_two (v : Word) :
    parentsAt (v ++ [Digit.two]) = Parents.mk ((parentsAt v).current .odd) (parentsAt v).even := by
  rw [parentsAt_append_singleton]
  rfl

theorem parentsAt_snoc_three (v : Word) :
    parentsAt (v ++ [Digit.three]) = Parents.mk (parentsAt v).odd ((parentsAt v).current .even) := by
  rw [parentsAt_append_singleton]
  rfl

/-- The invariant: the four words of the quad are the ceiling words of the slopes of the current and parent fractions. -/
def QuadInv (u : Word) : Prop :=
  CeilOf (quadAt [] u).childP (sOdd ((parentsAt u).current .odd)) ∧
    CeilOf (quadAt [] u).childQ (sEven ((parentsAt u).current .even)) ∧
    CeilOf (quadAt [] u).parentP (sOdd (parentsAt u).odd) ∧
    CeilOf (quadAt [] u).parentQ (sEven (parentsAt u).even)

theorem ceilOf_initial_nil : CeilOf [Letter.q, Letter.q, Letter.p] (sOdd ⟨1, 2⟩) := by
  show CeilWord [Letter.q, Letter.q, Letter.p] 2 3
  refine ⟨by simp, fun j hj => ?_⟩
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> norm_num [qPrefix]

theorem quadInv_nil : QuadInv [] := by
  unfold QuadInv
  have hq : quadAt [] ([] : Word) = initialQuad [] := rfl
  have hO : (parentsAt ([] : Word)).current .odd = ⟨1, 2⟩ := SiteBase.curO_nil
  have hE : (parentsAt ([] : Word)).current .even = ⟨1, 3⟩ := SiteBase.curE_nil
  have hP : (parentsAt ([] : Word)).odd = ⟨0, 1⟩ := rfl
  have hQ : (parentsAt ([] : Word)).even = ⟨1, 1⟩ := rfl
  rw [hq, hO, hE, hP, hQ]
  have e1 : (initialQuad ([] : Word)).childP = [Letter.q, Letter.q, Letter.p] := rfl
  have e2 : (initialQuad ([] : Word)).childQ = [Letter.q, Letter.p] := rfl
  have e3 : (initialQuad ([] : Word)).parentP = [Letter.p] := rfl
  have e4 : (initialQuad ([] : Word)).parentQ = [Letter.q] := rfl
  rw [e1, e2, e3, e4]
  refine ⟨ceilOf_initial_nil, ?_, ?_, ?_⟩
  · show CeilWord [Letter.q, Letter.p] 1 2
    refine ⟨by simp, fun j hj => ?_⟩
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl <;> norm_num [qPrefix]
  · show CeilWord [Letter.p] 0 1
    refine ⟨by simp, fun j hj => ?_⟩
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> norm_num [qPrefix]
  · show CeilWord [Letter.q] 1 1
    refine ⟨by simp, fun j hj => ?_⟩
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> norm_num [qPrefix]

theorem quadInv_all (u : Word) : QuadInv u := by
  induction u using List.reverseRecOn with
  | nil => exact quadInv_nil
  | append_singleton v d ih =>
    obtain ⟨i1, i2, i3, i4⟩ := ih
    have hv := parentsAt_valid v
    have hP1 : 0 < (parentsAt v).odd.den := hv.odd_bounds.1
    have hP0 : 0 ≤ (parentsAt v).odd.num := hv.odd_bounds.2.1
    have hQ1 : 0 < (parentsAt v).even.den := hv.even_bounds.1
    have hQ0 : 0 ≤ (parentsAt v).even.num := hv.even_bounds.2.1
    have hQp : ((parentsAt v).even.num + (parentsAt v).even.den) % 2 = 0 := hv.even_parity
    have hdet : (parentsAt v).odd.det (parentsAt v).even = 2 * (phase v : ℤ) - 1 := det_parentsAt v
    have hphase : phase v = v.count Digit.one % 2 := rfl
    have hph : phase v < 2 := by rw [hphase]; omega
    have hO : 0 < ((parentsAt v).current .odd).den ∧ 0 ≤ ((parentsAt v).current .odd).num :=
      cur_odd_bounds _ _ hP1 hP0 hQ1 hQ0
    have hE : 0 < ((parentsAt v).current .even).den ∧ 0 ≤ ((parentsAt v).current .even).num ∧
        (((parentsAt v).current .even).num + ((parentsAt v).current .even).den) % 2 = 0 :=
      cur_even_bounds _ _ hP1 hP0 hQ1 hQ0 hQp
    have hlO : 1 ≤ (sOdd ((parentsAt v).current .odd)).2 := lam_odd_pos _ hO.1 hO.2
    have hlE : 1 ≤ (sEven ((parentsAt v).current .even)).2 := lam_even_pos _ hE.1 hE.2.1 hE.2.2
    have hlP : 1 ≤ (sOdd (parentsAt v).odd).2 := lam_odd_pos _ hP1 hP0
    have hlQ : 1 ≤ (sEven (parentsAt v).even).2 := lam_even_pos _ hQ1 hQ0 hQp
    have hEpar := hE.2.2
    cases d with
    | one =>
      have hcount : (v ++ [Digit.one]).count Digit.one = v.count Digit.one + 1 := by simp [List.count_append]
      have hσ : (sEven ((parentsAt v).current .even)).1 * (sOdd ((parentsAt v).current .odd)).2 -
          (sOdd ((parentsAt v).current .odd)).1 * (sEven ((parentsAt v).current .even)).2 = 2 * (phase v : ℤ) - 1 :=
        (sig_one _ _ hQp).trans hdet
      have A := childWords_ceil (v ++ [Digit.one]) i1 i2 hlO hlE (by rw [hσ]; omega)
        (by rw [hcount, hσ, hphase]; omega)
      unfold QuadInv
      rw [quadAt_snoc_nil, parentsAt_snoc_one]
      refine ⟨?_, ?_, i1, i2⟩
      · unfold CeilOf
        rw [sOdd_cur_one _ _ hEpar]
        exact A.1
      · unfold CeilOf
        rw [sEven_cur_two]
        exact A.2
    | two =>
      have hcount : (v ++ [Digit.two]).count Digit.one = v.count Digit.one := by simp [List.count_append]
      have hσ : (sEven (parentsAt v).even).1 * (sOdd ((parentsAt v).current .odd)).2 -
          (sOdd ((parentsAt v).current .odd)).1 * (sEven (parentsAt v).even).2 = -(2 * (phase v : ℤ) - 1) := by
        have := sig_two (parentsAt v).odd (parentsAt v).even hQp
        rw [hdet] at this
        exact this
      have A := childWords_ceil (v ++ [Digit.two]) i1 i4 hlO hlQ (by rw [hσ]; omega)
        (by rw [hcount, hσ, hphase]; omega)
      unfold QuadInv
      rw [quadAt_snoc_nil, parentsAt_snoc_two]
      refine ⟨?_, ?_, i1, i4⟩
      · unfold CeilOf
        rw [sOdd_cur_one _ _ hQp]
        exact A.1
      · unfold CeilOf
        rw [sEven_cur_two]
        exact A.2
    | three =>
      have hcount : (v ++ [Digit.three]).count Digit.one = v.count Digit.one := by simp [List.count_append]
      have hσ : (sEven ((parentsAt v).current .even)).1 * (sOdd (parentsAt v).odd).2 -
          (sOdd (parentsAt v).odd).1 * (sEven ((parentsAt v).current .even)).2 = -(2 * (phase v : ℤ) - 1) := by
        have := sig_three (parentsAt v).odd (parentsAt v).even hQp
        rw [hdet] at this
        exact this
      have A := childWords_ceil (v ++ [Digit.three]) i3 i2 hlP hlE (by rw [hσ]; omega)
        (by rw [hcount, hσ, hphase]; omega)
      unfold QuadInv
      rw [quadAt_snoc_nil, parentsAt_snoc_three]
      refine ⟨?_, ?_, i3, i2⟩
      · unfold CeilOf
        rw [sOdd_cur_one _ _ hEpar]
        exact A.1
      · unfold CeilOf
        rw [sEven_cur_two]
        exact A.2

end FLatticePaper.Tiles.CeilWords
