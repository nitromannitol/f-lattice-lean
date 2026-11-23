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

end FLatticePaper.Tiles.CeilWords
