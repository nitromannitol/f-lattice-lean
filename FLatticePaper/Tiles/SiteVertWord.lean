import FLatticePaper.Tiles.CeilWords
import FLatticePaper.Tiles.SiteStrings

/-! Task 53, item 4 (the vertical word): the reversed complement of a ceiling word is a ceiling word of the complementary slope.

For a word `x` of length `l` with `k` letters `q` (`CeilWord x k l`), the word `(x.map swapLetter).reverse` has length `l` and
ceiling slope `(l − k)/l`: its prefix of length `j` has `j − k + qPrefix x (l − j)` letters `q`, and `l·Q − l < (l − j) k ≤ l·Q`
with `Q = qPrefix x (l − j)` transfers to the bounds for the complementary slope by a linear identity. This is the vertical cursor
`b_j = ⌈n j / d⌉` of the vertical word of `(n, d)` (with `x` the child word of slope `(d − n)/d`). -/

namespace FLatticePaper.Tiles.SiteVertWord

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.CeilWords

theorem count_q_map_swap (x : BinaryWord) : (x.map swapLetter).count Letter.q = x.count Letter.p := by
  induction x with
  | nil => rfl
  | cons l x ih =>
    cases l
    · simp [swapLetter, ih]
    · simp [swapLetter, ih]

theorem count_p_add_q (x : BinaryWord) : x.count Letter.p + x.count Letter.q = x.length := by
  induction x with
  | nil => rfl
  | cons l x ih =>
    cases l
    · simp [← ih]
      omega
    · simp [← ih]
      omega

/-- The `q`-count of the first `j` letters of the reversed complement. -/
theorem qPrefix_rev_comp (x : BinaryWord) (j : ℕ) (hj : j ≤ x.length) :
    qPrefix ((x.map swapLetter).reverse) j = (j : ℤ) - (x.count Letter.q : ℤ) + qPrefix x (x.length - j) := by
  unfold qPrefix
  set c := x.map swapLetter with hc
  have hclen : c.length = x.length := by simp [hc]
  have h1 : c.reverse.take j = (c.drop (c.length - j)).reverse := by
    have h := List.reverse_take (i := j) (l := c.reverse)
    rw [List.reverse_reverse, List.length_reverse] at h
    rw [← h, List.reverse_reverse]
  rw [h1, List.count_reverse]
  have h2 : c.drop (c.length - j) = (x.drop (x.length - j)).map swapLetter := by
    simp [hc]
  rw [h2, count_q_map_swap]
  have h3 := count_p_add_q (x.drop (x.length - j))
  have h4 : (x.drop (x.length - j)).length = j := by
    simp
    omega
  have h5 : x.count Letter.q = (x.take (x.length - j)).count Letter.q +
      (x.drop (x.length - j)).count Letter.q := by
    rw [← List.count_append, List.take_append_drop]
  omega

/-- **The reversed complement is a ceiling word.** If `x` is a ceiling word of slope `k/l` (length `l`), then
`(x.map swapLetter).reverse` is a ceiling word of slope `(l − k)/l`. -/
theorem ceil_rev_comp (x : BinaryWord) (k l : ℤ) (hx : CeilWord x k l) (hl : 1 ≤ l) :
    CeilWord ((x.map swapLetter).reverse) (l - k) l := by
  obtain ⟨hlen, hbd⟩ := hx
  have hK : (x.count Letter.q : ℤ) = k := by
    have h := ceil_total x k l ⟨hlen, hbd⟩ hl
    unfold qPrefix at h
    rw [List.take_length] at h
    exact_mod_cast h
  refine ⟨by simp [hlen], fun j hj => ?_⟩
  have hjle : j ≤ x.length := by omega
  rw [qPrefix_rev_comp x j hjle, hK]
  obtain ⟨h1, h2⟩ := hbd (x.length - j) (by rw [Nat.cast_sub hjle] at *; omega)
  have hc : ((x.length - j : ℕ) : ℤ) = l - j := by
    rw [Nat.cast_sub hjle, hlen]
  rw [hc] at h1 h2
  constructor
  · nlinarith
  · nlinarith

end FLatticePaper.Tiles.SiteVertWord
