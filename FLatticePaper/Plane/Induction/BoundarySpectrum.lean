import FLatticePaper.Farey.PeriodDeck

/-! # The boundary spectrum of the closed rectangle (grade level)

For a child `(n, d)` (both odd, `d ≥ n + 2`) with period `T` (even, `2(d + n) < T`), a site has grades `t` (with `t ≡ z₁ + z₂`) and `s`
(even). The closed rectangle is `EvenRect` (even `t`) or `OddRect` (odd `t`). A boundary site of the closed rectangle (with a
4-neighbour outside it) is, up to the deck translates `K = (d, n)` (shifts `s` by `−T`) and `V = (n − d, n + d)` (shifts `t` by `T`),
a native free H or free V point. These are the five arcs: `freeH` (bottom), `freeV` (left), `freeV + K` (right, up at `ε = −1`), and
`freeH + V` (top). The statements are pure linear arithmetic in the grades, proved by `omega`. -/

namespace FLatticePaper.BoundarySpectrum

/-- The even closed rectangle in grades `(t, s)`. -/
def EvenRect (n d T a b : ℤ) : Prop := 2 - T ≤ a ∧ a ≤ d + n - 2 ∧ 0 ≤ b ∧ b ≤ T + 2 * n

/-- The odd closed rectangle in grades `(t, s)`. -/
def OddRect (n d T a b : ℤ) : Prop := n - T ≤ a ∧ a ≤ d ∧ 2 - d + n ≤ b ∧ b ≤ T + d + n - 2

/-- The even boundary points of the H cut: `2 ≤ t ≤ L − 2`. -/
def HSpE (n d a : ℤ) : Prop := 2 ≤ a ∧ a ≤ d + n - 2

/-- The odd H cut: `n ≤ t ≤ d`. -/
def HSpO (n d a : ℤ) : Prop := n ≤ a ∧ a ≤ d

/-- The V cut (for even `s`): `0 ≤ s ≤ 2n` or `2 − d + n ≤ s ≤ L − 2`. -/
def VSp (n d b : ℤ) : Prop := (0 ≤ b ∧ b ≤ 2 * n) ∨ (2 - d + n ≤ b ∧ b ≤ d + n - 2)

/-- **The even boundary spectrum.** An even closed point with an outside 4-neighbour is free H, free V, free V + K, or free H + V.
Grades of the neighbours: left `(t − n, s − L)`, right `(t + n, s + L)`, down `(t + d, s − c)`, up `(t − d, s + c)` with `L = d + n`,
`c = d − n`. -/
theorem spectrum_even (n d T t s : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hnO : n % 2 = 1) (hdO : d % 2 = 1) (hT : 2 * (d + n) < T)
    (hTe : T % 2 = 0)
    (ht : t % 2 = 0) (hs : s % 2 = 0) (hE : EvenRect n d T t s)
    (hex : ¬ OddRect n d T (t - n) (s - (d + n)) ∨ ¬ OddRect n d T (t + n) (s + (d + n)) ∨
      ¬ OddRect n d T (t + d) (s - (d - n)) ∨ ¬ OddRect n d T (t - d) (s + (d - n))) :
    (HSpE n d t ∧ ¬ OddRect n d T (t + d) (s - (d - n))) ∨
    (VSp n d s ∧ ¬ OddRect n d T (t - n) (s - (d + n))) ∨
    (EvenRect n d T t (s - T) ∧ VSp n d (s - T) ∧ ¬ OddRect n d T (t - n) (s - T - (d + n))) ∨
    (EvenRect n d T (t + T) s ∧ HSpE n d (t + T) ∧ ¬ OddRect n d T (t + T + d) (s - (d - n))) := by
  unfold EvenRect OddRect HSpE VSp at *
  omega

/-- **The odd boundary spectrum.** The same statement for odd closed points (their neighbours are even). -/
theorem spectrum_odd (n d T t s : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hnO : n % 2 = 1) (hdO : d % 2 = 1) (hT : 2 * (d + n) < T)
    (hTe : T % 2 = 0)
    (ht : t % 2 = 1) (hs : s % 2 = 0) (hO : OddRect n d T t s)
    (hex : ¬ EvenRect n d T (t - n) (s - (d + n)) ∨ ¬ EvenRect n d T (t + n) (s + (d + n)) ∨
      ¬ EvenRect n d T (t + d) (s - (d - n)) ∨ ¬ EvenRect n d T (t - d) (s + (d - n))) :
    (HSpO n d t ∧ ¬ EvenRect n d T (t + d) (s - (d - n))) ∨
    (VSp n d s ∧ ¬ EvenRect n d T (t - n) (s - (d + n))) ∨
    (OddRect n d T t (s - T) ∧ VSp n d (s - T) ∧ ¬ EvenRect n d T (t - n) (s - T - (d + n))) ∨
    (OddRect n d T (t + T) s ∧ HSpO n d (t + T) ∧ ¬ EvenRect n d T (t + T + d) (s - (d - n))) := by
  unfold EvenRect OddRect HSpO VSp at *
  omega

end FLatticePaper.BoundarySpectrum
