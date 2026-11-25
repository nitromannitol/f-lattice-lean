import FLatticePaper.Plane.Induction.PureTrace
import FLatticePaper.Plane.Induction.VWindow
import FLatticePaper.Plane.Induction.RowMinus
import FLatticePaper.Plane.Induction.StandardField

/-! Task w3, B: the minus row at the pure conjugates `3^m` (the all-threes row).

For `C = frameAt (3^m)` (child `1/d`, `d = 2m+3`, odd parent `0/1`, period `L = d+1`, shifts `σ = (−2,0)`), the raw slip is
`D_−(z) = F(z) − F(z + (2,0))` on the reciprocal field `F`, and on the labelled cut `V'_i = (x,i)` the window of `s = (d+1)x + (d−1)i`
gives `x ≤ 0`, `x ≥ 2 − d`, `x = 0` for `i ∈ {0,1}`, `x ≤ −1` for `i ≥ 2`, and `x + i ≥ 1` for `i ≥ 1`. So
`D_−(V'_i) = 0, −1, −2` (`i = 0`, `i = 1`, `i ≥ 2`), which is the row `rowVal (−1) 1 L`. -/

namespace FLatticePaper.PureRow

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.Construction

/-- The window consequences for a V point `(x,i)` of the pure frame `1/d` (`s = (d+1)x + (d−1)i`). -/
theorem window_consequences (d x i : ℤ) (hd : 3 ≤ d) (hi0 : 0 ≤ i) (hiL : i ≤ d)
    (hw : ((x + i) % 2 = 0 → 0 ≤ (d + 1) * x + (d - 1) * i ∧ (d + 1) * x + (d - 1) * i ≤ 2) ∧
      ((x + i) % 2 = 1 → 3 - d ≤ (d + 1) * x + (d - 1) * i ∧ (d + 1) * x + (d - 1) * i ≤ d - 1)) :
    (2 - d ≤ x ∧ x ≤ 0) ∧ (i = 0 → x = 0) ∧ (i = 1 → x = 0) ∧ (2 ≤ i → x ≤ -1) ∧ (1 ≤ i → 1 ≤ x + i) := by
  have hlo : 3 - d ≤ (d + 1) * x + (d - 1) * i := by
    rcases (by omega : (x + i) % 2 = 0 ∨ (x + i) % 2 = 1) with h | h
    · have := (hw.1 h).1
      omega
    · exact (hw.2 h).1
  have hup : (d + 1) * x + (d - 1) * i ≤ d - 1 := by
    rcases (by omega : (x + i) % 2 = 0 ∨ (x + i) % 2 = 1) with h | h
    · have := (hw.1 h).2
      omega
    · exact (hw.2 h).2
  have hx0 : x ≤ 0 := by
    by_contra hc
    have h1 : (1 : ℤ) ≤ x := by omega
    nlinarith [mul_le_mul_of_nonneg_left h1 (show (0 : ℤ) ≤ d + 1 by omega),
      mul_nonneg (show (0 : ℤ) ≤ d - 1 by omega) hi0]
  have hx1 : 2 - d ≤ x := by
    by_contra hc
    have h1 : x ≤ 1 - d := by omega
    nlinarith [mul_le_mul_of_nonneg_left h1 (show (0 : ℤ) ≤ d + 1 by omega),
      mul_le_mul_of_nonneg_left hiL (show (0 : ℤ) ≤ d - 1 by omega)]
  have hi0x : i = 0 → x = 0 := by
    intro hi
    subst hi
    by_contra hc
    have h1 : x ≤ -1 := by omega
    nlinarith [mul_le_mul_of_nonneg_left h1 (show (0 : ℤ) ≤ d + 1 by omega)]
  have hi1x : i = 1 → x = 0 := by
    intro hi
    subst hi
    by_contra hc
    rcases (by omega : x = -1 ∨ x ≤ -2) with h | h
    · subst h
      have := (hw.1 (by norm_num)).1
      norm_num at this
      omega
    · nlinarith [mul_le_mul_of_nonneg_left (show x ≤ -2 by omega) (show (0 : ℤ) ≤ d + 1 by omega)]
  have hi2 : 2 ≤ i → x ≤ -1 := by
    intro hi
    by_contra hc
    have hx' : x = 0 := by omega
    subst hx'
    nlinarith
  have hpos : 1 ≤ i → 1 ≤ x + i := by
    intro hi
    by_contra hc
    have hu : x + i ≤ 0 := by omega
    rcases (by omega : (x + i) % 2 = 0 ∨ (x + i) % 2 = 1) with h | h
    · have := (hw.1 h).1
      nlinarith [mul_le_mul_of_nonneg_left hu (show (0 : ℤ) ≤ d + 1 by omega)]
    · have hu' : x + i ≤ -1 := by omega
      nlinarith [mul_le_mul_of_nonneg_left hu' (show (0 : ℤ) ≤ d + 1 by omega)]
  exact ⟨⟨hx1, hx0⟩, hi0x, hi1x, hi2, hpos⟩

/-- The stair-even tile contains `(x,i)` and `(x+2,i)` for the pure V points. -/
theorem mem_pure_tile (d x i : ℤ) (hi0 : 0 ≤ i) (hiL : i ≤ d) (hx1 : 2 - d ≤ x) (hx0 : x ≤ 0)
    (hi0x : i = 0 → x = 0) (hpos : 1 ≤ i → 1 ≤ x + i) :
    ((x, i) : Site) ∈ (BaseMask.stairEven.raw d).sites ∧ ((x + 2, i) : Site) ∈ (BaseMask.stairEven.raw d).sites := by
  constructor
  · rw [BaseMask.mem_stairEven_raw_iff]
    refine ⟨⟨by dsimp only; omega, by dsimp only; omega⟩, ⟨by dsimp only; omega, by dsimp only; omega⟩, ?_⟩
    by_cases hi : i = 0
    · left
      have hx := hi0x hi
      unfold BaseMask.StairEvenCorner
      left
      exact ⟨hx, hi⟩
    · right
      have := hpos (by omega)
      dsimp only
      constructor <;> omega
  · rw [BaseMask.mem_stairEven_raw_iff]
    refine ⟨⟨by dsimp only; omega, by dsimp only; omega⟩, ⟨by dsimp only; omega, by dsimp only; omega⟩, ?_⟩
    right
    dsimp only
    by_cases hi : i = 0
    · have := hi0x hi
      constructor <;> omega
    · have := hpos (by omega)
      constructor <;> omega

/-- The corner indicators of the pure V points: only the origin is a corner among `(x,i)` and `(x+2,i)` is never one. -/
theorem value_pure (d x i : ℤ) (hiL : i ≤ d) (hx0 : x ≤ 0) (hi0x : i = 0 → x = 0) :
    BaseMask.stairEvenValue d (x, i) - BaseMask.stairEvenValue d (x + 2, i) =
      min (x - 1) 0 - min (x + 1) 0 + (if x = 0 ∧ i = 0 then 1 else 0) := by
  have hc2 : ¬ BaseMask.StairEvenCorner d (x + 2, i) := by
    unfold BaseMask.StairEvenCorner
    rintro (h | h)
    · have := hi0x h.2
      simp only at h
      omega
    · simp only at h
      omega
  unfold BaseMask.stairEvenValue
  rw [if_neg hc2]
  by_cases h0 : x = 0 ∧ i = 0
  · have hc1 : BaseMask.StairEvenCorner d (x, i) := by
      unfold BaseMask.StairEvenCorner
      left
      exact h0
    rw [if_pos hc1, if_pos h0]
    simp only [h0.1]
    norm_num
  · have hc1 : ¬ BaseMask.StairEvenCorner d (x, i) := by
      unfold BaseMask.StairEvenCorner
      rintro (h | h)
      · exact h0 h
      · simp only at h
        omega
    rw [if_neg hc1, if_neg h0]
    have e : x + 2 - 1 = x + 1 := by ring
    simp only [e]
    ring

/-- The odd parent of `3^m` is `0/1`. -/
theorem odd_threes (m : ℕ) : (frameAt (List.replicate m Digit.three)).parents.odd.num = 0 ∧
    (frameAt (List.replicate m Digit.three)).parents.odd.den = 1 := by
  have hN := frameAt_threes_parentSlope m (1, 0)
  have hD := frameAt_threes_parentSlope m (0, 1)
  unfold ChildFrame.parentSlope at hN hD
  constructor
  · have := hN
      
    simp at this
    exact this
  · have := hD
    simp at this
    linarith

/-- The value of the raw slip on the pure V points: `D_−(x,i) = min(x−1,0) − min(x+1,0) + [origin]`. -/
theorem dq_threes_eq (m : ℕ) (x i : ℤ) (hi0 : 0 ≤ i) (hiL : i ≤ 2 * (m : ℤ) + 3) (hx1 : 2 - (2 * (m : ℤ) + 3) ≤ x)
    (hx0 : x ≤ 0) (hi0x : i = 0 → x = 0) (hpos : 1 ≤ i → 1 ≤ x + i) :
    EndpointDeck.Dq (frameAt (List.replicate m Digit.three)) (standardField (List.replicate m Digit.three)) (-1) (x, i) =
      min (x - 1) 0 - min (x + 1) 0 + (if x = 0 ∧ i = 0 then 1 else 0) := by
  obtain ⟨m1, m2⟩ := mem_pure_tile (2 * (m : ℤ) + 3) x i hi0 hiL hx1 hx0 hi0x hpos
  unfold EndpointDeck.Dq
  rw [standardField_threes, frameAt_threes_shortShift]
  have e : ((x, i) : Site) + (-1 : ℤ) • ((-2 : ℤ), (0 : ℤ)) = (x + 2, i) := by
    ext <;> simp
  rw [e, PureTrace.field_at_tile m (x, i) m1, PureTrace.field_at_tile m (x + 2, i) m2]
  exact value_pure (2 * (m : ℤ) + 3) x i hiL hx0 hi0x

/-- **The all-threes row.** The minus row of the pure conjugate `3^m`, on its labelled cut. -/
theorem rawRow_threes (m : ℕ) (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (List.replicate m Digit.three)) →
      base r ∈ (frameAt (List.replicate m Digit.three)).freeV ∧ (base r).2 = r) :
    StepTwoC.RawRow
      (fun i => EndpointDeck.Dq (frameAt (List.replicate m Digit.three)) (standardField (List.replicate m Digit.three)) (-1)
        (FreeEnum.vAt (frameAt (List.replicate m Digit.three)) base i)) (-1)
      ((frameAt (List.replicate m Digit.three)).parents.odd.den + (frameAt (List.replicate m Digit.three)).parents.odd.num)
      (FreeEnum.period (frameAt (List.replicate m Digit.three))) := by
  obtain ⟨hn, hd⟩ := odd_threes m
  have hchild := frameAt_threes_child m
  have hnum : (frameAt (List.replicate m Digit.three)).child.num = 1 := by rw [hchild]
  have hden : (frameAt (List.replicate m Digit.three)).child.den = 2 * (m : ℤ) + 3 := by rw [hchild]
  have hper : FreeEnum.period (frameAt (List.replicate m Digit.three)) = 2 * (m : ℤ) + 4 := by
    unfold FreeEnum.period
    rw [hnum, hden]
    ring
  have hr : (frameAt (List.replicate m Digit.three)).parents.odd.den +
      (frameAt (List.replicate m Digit.three)).parents.odd.num = 1 := by
    omega
  unfold StepTwoC.RawRow
  rw [hr, hper]
  intro i hi0 hiL
  dsimp only
  rw [RowMinus.rowVal_neg]
  set p := FreeEnum.vAt (frameAt (List.replicate m Digit.three)) base i with hp_def
  have hpi : p.2 = i := FreeEnum.vAt_snd _ base (fun r h0 h1 => (hbase r h0 h1).2) i
  have hp : p = (p.1, i) := Prod.ext rfl hpi
  have hw := VWindow.vAt_window (frameAt (List.replicate m Digit.three)) base
    (fun r h0 h1 => hbase r h0 h1) i
  rw [← hp_def] at hw
  rw [hp] at hw
  unfold ChildFrame.sGrade at hw
  rw [hnum, hden] at hw
  have hs : ((p.1 + i) % 2 = 0 → 0 ≤ (2 * (m : ℤ) + 3 + 1) * p.1 + (2 * (m : ℤ) + 3 - 1) * i ∧
      (2 * (m : ℤ) + 3 + 1) * p.1 + (2 * (m : ℤ) + 3 - 1) * i ≤ 2) ∧
      ((p.1 + i) % 2 = 1 → 3 - (2 * (m : ℤ) + 3) ≤ (2 * (m : ℤ) + 3 + 1) * p.1 + (2 * (m : ℤ) + 3 - 1) * i ∧
      (2 * (m : ℤ) + 3 + 1) * p.1 + (2 * (m : ℤ) + 3 - 1) * i ≤ 2 * (m : ℤ) + 3 - 1) := by
    constructor
    · intro h
      have h' : EvenSite (p.1, i) := h
      obtain ⟨h1, h2⟩ := hw.1 h'
      constructor <;> linarith
    · intro h
      have h' : ¬ EvenSite (p.1, i) := fun e => by
        have : (p.1 + i) % 2 = 0 := e
        omega
      obtain ⟨h1, h2⟩ := hw.2 h'
      constructor <;> linarith
  obtain ⟨⟨hx1, hx0⟩, hi0x, hi1x, hi2, hpos⟩ :=
    window_consequences (2 * (m : ℤ) + 3) p.1 i (by omega) hi0 (by omega) hs
  rw [hp, dq_threes_eq m p.1 i hi0 (by omega) hx1 hx0 hi0x hpos]
  rcases (by omega : i = 0 ∨ i = 1 ∨ 2 ≤ i) with h | h | h
  · have hx : p.1 = 0 := hi0x h
    rw [h, hx]
    norm_num
  · have hx : p.1 = 0 := hi1x h
    rw [h, hx]
    norm_num
  · have hx : p.1 ≤ -1 := hi2 h
    rw [min_eq_left (by omega : p.1 - 1 ≤ 0), min_eq_left (by omega : p.1 + 1 ≤ 0),
      if_neg (by omega : ¬(p.1 = 0 ∧ i = 0)), if_neg (by omega : ¬ i = 0), if_neg (by omega : ¬ i ≤ 1)]
    ring

/-- The all-threes row at an arbitrary all-threes word `X` (the conjugate of a proper word with no letter other than `3`). -/
theorem rowThrees_of_conj (X : Word) (hX : ∀ x ∈ X, x = Digit.three) (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt X) →
      base r ∈ (frameAt X).freeV ∧ (base r).2 = r) :
    StepTwoC.RawRow (fun i => EndpointDeck.Dq (frameAt X) (standardField X) (-1) (FreeEnum.vAt (frameAt X) base i)) (-1)
      ((frameAt X).parents.odd.den + (frameAt X).parents.odd.num) (FreeEnum.period (frameAt X)) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, X = List.replicate m Digit.three := ⟨X.length, all_three_eq_replicate hX⟩
  subst hm
  exact rawRow_threes m base hbase

end FLatticePaper.PureRow
