import FLatticePaper.Plane.Induction.Q3Exit
import FLatticePaper.Plane.Induction.W1Constructor

/-! Task 46, step 1: the two named hypotheses of w3's exit lemma (`Q3Exit.lean`), discharged.

`ChildFrame.openRect` is the strict interior `StrictInterior` of `W1Constructor` (`openRect_iff_strictInterior`). The inputs of a
point of the open rectangle lie in the closed rectangle (`rectInputs`, `hRectInputs`), and a point of the closed rectangle outside
the open one lies on a boundary spectrum (`boundaryClosed`, `hBoundary`). The arithmetic is linear in the grades `t, s` and the
period `T`, with the parities of the child (`n, d` odd, `T` even) and of the grades (`t` has the parity of the site, `s` is even). -/

namespace FLatticePaper.W1Exit

open FLatticePaper FLatticePaper.W1 FLatticePaper.Induction

/-! ### Parities -/

theorem odd_of_coprime (n d : ℤ) (hc : IsCoprime n d) (he : (n + d) % 2 = 0) : n % 2 = 1 := by
  by_contra h
  have hn : n % 2 = 0 := by omega
  have hd : d % 2 = 0 := by omega
  obtain ⟨p, hp⟩ : ∃ p, n = 2 * p := ⟨n / 2, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q, d = 2 * q := ⟨d / 2, by omega⟩
  obtain ⟨a, b, hab⟩ := hc
  subst hp hq
  have h2 : 2 * (a * p + b * q) = 1 := by linarith
  have h3 : (2 * (a * p + b * q)) % 2 = 1 % 2 := by rw [h2]
  simp at h3

theorem parity_t (n d x y : ℤ) (hn : n % 2 = 1) (hd : d % 2 = 1) : (n * x - d * y) % 2 = (x + y) % 2 := by
  have h : (n * x - d * y) % 2 = ((n % 2) * (x % 2) - (d % 2) * (y % 2)) % 2 := by
    simp [Int.sub_emod, Int.mul_emod]
  rw [h, hn, hd]
  omega

theorem parity_s (d n x y : ℤ) (hL : (d + n) % 2 = 0) (hdn : (d - n) % 2 = 0) :
    ((d + n) * x + (d - n) * y) % 2 = 0 := by
  have h1 : ((d + n) * x) % 2 = 0 := by rw [Int.mul_emod, hL]; simp
  have h2 : ((d - n) * y) % 2 = 0 := by rw [Int.mul_emod, hdn]; simp
  rw [Int.add_emod, h1, h2]
  norm_num

theorem parity_T (n d : ℤ) (hn : n % 2 = 1) (hd : d % 2 = 1) : (d ^ 2 + 2 * d * n - n ^ 2) % 2 = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, d = 2 * a + 1 := ⟨d / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, n = 2 * b + 1 := ⟨n / 2, by omega⟩
  have : d ^ 2 + 2 * d * n - n ^ 2 = 2 * (2 * a ^ 2 + 4 * a + 4 * a * b - 2 * b ^ 2 + 1) := by
    subst ha hb
    ring
  rw [this]
  simp

/-! ### The grades of the inputs -/

theorem t_negE (n d x y : ℤ) : w1t n d (x - 1, y) = w1t n d (x, y) - n := by
  show n * (x - 1) - d * y = (n * x - d * y) - n
  ring

theorem s_negE (n d x y : ℤ) : w1s n d (x - 1, y) = w1s n d (x, y) - (d + n) := by
  show (d + n) * (x - 1) + (d - n) * y = ((d + n) * x + (d - n) * y) - (d + n)
  ring

theorem t_posE (n d x y : ℤ) : w1t n d (x + 1, y) = w1t n d (x, y) + n := by
  show n * (x + 1) - d * y = (n * x - d * y) + n
  ring

theorem s_posE (n d x y : ℤ) : w1s n d (x + 1, y) = w1s n d (x, y) + (d + n) := by
  show (d + n) * (x + 1) + (d - n) * y = ((d + n) * x + (d - n) * y) + (d + n)
  ring

theorem t_negO (n d x y : ℤ) : w1t n d (x, y - 1) = w1t n d (x, y) + d := by
  show n * x - d * (y - 1) = (n * x - d * y) + d
  ring

theorem s_negO (n d x y : ℤ) : w1s n d (x, y - 1) = w1s n d (x, y) - (d - n) := by
  show (d + n) * x + (d - n) * (y - 1) = ((d + n) * x + (d - n) * y) - (d - n)
  ring

theorem t_posO (n d x y : ℤ) : w1t n d (x, y + 1) = w1t n d (x, y) - d := by
  show n * x - d * (y + 1) = (n * x - d * y) - d
  ring

theorem s_posO (n d x y : ℤ) : w1s n d (x, y + 1) = w1s n d (x, y) + (d - n) := by
  show (d + n) * x + (d - n) * (y + 1) = ((d + n) * x + (d - n) * y) + (d - n)
  ring

/-! ### Linear arithmetic on the grades (atoms `t, s, T, n, d`) -/

/-- The input `x − 1` of an even centre (an odd site) lies in the closed odd rectangle. -/
theorem inNegEven (t s T n d : ℤ) (hn : n % 2 = 1) (hd : d % 2 = 1) (hT : T % 2 = 0) (hn1 : 1 ≤ n)
    (hnd : n + 2 ≤ d) (ht : t % 2 = 0) (hs : s % 2 = 0) (h1 : d + n - 2 - T < t) (h2 : t < 2)
    (h3 : 2 * n < s) (h4 : s < T) :
    n - T ≤ t - n ∧ t - n ≤ d ∧ 2 - d + n ≤ s - (d + n) ∧ s - (d + n) ≤ T + d + n - 2 := by
  omega

theorem inPosEven (t s T n d : ℤ) (hn : n % 2 = 1) (hd : d % 2 = 1) (hT : T % 2 = 0) (hn1 : 1 ≤ n)
    (hnd : n + 2 ≤ d) (ht : t % 2 = 0) (hs : s % 2 = 0) (h1 : d + n - 2 - T < t) (h2 : t < 2)
    (h3 : 2 * n < s) (h4 : s < T) :
    n - T ≤ t + n ∧ t + n ≤ d ∧ 2 - d + n ≤ s + (d + n) ∧ s + (d + n) ≤ T + d + n - 2 := by
  omega

/-- The inputs `y − 1`, `y + 1` of an odd centre (even sites) lie in the closed even rectangle. -/
theorem inNegOdd (t s T n d : ℤ) (hn : n % 2 = 1) (hd : d % 2 = 1) (hT : T % 2 = 0) (hn1 : 1 ≤ n)
    (hnd : n + 2 ≤ d) (ht : t % 2 = 1) (hs : s % 2 = 0) (h1 : d - T < t) (h2 : t < n)
    (h3 : d + n - 2 < s) (h4 : s < T + (2 - d + n)) :
    2 - T ≤ t + d ∧ t + d ≤ d + n - 2 ∧ 0 ≤ s - (d - n) ∧ s - (d - n) ≤ T + 2 * n := by
  omega

theorem inPosOdd (t s T n d : ℤ) (hn : n % 2 = 1) (hd : d % 2 = 1) (hT : T % 2 = 0) (hn1 : 1 ≤ n)
    (hnd : n + 2 ≤ d) (ht : t % 2 = 1) (hs : s % 2 = 0) (h1 : d - T < t) (h2 : t < n)
    (h3 : d + n - 2 < s) (h4 : s < T + (2 - d + n)) :
    2 - T ≤ t - d ∧ t - d ≤ d + n - 2 ∧ 0 ≤ s + (d - n) ∧ s + (d - n) ≤ T + 2 * n := by
  omega

/-! ### The boundary spectra (atoms) -/

theorem boundary_even (t s T n d : ℤ) (hT : T % 2 = 0) (ht : t % 2 = 0) (hs : s % 2 = 0)
    (hc : 2 - T ≤ t ∧ t ≤ d + n - 2 ∧ 0 ≤ s ∧ s ≤ T + 2 * n)
    (hno : ¬ (d + n - 2 - T < t ∧ t < 2 ∧ 2 * n < s ∧ s < T)) :
    ∃ k : ℤ, (k = -1 ∨ k = 0 ∨ k = 1) ∧
      ((((t + k * T) % 2 = 0 ∧ 2 ≤ t + k * T ∧ t + k * T ≤ d + n - 2) ∨
          ((t + k * T) % 2 = 1 ∧ n ≤ t + k * T ∧ t + k * T ≤ d)) ∨
        ((s + k * T) % 2 = 0 ∧ ((0 ≤ s + k * T ∧ s + k * T ≤ 2 * n) ∨
          (2 - d + n ≤ s + k * T ∧ s + k * T ≤ d + n - 2)))) := by
  by_cases h1 : t ≤ d + n - 2 - T
  · exact ⟨1, by norm_num, Or.inl (Or.inl (by omega))⟩
  by_cases h2 : 2 ≤ t
  · exact ⟨0, by norm_num, Or.inl (Or.inl (by omega))⟩
  by_cases h3 : s ≤ 2 * n
  · exact ⟨0, by norm_num, Or.inr (by omega)⟩
  have hsT : T ≤ s := by
    by_contra hlt
    exact hno ⟨by omega, by omega, by omega, by omega⟩
  exact ⟨-1, by norm_num, Or.inr (by omega)⟩

theorem boundary_odd (t s T n d : ℤ) (hT : T % 2 = 0) (ht : t % 2 = 1) (hs : s % 2 = 0)
    (hc : n - T ≤ t ∧ t ≤ d ∧ 2 - d + n ≤ s ∧ s ≤ T + d + n - 2)
    (hno : ¬ (d - T < t ∧ t < n ∧ d + n - 2 < s ∧ s < T + (2 - d + n))) :
    ∃ k : ℤ, (k = -1 ∨ k = 0 ∨ k = 1) ∧
      ((((t + k * T) % 2 = 0 ∧ 2 ≤ t + k * T ∧ t + k * T ≤ d + n - 2) ∨
          ((t + k * T) % 2 = 1 ∧ n ≤ t + k * T ∧ t + k * T ≤ d)) ∨
        ((s + k * T) % 2 = 0 ∧ ((0 ≤ s + k * T ∧ s + k * T ≤ 2 * n) ∨
          (2 - d + n ≤ s + k * T ∧ s + k * T ≤ d + n - 2)))) := by
  by_cases h1 : t ≤ d - T
  · exact ⟨1, by norm_num, Or.inl (Or.inr (by omega))⟩
  by_cases h2 : n ≤ t
  · exact ⟨0, by norm_num, Or.inl (Or.inr (by omega))⟩
  by_cases h3 : s ≤ d + n - 2
  · exact ⟨0, by norm_num, Or.inr (by omega)⟩
  have hsT : T + 2 - d + n ≤ s := by
    by_contra hlt
    exact hno ⟨by omega, by omega, by omega, by omega⟩
  exact ⟨-1, by norm_num, Or.inr (by omega)⟩

/-! ### Frame level -/

theorem child_parity (frame : ChildFrame) : frame.child.num % 2 = 1 ∧ frame.child.den % 2 = 1 := by
  have he : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hc : IsCoprime frame.child.num frame.child.den := frame.child_reduced
  have hn := odd_of_coprime _ _ hc he
  exact ⟨hn, by omega⟩

/-- The open parity rectangle of `ChildFrame` is the strict interior `StrictInterior`. -/
theorem openRect_iff (frame : ChildFrame) (z : Site) :
    frame.openRect z ↔ StrictInterior frame.child.num frame.child.den z := by
  unfold ChildFrame.openRect StrictInterior
  simp only [w1a, w1b, w1c, w1h, frame_periodDenominator_eq, frame_tGrade_eq, frame_sGrade_eq]
  split_ifs
  · constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **The inputs of the open rectangle lie in the closed polygon** (`hRectInputs` of `Q3Exit`). -/
theorem rectInputs (frame : ChildFrame) (z : Site) (hz : frame.openRect z) (i : Site)
    (hi : i = incomingNeg z ∨ i = incomingPos z) : i ∈ frame.closedPolygon := by
  obtain ⟨hn1, hd1⟩ := child_parity frame
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  have hn0 : 1 ≤ frame.child.num := by omega
  have hLev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hT : w1T frame.child.num frame.child.den % 2 = 0 := parity_T _ _ hn1 hd1
  have hdnev : (frame.child.den - frame.child.num) % 2 = 0 := by omega
  have hSI := (openRect_iff frame z).1 hz
  rw [closedPolygon_eq_closedRect]
  show closedRect frame.child.num frame.child.den i
  obtain ⟨x, y⟩ := z
  by_cases hE : EvenSite (x, y)
  · have hxy : (x + y) % 2 = 0 := hE
    have ht : w1t frame.child.num frame.child.den (x, y) % 2 = 0 := by
      show (frame.child.num * x - frame.child.den * y) % 2 = 0
      rw [parity_t _ _ x y hn1 hd1]
      omega
    have hs : w1s frame.child.num frame.child.den (x, y) % 2 = 0 :=
      parity_s _ _ x y (by omega) hdnev
    simp only [StrictInterior, w1a, w1b, w1c, w1h, hE, if_true, add_zero] at hSI
    obtain ⟨h1, h2, h3, h4⟩ := hSI
    rcases hi with rfl | rfl
    · have hI : incomingNeg (x, y) = (x - 1, y) := by unfold incomingNeg; rw [if_pos hE]
      rw [hI]
      have hnE : ¬ EvenSite (x - 1, y) := by
        show ¬ ((x - 1 + y) % 2 = 0)
        omega
      unfold closedRect
      rw [if_neg hnE, t_negE, s_negE]
      exact inNegEven _ _ _ _ _ hn1 hd1 hT hn0 hnd ht hs h1 h2 h3 h4
    · have hI : incomingPos (x, y) = (x + 1, y) := by unfold incomingPos; rw [if_pos hE]
      rw [hI]
      have hnE : ¬ EvenSite (x + 1, y) := by
        show ¬ ((x + 1 + y) % 2 = 0)
        omega
      unfold closedRect
      rw [if_neg hnE, t_posE, s_posE]
      exact inPosEven _ _ _ _ _ hn1 hd1 hT hn0 hnd ht hs h1 h2 h3 h4
  · have hxy : (x + y) % 2 = 1 := by
      have : ¬ ((x + y) % 2 = 0) := hE
      omega
    have ht : w1t frame.child.num frame.child.den (x, y) % 2 = 1 := by
      show (frame.child.num * x - frame.child.den * y) % 2 = 1
      rw [parity_t _ _ x y hn1 hd1]
      omega
    have hs : w1s frame.child.num frame.child.den (x, y) % 2 = 0 :=
      parity_s _ _ x y (by omega) hdnev
    simp only [StrictInterior, w1a, w1b, w1c, w1h, hE, if_false] at hSI
    obtain ⟨h1, h2, h3, h4⟩ := hSI
    rcases hi with rfl | rfl
    · have hI : incomingNeg (x, y) = (x, y - 1) := by unfold incomingNeg; rw [if_neg hE]
      rw [hI]
      have hnE : EvenSite (x, y - 1) := by
        show ((x + (y - 1)) % 2 = 0)
        omega
      unfold closedRect
      rw [if_pos hnE, t_negO, s_negO]
      exact inNegOdd _ _ _ _ _ hn1 hd1 hT hn0 hnd ht hs h1 h2 h3 h4
    · have hI : incomingPos (x, y) = (x, y + 1) := by unfold incomingPos; rw [if_neg hE]
      rw [hI]
      have hnE : EvenSite (x, y + 1) := by
        show ((x + (y + 1)) % 2 = 0)
        omega
      unfold closedRect
      rw [if_pos hnE, t_posO, s_posO]
      exact inPosOdd _ _ _ _ _ hn1 hd1 hT hn0 hnd ht hs h1 h2 h3 h4

/-- **A closed point outside the open rectangle lies on a boundary spectrum** (`hBoundary` of `Q3Exit`). -/
theorem boundaryClosed (frame : ChildFrame) (z : Site) (hz : z ∈ frame.closedPolygon)
    (hno : ¬ frame.openRect z) : frame.onBoundarySpectrum z := by
  obtain ⟨hn1, hd1⟩ := child_parity frame
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  have hLev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hT : w1T frame.child.num frame.child.den % 2 = 0 := parity_T _ _ hn1 hd1
  have hdnev : (frame.child.den - frame.child.num) % 2 = 0 := by omega
  have hSI : ¬ StrictInterior frame.child.num frame.child.den z := fun h => hno ((openRect_iff frame z).2 h)
  rw [closedPolygon_eq_closedRect] at hz
  have hz' : closedRect frame.child.num frame.child.den z := hz
  obtain ⟨x, y⟩ := z
  unfold ChildFrame.onBoundarySpectrum
  rw [frame_periodDenominator_eq]
  by_cases hE : EvenSite (x, y)
  · have hxy : (x + y) % 2 = 0 := hE
    have ht : w1t frame.child.num frame.child.den (x, y) % 2 = 0 := by
      show (frame.child.num * x - frame.child.den * y) % 2 = 0
      rw [parity_t _ _ x y hn1 hd1]
      omega
    have hs : w1s frame.child.num frame.child.den (x, y) % 2 = 0 := parity_s _ _ x y (by omega) hdnev
    unfold closedRect at hz'
    rw [if_pos hE] at hz'
    have hno' : ¬ (frame.child.den + frame.child.num - 2 - w1T frame.child.num frame.child.den <
        w1t frame.child.num frame.child.den (x, y) ∧ w1t frame.child.num frame.child.den (x, y) < 2 ∧
        2 * frame.child.num < w1s frame.child.num frame.child.den (x, y) ∧
        w1s frame.child.num frame.child.den (x, y) < w1T frame.child.num frame.child.den) := by
      intro h
      apply hSI
      simp only [StrictInterior, w1a, w1b, w1c, w1h, hE, if_true, add_zero]
      exact h
    obtain ⟨k, hk, hH⟩ := boundary_even _ _ _ _ _ hT ht hs hz' hno'
    refine ⟨k, hk, ?_⟩
    rcases hH with hH | hH
    · exact Or.inl hH
    · exact Or.inr hH
  · have hxy : (x + y) % 2 = 1 := by
      have : ¬ ((x + y) % 2 = 0) := hE
      omega
    have ht : w1t frame.child.num frame.child.den (x, y) % 2 = 1 := by
      show (frame.child.num * x - frame.child.den * y) % 2 = 1
      rw [parity_t _ _ x y hn1 hd1]
      omega
    have hs : w1s frame.child.num frame.child.den (x, y) % 2 = 0 := parity_s _ _ x y (by omega) hdnev
    unfold closedRect at hz'
    rw [if_neg hE] at hz'
    have hno' : ¬ (frame.child.den - w1T frame.child.num frame.child.den <
        w1t frame.child.num frame.child.den (x, y) ∧ w1t frame.child.num frame.child.den (x, y) < frame.child.num ∧
        frame.child.den + frame.child.num - 2 < w1s frame.child.num frame.child.den (x, y) ∧
        w1s frame.child.num frame.child.den (x, y) <
          w1T frame.child.num frame.child.den + (2 - frame.child.den + frame.child.num)) := by
      intro h
      apply hSI
      simp only [StrictInterior, w1a, w1b, w1c, w1h, hE, if_false]
      exact h
    obtain ⟨k, hk, hH⟩ := boundary_odd _ _ _ _ _ hT ht hs hz' hno'
    refine ⟨k, hk, ?_⟩
    rcases hH with hH | hH
    · exact Or.inl hH
    · exact Or.inr hH

/-- **The exit lemma, unconditional.** `Q3Exit.exit_centre_on_boundary_spectrum` with its two named hypotheses discharged. -/
theorem exit_centre_on_boundary_spectrum (frame : ChildFrame) (z i : Site) (hz : z ∈ frame.closedPolygon)
    (hi : i = incomingNeg z ∨ i = incomingPos z) (hout : i ∉ frame.closedPolygon) :
    frame.onBoundarySpectrum z :=
  ChildFrame.exit_centre_on_boundary_spectrum frame (fun z hz i hi => rectInputs frame z hz i hi)
    (fun z hz hr => boundaryClosed frame z hz hr) z i hz hi hout

end FLatticePaper.W1Exit
