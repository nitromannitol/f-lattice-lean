import FLatticePaper.Plane.Induction.W1Constructor
import FLatticePaper.Plane.Induction.EPolicyLap
import FLatticePaper.Plane.Induction.W1OffCollar

/-! # The W1 forcing at the pure-threes children (task 72, W1 base; lead's option (a))

For the child `1/d`, `d = 2k+3`, the reciprocal field `reciprocalField k` (the standard field of `3^k`). Its strict interior
`StrictInterior 1 d` (the W1 grades with `n = 1`, `T = d² + 2d − 1`) is the hexagon
`1 ≤ y ≤ d`, `3 − d ≤ x ≤ d − 1`, `2 ≤ x + y ≤ d + 1` (`strictInterior_hexagon`). The proof uses the identities
`T·y = s − (d+1)t` and `T·x = (d−1)t + d·s` with `t = x − dy`, `s = (d+1)x + (d−1)y`.
-/

namespace FLatticePaper.W1Reciprocal


open FLatticePaper FLatticePaper.W1

/-- Even strict-interior points lie in the hexagon (forward direction). -/
theorem hex_even_fwd {d x y : ℤ} (hd : 3 ≤ d) (hdo : d % 2 = 1) (hpar : (x + y) % 2 = 0)
    (h1 : d - 1 - (d ^ 2 + 2 * d - 1) < x - d * y) (h2 : x - d * y < 2)
    (h3 : 2 < (d + 1) * x + (d - 1) * y) (h4 : (d + 1) * x + (d - 1) * y < d ^ 2 + 2 * d - 1) :
    1 ≤ y ∧ y ≤ d ∧ 3 - d ≤ x ∧ x ≤ d - 1 ∧ 2 ≤ x + y ∧ x + y ≤ d + 1 := by
  have hT : (d ^ 2 + 2 * d - 1) * y = ((d + 1) * x + (d - 1) * y) - (d + 1) * (x - d * y) := by ring
  have hA : x - d * y ≤ 1 := by linarith
  have hB : 3 ≤ (d + 1) * x + (d - 1) * y := by linarith
  have hC : (d + 1) * x + (d - 1) * y ≤ d ^ 2 + 2 * d - 2 := by linarith
  have hD : d - (d ^ 2 + 2 * d - 1) ≤ x - d * y := by linarith
  have hd1 : (0 : ℤ) ≤ d + 1 := by linarith
  -- y ≥ 1
  have hy1 : 1 ≤ y := by
    by_contra hcon
    rcases (show y = 0 ∨ y ≤ -1 by omega) with hy | hy
    · subst hy
      have hx1 : x ≤ 1 := by linarith
      have hx2 : 1 ≤ x := by
        by_contra hc
        have : x ≤ 0 := by omega
        nlinarith
      have hx : x = 1 := by omega
      subst hx
      norm_num at hpar
    · have hT0 : (0 : ℤ) ≤ d ^ 2 + 2 * d - 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hy hT0, mul_le_mul_of_nonneg_left hA hd1]
  -- y ≤ d
  have hyd : y ≤ d := by
    by_contra hcon
    have hy2 : d + 1 ≤ y := by omega
    rcases (show y = d + 1 ∨ d + 2 ≤ y by omega) with hy | hy
    · subst hy
      have hx1 : x ≤ 1 := by nlinarith
      have hx2 : 1 ≤ x := by nlinarith
      have hx : x = 1 := by omega
      subst hx
      have : (d + 1) % 2 = 0 := by omega
      omega
    · have hT0 : (0 : ℤ) ≤ d ^ 2 + 2 * d - 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hy hT0, mul_le_mul_of_nonneg_left hD hd1]
  -- x ≥ 3 - d
  have hxlo : 3 - d ≤ x := by
    by_contra hc
    have hc' : x ≤ 2 - d := by omega
    nlinarith [mul_le_mul_of_nonneg_left hc' hd1]
  -- x ≤ d - 1
  have hxhi : x ≤ d - 1 := by
    by_contra hc
    have hc' : d ≤ x := by omega
    nlinarith [mul_le_mul_of_nonneg_left hc' hd1]
  -- 2 ≤ x + y
  have hsum2 : 2 ≤ x + y := by
    by_contra hc
    have hc' : x + y ≤ 0 := by omega
    nlinarith [mul_le_mul_of_nonneg_left hc' hd1]
  -- x + y ≤ d + 1
  have hsumhi : x + y ≤ d + 1 := by
    by_contra hc
    have hc' : d + 2 ≤ x + y := by omega
    have hc'' : d + 3 ≤ x + y := by omega
    nlinarith [mul_le_mul_of_nonneg_left hc'' hd1]
  exact ⟨hy1, hyd, hxlo, hxhi, hsum2, hsumhi⟩


/-- Odd strict-interior points lie in the hexagon. -/
theorem hex_odd_fwd {d x y : ℤ} (hd : 3 ≤ d) (hdo : d % 2 = 1) (hpar : (x + y) % 2 = 1)
    (h1 : d - (d ^ 2 + 2 * d - 1) < x - d * y) (h2 : x - d * y < 1)
    (h3 : d - 1 < (d + 1) * x + (d - 1) * y) (h4 : (d + 1) * x + (d - 1) * y < d ^ 2 + 2 * d - 1 + 3 - d) :
    1 ≤ y ∧ y ≤ d ∧ 3 - d ≤ x ∧ x ≤ d - 1 ∧ 2 ≤ x + y ∧ x + y ≤ d + 1 := by
  have hT : (d ^ 2 + 2 * d - 1) * y = ((d + 1) * x + (d - 1) * y) - (d + 1) * (x - d * y) := by ring
  have hA : x - d * y ≤ 0 := by linarith
  have hB : d ≤ (d + 1) * x + (d - 1) * y := by linarith
  have hC : (d + 1) * x + (d - 1) * y ≤ d ^ 2 + 2 * d + 2 - d := by linarith
  have hD : d - (d ^ 2 + 2 * d - 1) + 1 ≤ x - d * y := by linarith
  have hd1 : (0 : ℤ) ≤ d + 1 := by linarith
  have hT0 : (0 : ℤ) ≤ d ^ 2 + 2 * d - 1 := by nlinarith
  have hy1 : 1 ≤ y := by
    by_contra hcon
    have hy0 : y ≤ 0 := by omega
    nlinarith [mul_le_mul_of_nonneg_left hy0 hT0, mul_le_mul_of_nonneg_left hA hd1]
  have hyd : y ≤ d := by
    by_contra hcon
    have hy2 : d + 1 ≤ y := by omega
    nlinarith [mul_le_mul_of_nonneg_left hy2 hT0, mul_le_mul_of_nonneg_left hD hd1]
  have hxlo : 3 - d ≤ x := by
    by_contra hc
    have hc' : x ≤ 2 - d := by omega
    have hyd' : (d - 1) * y ≤ (d - 1) * d := mul_le_mul_of_nonneg_left hyd (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hc' hd1]
  have hxhi : x ≤ d - 1 := by
    by_contra hc
    have hc' : d ≤ x := by omega
    nlinarith [mul_le_mul_of_nonneg_left hc' hd1]
  have hsum2 : 2 ≤ x + y := by
    by_contra hc
    have hc' : x + y ≤ 1 := by omega
    nlinarith [mul_le_mul_of_nonneg_left hc' hd1]
  have hsumhi : x + y ≤ d + 1 := by
    by_contra hc
    have hc' : d + 2 ≤ x + y := by omega
    nlinarith [mul_le_mul_of_nonneg_left hc' hd1]
  exact ⟨hy1, hyd, hxlo, hxhi, hsum2, hsumhi⟩

/-- The hexagon gives the even strict-interior inequalities. -/
theorem hex_even_bwd {d x y : ℤ} (hd : 3 ≤ d) (hdo : d % 2 = 1) (hpar : (x + y) % 2 = 0)
    (hy1 : 1 ≤ y) (hyd : y ≤ d) (hxlo : 3 - d ≤ x) (hxhi : x ≤ d - 1) (hs2 : 2 ≤ x + y) (hss : x + y ≤ d + 1) :
    d - 1 - (d ^ 2 + 2 * d - 1) < x - d * y ∧ x - d * y < 2 ∧
      2 < (d + 1) * x + (d - 1) * y ∧ (d + 1) * x + (d - 1) * y < d ^ 2 + 2 * d - 1 := by
  have hd1 : (0 : ℤ) ≤ d + 1 := by linarith
  have hdy : d * 1 ≤ d * y := mul_le_mul_of_nonneg_left hy1 (by linarith)
  have hdyd : d * y ≤ d * d := mul_le_mul_of_nonneg_left hyd (by linarith)
  refine ⟨by nlinarith, by nlinarith, ?_, ?_⟩
  · rcases (show x + y = 2 ∨ 3 ≤ x + y by omega) with h | h
    · have hx : x = 2 - y := by omega
      have hyd' : y ≤ d - 1 := by
        by_contra hc
        have : y = d := by omega
        subst this
        omega
      nlinarith [mul_le_mul_of_nonneg_left hyd' hd1]
    · nlinarith [mul_le_mul_of_nonneg_left h hd1]
  · rcases (show y = 1 ∨ 2 ≤ y by omega) with h | h
    · subst h
      nlinarith [mul_le_mul_of_nonneg_left hxhi hd1]
    · nlinarith [mul_le_mul_of_nonneg_left hss hd1, mul_le_mul_of_nonneg_left hxhi hd1]

/-- The hexagon gives the odd strict-interior inequalities. -/
theorem hex_odd_bwd {d x y : ℤ} (hd : 3 ≤ d) (hdo : d % 2 = 1) (hpar : (x + y) % 2 = 1)
    (hy1 : 1 ≤ y) (hyd : y ≤ d) (hxlo : 3 - d ≤ x) (hxhi : x ≤ d - 1) (hs2 : 2 ≤ x + y) (hss : x + y ≤ d + 1) :
    d - (d ^ 2 + 2 * d - 1) < x - d * y ∧ x - d * y < 1 ∧
      d - 1 < (d + 1) * x + (d - 1) * y ∧ (d + 1) * x + (d - 1) * y < d ^ 2 + 2 * d - 1 + 3 - d := by
  have hd1 : (0 : ℤ) ≤ d + 1 := by linarith
  have hdy : d * 1 ≤ d * y := mul_le_mul_of_nonneg_left hy1 (by linarith)
  have hdyd : d * y ≤ d * d := mul_le_mul_of_nonneg_left hyd (by linarith)
  have hss' : x + y ≤ d := by omega
  have hs3 : 3 ≤ x + y := by omega
  refine ⟨by nlinarith, by nlinarith, by nlinarith [mul_le_mul_of_nonneg_left hs3 hd1], ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hss' hd1]

/-- The strict interior of the child `1/d` (`n = 1`, `d` odd, `d ≥ 3`) is the hexagon. -/
theorem strictInterior_hexagon {d : ℤ} (hd : 3 ≤ d) (hdo : d % 2 = 1) (x y : ℤ) :
    StrictInterior 1 d (x, y) ↔
      (1 ≤ y ∧ y ≤ d ∧ 3 - d ≤ x ∧ x ≤ d - 1 ∧ 2 ≤ x + y ∧ x + y ≤ d + 1) := by
  unfold StrictInterior w1b w1T w1t w1a w1s w1h w1c
  simp only [EvenSite]
  by_cases hpar : (x + y) % 2 = 0
  · simp only [hpar, if_true]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      norm_num at h1 h2 h3 h4
      exact hex_even_fwd hd hdo hpar (by linarith) (by linarith) (by linarith) (by linarith)
    · rintro ⟨hy1, hyd, hxlo, hxhi, hs2, hss⟩
      have := hex_even_bwd hd hdo hpar hy1 hyd hxlo hxhi hs2 hss
      norm_num
      exact ⟨by linarith [this.1], by linarith [this.2.1], by linarith [this.2.2.1], by linarith [this.2.2.2]⟩
  · have hpar1 : (x + y) % 2 = 1 := by omega
    simp only [hpar, if_false]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      norm_num at h1 h2 h3 h4
      exact hex_odd_fwd hd hdo hpar1 (by linarith) (by linarith) (by linarith) (by linarith)
    · rintro ⟨hy1, hyd, hxlo, hxhi, hs2, hss⟩
      have := hex_odd_bwd hd hdo hpar1 hy1 hyd hxlo hxhi hs2 hss
      norm_num
      exact ⟨by linarith [this.1], by linarith [this.2.1], by linarith [this.2.2.1], by linarith [this.2.2.2]⟩



/-! ## The forcing induction (lead option (a)): the strict-interior whites of the pure-threes child are forced inside the strict interior. -/

open FLatticePaper.Induction FLatticePaper.EPolicy FLatticePaper.PureRank FLatticePaper.AndOrRank

/-- The inside target of the forced arrow: west for `x ≤ 0`, east for `x ≥ 2`. -/
def wInside (c : Site) : Site := if c.1 ≤ 0 then (c.1 - 1, c.2) else (c.1 + 1, c.2)

theorem wInside_neg {c : Site} (he : EvenSite c) (h : c.1 ≤ 0) : wInside c = incomingNeg c := by
  unfold wInside incomingNeg
  simp [he, h]

theorem wInside_pos {c : Site} (he : EvenSite c) (h : ¬ c.1 ≤ 0) : wInside c = incomingPos c := by
  unfold wInside incomingPos
  simp [he, h]

theorem si_of_hex (k : ℕ) {x y : ℤ} (h1 : 1 ≤ y) (h2 : y ≤ 2 * (k : ℤ) + 3)
    (h3 : 3 - (2 * (k : ℤ) + 3) ≤ x) (h4 : x ≤ 2 * (k : ℤ) + 3 - 1) (h5 : 2 ≤ x + y)
    (h6 : x + y ≤ 2 * (k : ℤ) + 3 + 1) : StrictInterior 1 (2 * (k : ℤ) + 3) (x, y) :=
  (strictInterior_hexagon (d := 2 * (k : ℤ) + 3) (by omega) (by omega) x y).2 ⟨h1, h2, h3, h4, h5, h6⟩

theorem nativeP_of_si {k : ℕ} {x y : ℤ} (h : StrictInterior 1 (2 * (k : ℤ) + 3) (x, y)) :
    NativeP (2 * (k : ℤ) + 3) (x, y) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    (strictInterior_hexagon (d := 2 * (k : ℤ) + 3) (by omega) (by omega) x y).1 h
  unfold NativeP
  refine Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega

theorem lap_si {k : ℕ} {x y : ℤ} (h : StrictInterior 1 (2 * (k : ℤ) + 3) (x, y)) :
    ((x + y) % 2 ≠ 0 → laplacian (reciprocalField k) (x, y) = -1) ∧
    ((x + y) % 2 = 0 → x = 1 → laplacian (reciprocalField k) (x, y) = -1) ∧
    ((x + y) % 2 = 0 → x ≠ 1 → laplacian (reciprocalField k) (x, y) = 0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    (strictInterior_hexagon (d := 2 * (k : ℤ) + 3) (by omega) (by omega) x y).1 h
  have hN := laplacian_reciprocal_native k (nativeP_of_si h)
  refine ⟨fun hp => ?_, fun hp hx => ?_, fun hp hx => ?_⟩
  · have he : ¬ EvenSite (x, y) := hp
    rw [hN, if_neg he]
    split_ifs with hc
    · rfl
    · exact (hc ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩).elim
  · have he : EvenSite (x, y) := hp
    rw [hN, if_pos he]
    simp [hx]
  · have he : EvenSite (x, y) := hp
    rw [hN, if_pos he]
    simp [hx]

theorem white_even {k : ℕ} {x y : ℤ} (h : StrictInterior 1 (2 * (k : ℤ) + 3) (x, y))
    (hw : laplacian (reciprocalField k) (x, y) = 0) : (x + y) % 2 = 0 := by
  by_contra hp
  rw [(lap_si h).1 hp] at hw
  norm_num at hw

/-- The one-square step: the white centre `z = (x, y)` of the square `squareCorners a b` is forced out of it, when its other
corners are black or whites with a smaller measure whose arrow points into the square. -/
theorem forced_of_square (k : ℕ) (m : ℕ)
    (ih : ∀ m' < m, ∀ c : Site, (c.1 - 1).natAbs = m' → StrictInterior 1 (2 * (k : ℤ) + 3) c →
      laplacian (reciprocalField k) c = 0 →
      ForcedEdgeIn (reciprocalField k) (StrictInterior 1 (2 * (k : ℤ) + 3)) (fun _ _ => False) c (wInside c))
    {a b x y : ℤ} (hz : (x, y) ∈ squareCorners a b)
    (hw : laplacian (reciprocalField k) (x, y) = 0)
    (hR : ∀ c' ∈ squareCorners a b, StrictInterior 1 (2 * (k : ℤ) + 3) c')
    (hout : wInside (x, y) ∉ squareCorners a b)
    (hcorner : ∀ c' ∈ squareCorners a b, c' ≠ (x, y) → laplacian (reciprocalField k) c' = -1 ∨
      (laplacian (reciprocalField k) c' = 0 ∧ wInside c' ∈ squareCorners a b ∧ (c'.1 - 1).natAbs < m)) :
    ForcedEdgeIn (reciprocalField k) (StrictInterior 1 (2 * (k : ℤ) + 3)) (fun _ _ => False) (x, y) (wInside (x, y)) := by
  have hS : StrictInterior 1 (2 * (k : ℤ) + 3) (x, y) := hR _ hz
  have hpar : (x + y) % 2 = 0 := white_even hS hw
  have ho : wInside (x, y) = incomingNeg (x, y) ∨ wInside (x, y) = incomingPos (x, y) := by
    by_cases hs : x ≤ 0
    · exact Or.inl (wInside_neg (show EvenSite (x, y) from hpar) hs)
    · exact Or.inr (wInside_pos (show EvenSite (x, y) from hpar) hs)
  refine ForcedEdgeIn.unit wInside hR hz hw ho hout ?_ ?_
  · intro c' hc' hne
    rcases hcorner c' hc' hne with h | ⟨h0, hmem, _⟩
    · exact Or.inl h
    · refine Or.inr ⟨h0, hmem, ?_⟩
      obtain ⟨p, q⟩ := c'
      have hpar' : (p + q) % 2 = 0 := white_even (hR _ hc') h0
      by_cases hp : p ≤ 0
      · exact Or.inl (wInside_neg (show EvenSite (p, q) from hpar') hp)
      · exact Or.inr (wInside_pos (show EvenSite (p, q) from hpar') hp)
  · intro c' hc' hne h0
    rcases hcorner c' hc' hne with h | ⟨h0', hmem, hlt⟩
    · rw [h] at h0
      norm_num at h0
    · exact ih _ hlt c' rfl (hR c' hc') h0'


/-- The forced arrow of every white strict-interior site (strong induction on `|x − 1|`). -/
theorem forced_claim (k : ℕ) (m : ℕ) : ∀ c : Site, (c.1 - 1).natAbs = m →
    StrictInterior 1 (2 * (k : ℤ) + 3) c → laplacian (reciprocalField k) c = 0 →
    ForcedEdgeIn (reciprocalField k) (StrictInterior 1 (2 * (k : ℤ) + 3)) (fun _ _ => False) c (wInside c) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rintro ⟨x, y⟩ hm hS hw
  have hpar : (x + y) % 2 = 0 := white_even hS hw
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    (strictInterior_hexagon (d := 2 * (k : ℤ) + 3) (by omega) (by omega) x y).1 hS
  rcases (show x ≤ 0 ∨ 2 ≤ x by
    have hx1 : x ≠ 1 := fun hx => by rw [(lap_si hS).2.1 hpar hx] at hw; norm_num at hw
    omega) with hx | hx
  · by_cases hy : y ≤ 2 * (k : ℤ) + 3 - 1
    · -- the square at (x, y): corners (x+1,y), (x,y+1) black, (x+1,y+1) even
      have hzc : (x, y) ∈ squareCorners (x) (y) := by
        simp [squareCorners]
      refine forced_of_square k m ih (a := x) (b := y) hzc hw ?_ ?_ ?_
      · intro c' hc'
        simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
        rcases hc' with rfl | rfl | rfl | rfl <;>
          exact si_of_hex k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      · unfold wInside
        dsimp only
        rw [if_pos hx]
        simp [squareCorners]
        omega
      · intro c' hc' hne
        simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
        rcases hc' with rfl | rfl | rfl | rfl
        · exact absurd rfl hne
        · have hS1 : StrictInterior 1 (2 * (k : ℤ) + 3) (x + 1, y) :=
            si_of_hex k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          exact Or.inl ((lap_si hS1).1 (by omega))
        · have hS2 : StrictInterior 1 (2 * (k : ℤ) + 3) (x, y + 1) :=
            si_of_hex k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          exact Or.inl ((lap_si hS2).1 (by omega))
        · have hS3 : StrictInterior 1 (2 * (k : ℤ) + 3) (x + 1, y + 1) :=
            si_of_hex k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          by_cases hx0 : x = 0
          · exact Or.inl ((lap_si hS3).2.1 (by omega) (by omega))
          · refine Or.inr ⟨(lap_si hS3).2.2 (by omega) (by omega), ?_, ?_⟩
            · have hw' : wInside (x + 1, y + 1) = (x, y + 1) := by
                unfold wInside
                dsimp only
                rw [if_pos (show x + 1 ≤ 0 by omega)]
                congr 1
                omega
              rw [hw']
              simp [squareCorners]
            · rw [← hm]
              dsimp only
              omega
    · -- the square at (x, y-1): corners (x,y-1), (x+1,y) black, (x+1,y-1) even
      have hzc : (x, y) ∈ squareCorners (x) (y - 1) := by
        simp [squareCorners]
      refine forced_of_square k m ih (a := x) (b := y - 1) hzc hw ?_ ?_ ?_
      · intro c' hc'
        simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
        rcases hc' with rfl | rfl | rfl | rfl <;>
          exact si_of_hex k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      · unfold wInside
        dsimp only
        rw [if_pos hx]
        simp [squareCorners]
        omega
      · intro c' hc' hne
        simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
        rcases hc' with rfl | rfl | rfl | rfl <;> try simp only [sub_add_cancel] at hne ⊢
        · have hS1 : StrictInterior 1 (2 * (k : ℤ) + 3) (x, y - 1) :=
            si_of_hex k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          exact Or.inl ((lap_si hS1).1 (by omega))
        · have hS2 : StrictInterior 1 (2 * (k : ℤ) + 3) (x + 1, y - 1) :=
            si_of_hex k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          by_cases hx0 : x = 0
          · exact Or.inl ((lap_si hS2).2.1 (by omega) (by omega))
          · refine Or.inr ⟨(lap_si hS2).2.2 (by omega) (by omega), ?_, ?_⟩
            · have hw' : wInside (x + 1, y - 1) = (x, y - 1) := by
                unfold wInside
                dsimp only
                rw [if_pos (show x + 1 ≤ 0 by omega)]
                congr 1
                omega
              rw [hw']
              simp [squareCorners]
            · rw [← hm]
              dsimp only
              omega
        · exact absurd rfl hne
        · have hS3 : StrictInterior 1 (2 * (k : ℤ) + 3) (x + 1, y) :=
            si_of_hex k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          exact Or.inl ((lap_si hS3).1 (by omega))
  · by_cases hxy : x + y ≤ 2 * (k : ℤ) + 3 - 1
    · -- the square at (x - 1, y): corners (x-1,y), (x,y+1) black, (x-1,y+1) even
      have hzc : (x, y) ∈ squareCorners (x - 1) (y) := by
        simp [squareCorners]
      refine forced_of_square k m ih (a := x - 1) (b := y) hzc hw ?_ ?_ ?_
      · intro c' hc'
        simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
        rcases hc' with rfl | rfl | rfl | rfl <;>
          exact si_of_hex k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      · unfold wInside
        dsimp only
        rw [if_neg (show ¬ x ≤ 0 by omega)]
        simp [squareCorners]
        omega
      · intro c' hc' hne
        simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
        rcases hc' with rfl | rfl | rfl | rfl <;> try simp only [sub_add_cancel] at hne ⊢
        · have hS1 : StrictInterior 1 (2 * (k : ℤ) + 3) (x - 1, y) :=
            si_of_hex k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          exact Or.inl ((lap_si hS1).1 (by omega))
        · exact absurd rfl hne
        · have hS2 : StrictInterior 1 (2 * (k : ℤ) + 3) (x - 1, y + 1) :=
            si_of_hex k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          by_cases hx2 : x = 2
          · exact Or.inl ((lap_si hS2).2.1 (by omega) (by omega))
          · refine Or.inr ⟨(lap_si hS2).2.2 (by omega) (by omega), ?_, ?_⟩
            · have hw' : wInside (x - 1, y + 1) = (x, y + 1) := by
                unfold wInside
                dsimp only
                rw [if_neg (show ¬ x - 1 ≤ 0 by omega)]
                congr 1
                omega
              rw [hw']
              simp [squareCorners]
            · rw [← hm]
              dsimp only
              omega
        · have hS3 : StrictInterior 1 (2 * (k : ℤ) + 3) (x, y + 1) :=
            si_of_hex k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          exact Or.inl ((lap_si hS3).1 (by omega))
    · -- the square at (x - 1, y - 1): corners (x-1,y-1) even, (x,y-1), (x-1,y) black
      have hzc : (x, y) ∈ squareCorners (x - 1) (y - 1) := by
        simp [squareCorners]
      refine forced_of_square k m ih (a := x - 1) (b := y - 1) hzc hw ?_ ?_ ?_
      · intro c' hc'
        simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
        rcases hc' with rfl | rfl | rfl | rfl <;>
          exact si_of_hex k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      · unfold wInside
        dsimp only
        rw [if_neg (show ¬ x ≤ 0 by omega)]
        simp [squareCorners]
        omega
      · intro c' hc' hne
        simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
        rcases hc' with rfl | rfl | rfl | rfl <;> try simp only [sub_add_cancel] at hne ⊢
        · have hS1 : StrictInterior 1 (2 * (k : ℤ) + 3) (x - 1, y - 1) :=
            si_of_hex k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          by_cases hx2 : x = 2
          · exact Or.inl ((lap_si hS1).2.1 (by omega) (by omega))
          · refine Or.inr ⟨(lap_si hS1).2.2 (by omega) (by omega), ?_, ?_⟩
            · have hw' : wInside (x - 1, y - 1) = (x, y - 1) := by
                unfold wInside
                dsimp only
                rw [if_neg (show ¬ x - 1 ≤ 0 by omega)]
                congr 1
                omega
              rw [hw']
              simp [squareCorners]
            · rw [← hm]
              dsimp only
              omega
        · have hS2 : StrictInterior 1 (2 * (k : ℤ) + 3) (x, y - 1) :=
            si_of_hex k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          exact Or.inl ((lap_si hS2).1 (by omega))
        · have hS3 : StrictInterior 1 (2 * (k : ℤ) + 3) (x - 1, y) :=
            si_of_hex k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          exact Or.inl ((lap_si hS3).1 (by omega))
        · exact absurd rfl hne

/-- **W1Forced at the pure-threes children**: every strict-interior white of `reciprocalField k` is forced by unit squares
inside the strict interior, with no seeds. -/
theorem w1Forced_reciprocal (k : ℕ) : W1Forced 1 (2 * (k : ℤ) + 3) (reciprocalField k) := by
  intro z hz hw
  exact ⟨wInside z, forced_claim k _ z rfl hz hw⟩


/-! ## The closure (lead item 3): a free H or V vertex is never forced inside the strict interior. -/

open FLatticePaper.W1OffCollar

theorem t_parity (k : ℕ) (x y : ℤ) : (1 * x - (2 * (k : ℤ) + 3) * y) % 2 = (x + y) % 2 := by
  have e : (2 * (k : ℤ) + 3) * y = 2 * ((k : ℤ) * y) + 3 * y := by ring
  rw [e]
  omega

theorem s_parity (k : ℕ) (x y : ℤ) : ((2 * (k : ℤ) + 3 + 1) * x + (2 * (k : ℤ) + 3 - 1) * y) % 2 = 0 := by
  have e : (2 * (k : ℤ) + 3 + 1) * x + (2 * (k : ℤ) + 3 - 1) * y = 2 * (((k : ℤ) + 2) * x + ((k : ℤ) + 1) * y) := by
    ring
  rw [e]
  omega

theorem si_not_freeHn {k : ℕ} {x y : ℤ} (hS : StrictInterior 1 (2 * (k : ℤ) + 3) (x, y)) :
    ¬ freeHn 1 (2 * (k : ℤ) + 3) (x, y) := by
  rintro ⟨-, -, hsp⟩
  obtain ⟨-, ht, -, -⟩ := hS
  have hp := t_parity k x y
  unfold hSp w1t at hsp
  unfold w1t w1a at ht
  dsimp only at hsp ht
  split_ifs at ht with he
  · have he' : (x + y) % 2 = 0 := he
    omega
  · have he' : ¬ (x + y) % 2 = 0 := he
    omega

theorem closedRect_shift_of_si {k : ℕ} {x y : ℤ} (hS : StrictInterior 1 (2 * (k : ℤ) + 3) (x, y)) :
    closedRect 1 (2 * (k : ℤ) + 3) (x - 1, y) := by
  have hsp := s_parity k x y
  unfold StrictInterior w1b w1T w1t w1a w1s w1h w1c at hS
  obtain ⟨hA, hB, hC, hD⟩ := hS
  rw [closedRect_iff]
  by_cases hp : (x + y) % 2 = 0
  · have he : EvenSite (x, y) := hp
    rw [if_pos he] at hA hB hC hD
    have hne : ¬ EvenSite (x - 1, y) := by
      unfold EvenSite
      dsimp only
      omega
    right
    refine ⟨hne, ?_, ?_, ?_, ?_⟩
    · try unfold w1T
      try unfold w1t
      try unfold w1s
      dsimp only at hA hB hC hD ⊢
      linarith
    · try unfold w1T
      try unfold w1t
      try unfold w1s
      dsimp only at hA hB hC hD ⊢
      linarith
    · try unfold w1T
      try unfold w1t
      try unfold w1s
      dsimp only at hA hB hC hD hsp ⊢
      have hs4 : 4 ≤ (2 * (k : ℤ) + 3 + 1) * x + (2 * (k : ℤ) + 3 - 1) * y := by omega
      linarith
    · try unfold w1T
      try unfold w1t
      try unfold w1s
      dsimp only at hA hB hC hD ⊢
      linarith
  · have he : ¬ EvenSite (x, y) := hp
    rw [if_neg he] at hA hB hC hD
    have hse : EvenSite (x - 1, y) := by
      unfold EvenSite
      dsimp only
      omega
    left
    refine ⟨hse, ?_, ?_, ?_, ?_⟩
    · try unfold w1T
      try unfold w1t
      try unfold w1s
      dsimp only at hA hB hC hD ⊢
      linarith
    · try unfold w1T
      try unfold w1t
      try unfold w1s
      dsimp only at hA hB hC hD ⊢
      linarith
    · try unfold w1T
      try unfold w1t
      try unfold w1s
      dsimp only at hA hB hC hD hsp ⊢
      have hs1 : 2 * (k : ℤ) + 3 + 1 ≤ (2 * (k : ℤ) + 3 + 1) * x + (2 * (k : ℤ) + 3 - 1) * y := by omega
      linarith
    · try unfold w1T
      try unfold w1t
      try unfold w1s
      dsimp only at hA hB hC hD ⊢
      linarith

theorem not_freeVn_of_si {k : ℕ} {x y : ℤ} (hS : StrictInterior 1 (2 * (k : ℤ) + 3) (x, y)) :
    ¬ freeVn 1 (2 * (k : ℤ) + 3) (x, y) := by
  rintro ⟨-, hnot, -⟩
  exact hnot (closedRect_shift_of_si hS)

/-- The closure: a free H or V vertex is never forced inside the strict interior. -/
theorem free_not_forced (k : ℕ) (x y : ℤ) (hv : freeHn 1 (2 * (k : ℤ) + 3) (x, y) ∨ freeVn 1 (2 * (k : ℤ) + 3) (x, y))
    (o : Site) : ¬ ForcedEdgeIn (reciprocalField k) (StrictInterior 1 (2 * (k : ℤ) + 3)) (fun _ _ => False) (x, y) o := by
  intro h
  cases h with
  | seed hs => exact hs
  | unit inside hR hc hw ho hout hin hforced =>
    have hS := hR (x, y) hc
    rcases hv with h | h
    · exact si_not_freeHn hS h
    · exact not_freeVn_of_si hS h

/-! ## The bridge to the frame of `3^k` (the form of the named input `hW1`, at the conjugate of the pure twos words). -/

/-- **W1Forced at the pure-threes word**, in the frame's own grades and standard field: the child of `3^k` is `1/(2k+3)` and its
standard field is `reciprocalField k`. -/
theorem w1Forced_threes (k : ℕ) :
    FLatticePaper.W1.W1Forced (frameAt (List.replicate k FLatticePaper.Farey.Digit.three)).child.num
      (frameAt (List.replicate k FLatticePaper.Farey.Digit.three)).child.den (standardField (List.replicate k FLatticePaper.Farey.Digit.three)) := by
  have hc : (frameAt (List.replicate k FLatticePaper.Farey.Digit.three)).child = ⟨1, 2 * (k : ℤ) + 3⟩ := reciprocalFrame_child k
  rw [hc, standardField_threes]
  exact w1Forced_reciprocal k

end FLatticePaper.W1Reciprocal
