import FLatticePaper.Plane.Induction.PriceRange

/-! `NoPriceSaddle` at `3^k` (`F1_noPriceSaddle` of `StrongResidual`).

A saddle at `s` is two equal nonzero increments of the price along the axis through `s`; it is excluded once the three sites of
the star of `s` have prices in an interval of length one. The price is `P(z + combine i j) = P z − i`, and stars translate with the
raw representative, so it suffices that `P` on the star of every raw centre lies in `[0,1]`. Those star sites are either raw
(`threesP_raw_range`) or reached from a fixed set of four period shifts `±K`, `±T` into the raw tile, where the exact value
`priceValueRaw` applies. -/

namespace FLatticePaper.Induction

open Farey Construction

/-- The exact price on the raw tile: `1` on the points with `y₁ ≤ 1`, except that on the top row `y₂ = d+1` only `y₁ = 2−d` gives `1`. -/
def priceValueRaw (d : ℤ) (u : Site) : ℤ :=
  if u.2 = d + 1 then (if u.1 = 2 - d then 1 else 0) else (if u.1 ≤ 1 then 1 else 0)

theorem threesP_raw_exact (k : ℕ) (y : Site)
    (hy : y ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites) :
    threesP k y = priceValueRaw (2 * (k : ℤ) + 3) y := by
  obtain ⟨y1, y2⟩ := y
  have hy' : RawMem (2 * (k : ℤ) + 3) y1 y2 := (raw_mem_site (2 * (k : ℤ) + 3) (y1, y2)).mp hy
  by_cases hv : RawMem (2 * (k : ℤ) + 3) (y1 - 1) (y2 + 1)
  · rw [threesP_of_N k y1 y2 hy' hv]
    have hne : ¬ (y2 = 2 * (k : ℤ) + 3 + 1) := by
      unfold RawMem at hv
      omega
    unfold priceValueRaw
    simp only [hne, if_false]
  · have hcases : (y1 = 0 ∧ y2 = 0) ∨ (y1 = 2 ∧ y2 = 2 * (k : ℤ) + 3 + 1) ∨
        (y2 = 2 * (k : ℤ) + 3 + 1 ∧ 2 - (2 * (k : ℤ) + 3) ≤ y1 ∧ y1 ≤ 1) ∨
        (y1 = 2 - (2 * (k : ℤ) + 3) ∧ y2 = 2 * (k : ℤ) + 3 - 1) ∨
        (y1 = 2 - (2 * (k : ℤ) + 3) ∧ y2 = 2 * (k : ℤ) + 3) := by
      unfold RawMem at hy' hv
      omega
    have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, h3, h4⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [threesP_E3a]
      unfold priceValueRaw
      rw [if_neg (by omega), if_pos (by norm_num)]
    · rw [threesP_E3b]
      unfold priceValueRaw
      rw [if_pos rfl, if_neg (by omega)]
    · rw [threesP_E1 k y1 h3 h4]
      unfold priceValueRaw
      dsimp only
      split_ifs <;> first | rfl | omega
    · rw [threesP_E2a]
      unfold priceValueRaw
      rw [if_neg (by omega), if_pos (by omega)]
    · rw [threesP_E2b, threesP_E3b]
      unfold priceValueRaw
      rw [if_neg (by omega), if_pos (by omega)]
      norm_num

/-- Shifts by `n·K`: `P(w + nK) = P w − n`, by induction on `n`. -/
theorem threesP_nK (k : ℕ) (w : Site) (n : ℤ) :
    threesP k (w + (n * (2 * (k : ℤ) + 3), n)) = threesP k w - n := by
  refine Int.induction_on n ?_ ?_ ?_
  · have e0 : w + ((0 : ℤ) * (2 * (k : ℤ) + 3), (0 : ℤ)) = w := by ext <;> simp
    rw [e0]
    simp
  · intro i ih
    have e : w + (((i : ℤ) + 1) * (2 * (k : ℤ) + 3), (i : ℤ) + 1) =
        (w + ((i : ℤ) * (2 * (k : ℤ) + 3), (i : ℤ))) + (2 * (k : ℤ) + 3, 1) := by
      ext
      all_goals simp only [Prod.fst_add, Prod.snd_add]
      all_goals ring
    rw [e, threesP_K, ih]
    ring
  · intro i ih
    have e : w + ((-(i : ℤ) - 1) * (2 * (k : ℤ) + 3), -(i : ℤ) - 1) + (2 * (k : ℤ) + 3, 1) =
        w + (-(i : ℤ) * (2 * (k : ℤ) + 3), -(i : ℤ)) := by
      ext
      all_goals simp only [Prod.fst_add, Prod.snd_add]
      all_goals ring
    have h := threesP_K k (w + ((-(i : ℤ) - 1) * (2 * (k : ℤ) + 3), -(i : ℤ) - 1))
    rw [e, ih] at h
    linarith

/-- Shifts by `m·T`: `P(w + mT) = P w`. -/
theorem threesP_mT (k : ℕ) (w : Site) (m : ℤ) :
    threesP k (w + (m * (1 - (2 * (k : ℤ) + 3)), m * (1 + (2 * (k : ℤ) + 3)))) = threesP k w := by
  refine Int.induction_on m ?_ ?_ ?_
  · have e0 : w + ((0 : ℤ) * (1 - (2 * (k : ℤ) + 3)), (0 : ℤ) * (1 + (2 * (k : ℤ) + 3))) = w := by
      ext <;> simp
    rw [e0]
  · intro i ih
    have e : w + (((i : ℤ) + 1) * (1 - (2 * (k : ℤ) + 3)), ((i : ℤ) + 1) * (1 + (2 * (k : ℤ) + 3))) =
        (w + ((i : ℤ) * (1 - (2 * (k : ℤ) + 3)), (i : ℤ) * (1 + (2 * (k : ℤ) + 3)))) +
          (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) := by
      ext
      all_goals simp only [Prod.fst_add, Prod.snd_add]
      all_goals ring
    rw [e, threesP_T, ih]
  · intro i ih
    have e : w + ((-(i : ℤ) - 1) * (1 - (2 * (k : ℤ) + 3)), (-(i : ℤ) - 1) * (1 + (2 * (k : ℤ) + 3))) +
        (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) =
        w + (-(i : ℤ) * (1 - (2 * (k : ℤ) + 3)), -(i : ℤ) * (1 + (2 * (k : ℤ) + 3))) := by
      ext
      all_goals simp only [Prod.fst_add, Prod.snd_add]
      all_goals ring
    have h := threesP_T k (w + ((-(i : ℤ) - 1) * (1 - (2 * (k : ℤ) + 3)), (-(i : ℤ) - 1) * (1 + (2 * (k : ℤ) + 3))))
    rw [e, ih] at h
    exact h.symm

/-- The shift by a lattice vector `combine i j`: `P(w + combine i j) = P w − i`. -/
theorem threesP_combine (k : ℕ) (w : Site) (i j : ℤ) :
    threesP k (w + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j) = threesP k w - i := by
  rw [combine_eq _ (by omega : (2 * (k : ℤ) + 3) % 2 = 1)]
  have e : w + (i * (2 * (k : ℤ) + 3) + j * (1 - (2 * (k : ℤ) + 3)), i + j * (1 + (2 * (k : ℤ) + 3))) =
      (w + (i * (2 * (k : ℤ) + 3), i)) + (j * (1 - (2 * (k : ℤ) + 3)), j * (1 + (2 * (k : ℤ) + 3))) := by
    ext
    all_goals simp only [Prod.fst_add, Prod.snd_add]
    all_goals ring
  rw [e, threesP_mT, threesP_nK]

set_option maxHeartbeats 400000 in
/-- The covering of a star site outside the raw tile. The parity fixes the axis of the star. Even centres use `K⁺` (incNeg)
and `K⁻` (incPos); odd centres use `T⁺` on the bottom row `c₂ = 0` and `K⁺` otherwise (incNeg), and `T⁻` on the top row
`c₂ = d+1` and `K⁻` otherwise (incPos). -/
theorem star_cover (d c1 c2 w1 w2 : ℤ) (hd : 3 ≤ d) (hodd : d % 2 = 1)
    (hc : RawMem d c1 c2) (hw : ¬ RawMem d w1 w2)
    (hadj : (c1 + c2) % 2 = 0 ∧ (w1 = c1 - 1 ∧ w2 = c2 ∨ w1 = c1 + 1 ∧ w2 = c2) ∨
      (c1 + c2) % 2 = 1 ∧ (w1 = c1 ∧ w2 = c2 - 1 ∨ w1 = c1 ∧ w2 = c2 + 1)) :
    (RawMem d (w1 + d) (w2 + 1) ∧
        ¬((w2 + 1 = d + 1 ∧ w1 + d = 2 - d) ∨ (w2 + 1 ≠ d + 1 ∧ w1 + d ≤ 1))) ∨
    (RawMem d (w1 - d) (w2 - 1) ∧
        ((w2 - 1 = d + 1 ∧ w1 - d = 2 - d) ∨ (w2 - 1 ≠ d + 1 ∧ w1 - d ≤ 1))) ∨
    RawMem d (w1 + (1 - d)) (w2 + (1 + d)) ∨
    RawMem d (w1 - (1 - d)) (w2 - (1 + d)) := by
  unfold RawMem at hc hw ⊢
  obtain ⟨hc1, hc2, hc3⟩ := hc
  rcases hadj with ⟨hp, h⟩ | ⟨hp, h⟩
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst w1; subst w2
      left
      constructor <;> omega
    · subst w1; subst w2
      right; left
      constructor <;> omega
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst w1; subst w2
      by_cases hz : c2 = 0
      · right; right; left
        omega
      · left
        constructor <;> omega
    · subst w1; subst w2
      by_cases hz : c2 = d + 1
      · right; right; right
        omega
      · right; left
        constructor <;> omega

set_option maxHeartbeats 400000 in
/-- The price on a star site outside the raw tile, and on the raw tile, lies in `[0,1]`. -/
theorem star_range (k : ℕ) (c w : Site)
    (hc : c ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites)
    (hw : w = FLatticePaper.incomingNeg c ∨ w = FLatticePaper.incomingPos c) :
    0 ≤ threesP k w ∧ threesP k w ≤ 1 := by
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have hodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hcR : RawMem (2 * (k : ℤ) + 3) c.1 c.2 := (raw_mem_site _ c).mp hc
  have hadj : (c.1 + c.2) % 2 = 0 ∧ (w.1 = c.1 - 1 ∧ w.2 = c.2 ∨ w.1 = c.1 + 1 ∧ w.2 = c.2) ∨
      (c.1 + c.2) % 2 = 1 ∧ (w.1 = c.1 ∧ w.2 = c.2 - 1 ∨ w.1 = c.1 ∧ w.2 = c.2 + 1) := by
    obtain ⟨c1, c2⟩ := c
    obtain ⟨w1, w2⟩ := w
    by_cases hpar : (c1 + c2) % 2 = 0
    · rcases hw with hw | hw
      · left
        refine ⟨hpar, Or.inl ?_⟩
        simp only [FLatticePaper.incomingNeg, FLatticePaper.EvenSite, hpar, if_true, Prod.mk.injEq] at hw
        exact hw
      · left
        refine ⟨hpar, Or.inr ?_⟩
        simp only [FLatticePaper.incomingPos, FLatticePaper.EvenSite, hpar, if_true, Prod.mk.injEq] at hw
        exact hw
    · rcases hw with hw | hw
      · right
        refine ⟨by omega, Or.inl ?_⟩
        simp only [FLatticePaper.incomingNeg, FLatticePaper.EvenSite, hpar, if_false, Prod.mk.injEq] at hw
        exact hw
      · right
        refine ⟨by omega, Or.inr ?_⟩
        simp only [FLatticePaper.incomingPos, FLatticePaper.EvenSite, hpar, if_false, Prod.mk.injEq] at hw
        exact hw
  by_cases hwR : RawMem (2 * (k : ℤ) + 3) w.1 w.2
  · exact threesP_raw_range k w ((raw_mem_site _ w).mpr hwR)
  · have hcov := star_cover (2 * (k : ℤ) + 3) c.1 c.2 w.1 w.2 hd3 hodd hcR hwR hadj
    rcases hcov with ⟨hK, hV⟩ | ⟨hK', hV'⟩ | hT | hT'
    · have hu := threesP_raw_exact k (w + (2 * (k : ℤ) + 3, 1)) ((raw_mem_site _ _).mpr hK)
      have hval : priceValueRaw (2 * (k : ℤ) + 3) (w + (2 * (k : ℤ) + 3, 1)) = 0 := by
        unfold priceValueRaw
        simp only [Prod.fst_add, Prod.snd_add]
        split_ifs <;> omega
      have hs := threesP_K k w
      constructor <;> linarith
    · have hu := threesP_raw_exact k (w - (2 * (k : ℤ) + 3, 1)) ((raw_mem_site _ _).mpr hK')
      have hval : priceValueRaw (2 * (k : ℤ) + 3) (w - (2 * (k : ℤ) + 3, 1)) = 1 := by
        unfold priceValueRaw
        simp only [Prod.fst_sub, Prod.snd_sub]
        split_ifs <;> omega
      have hs := threesP_K k (w - (2 * (k : ℤ) + 3, 1))
      have e : w - (2 * (k : ℤ) + 3, 1) + (2 * (k : ℤ) + 3, 1) = w := by
        ext <;> simp
      rw [e] at hs
      constructor <;> linarith
    · have hu := threesP_raw_exact k (w + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)))
        ((raw_mem_site _ _).mpr hT)
      have hs := threesP_T k w
      have hv01 : priceValueRaw (2 * (k : ℤ) + 3) (w + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3))) = 0 ∨
          priceValueRaw (2 * (k : ℤ) + 3) (w + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3))) = 1 := by
        unfold priceValueRaw
        split_ifs <;> simp
      rcases hv01 with h0 | h1 <;> constructor <;> linarith
    · have hu := threesP_raw_exact k (w - (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)))
        ((raw_mem_site _ _).mpr hT')
      have hs := threesP_T k (w - (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)))
      have e : w - (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) = w := by
        ext <;> simp
      rw [e] at hs
      have hv01 : priceValueRaw (2 * (k : ℤ) + 3) (w - (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3))) = 0 ∨
          priceValueRaw (2 * (k : ℤ) + 3) (w - (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3))) = 1 := by
        unfold priceValueRaw
        split_ifs <;> simp
      rcases hv01 with h0 | h1 <;> constructor <;> linarith

/-- A lattice vector `combine i j` has even coordinate sum. -/
theorem combine_even (k : ℕ) (i j : ℤ) :
    ∃ t : ℤ, ((Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j).1 +
      ((Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j).2 = 2 * t := by
  rw [combine_eq _ (by omega : (2 * (k : ℤ) + 3) % 2 = 1)]
  exact ⟨i * ((k : ℤ) + 2) + j, by ring⟩

theorem incomingNeg_add (y c : Site) (t : ℤ) (ht : c.1 + c.2 = 2 * t) :
    FLatticePaper.incomingNeg (y + c) = FLatticePaper.incomingNeg y + c := by
  unfold FLatticePaper.incomingNeg FLatticePaper.EvenSite
  by_cases h : (y.1 + y.2) % 2 = 0
  · have h' : ((y + c).1 + (y + c).2) % 2 = 0 := by
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    rw [if_pos h, if_pos h']
    ext
    all_goals simp only [Prod.fst_add, Prod.snd_add]
    all_goals ring
  · have h' : ¬ (((y + c).1 + (y + c).2) % 2 = 0) := by
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    rw [if_neg h, if_neg h']
    ext
    all_goals simp only [Prod.fst_add, Prod.snd_add]
    all_goals ring

theorem incomingPos_add (y c : Site) (t : ℤ) (ht : c.1 + c.2 = 2 * t) :
    FLatticePaper.incomingPos (y + c) = FLatticePaper.incomingPos y + c := by
  unfold FLatticePaper.incomingPos FLatticePaper.EvenSite
  by_cases h : (y.1 + y.2) % 2 = 0
  · have h' : ((y + c).1 + (y + c).2) % 2 = 0 := by
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    rw [if_pos h, if_pos h']
    ext
    all_goals simp only [Prod.fst_add, Prod.snd_add]
    all_goals ring
  · have h' : ¬ (((y + c).1 + (y + c).2) % 2 = 0) := by
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    rw [if_neg h, if_neg h']
    ext
    all_goals simp only [Prod.fst_add, Prod.snd_add]
    all_goals ring

/-- **`F1_noPriceSaddle` at `3^k`.** -/
theorem noPriceSaddle_threes (k : ℕ) :
    NoPriceSaddle (frameAt (List.replicate k Digit.three)) (standardField (List.replicate k Digit.three)) := by
  intro s
  dsimp only
  obtain ⟨y, hyR, i, j, hs⟩ := raw_cover_rep k s
  obtain ⟨t, ht⟩ := combine_even k i j
  subst hs
  have hyS : y ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites := (raw_mem_site _ y).mpr hyR
  unfold priceIncrement
  simp only [frame_price_threes]
  rw [incomingNeg_add y _ t ht, incomingPos_add y _ t ht]
  simp only [threesP_combine]
  have hB := threesP_raw_range k y hyS
  have hA := star_range k y (FLatticePaper.incomingNeg y) hyS (Or.inl rfl)
  have hC := star_range k y (FLatticePaper.incomingPos y) hyS (Or.inr rfl)
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2]

end FLatticePaper.Induction
