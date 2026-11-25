import FLatticePaper.Plane.Induction.W1Twos

namespace FLatticePaper.W1Twos

open FLatticePaper FLatticePaper.W1 FLatticePaper.Construction FLatticePaper.Induction FLatticePaper.TwosEPolicy FLatticePaper.AndOrRank Farey

/-- The twos field of the word `2^(k+1)`. -/
noncomputable abbrev twF (k : ℕ) : Field := standardField (List.replicate (k + 1) Digit.two)

/-- The forced arrow of a white strict-interior site: horizontal for the even classes, vertical for the odd ones. -/
def twArrow (a : ℤ) (c : Site) : Site :=
  if (c.1 + c.2) % 2 = 0 then
    (if c.2 - c.1 = a - 2 then incomingPos c else incomingNeg c)
  else
    (if (c.2 - c.1 ≤ a - 3 ∧ c.2 < a - 1) ∨ (a + 1 ≤ c.2 - c.1 ∧ c.2 < 2 * a - 1) then incomingNeg c
      else incomingPos c)

/-- The grade of a white strict-interior site (the archive's grades). -/
def twGrade (a : ℤ) (c : Site) : ℤ :=
  if (c.1 + c.2) % 2 = 0 then
    (if c.2 - c.1 = a - 2 then (c.1 - 1) + (if c.1 = a then 1 else 0)
      else (a - 1 - c.1) + (if c.1 = 0 then 1 else 0))
  else
    (if c.2 - c.1 ≤ a - 3 then (((c.2 - (a - 1)).natAbs : ℕ) : ℤ) + (if c.1 = a ∧ c.2 - c.1 = a - 3 then 1 else 0)
      else (((c.2 - (2 * a - 1)).natAbs : ℕ) : ℤ) + (if c.1 = 0 ∧ c.2 - c.1 = a + 1 then 1 else 0))

theorem twos_lap_zero_or_neg {k : ℕ} {x y : ℤ}
    (hS : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x, y)) :
    laplacian (twF k) (x, y) = 0 ∨ laplacian (twF k) (x, y) = -1 := by
  show laplacian (standardField (List.replicate (k + 1) Digit.two)) (x, y) = 0 ∨ _
  rw [laplacian_twos_std_native (native_of_si_twos hS)]
  split_ifs <;> simp

theorem twArrow_E {a x y : ℤ} (h : TwosClE a x y) : twArrow a (x, y) = (x + 1, y) := by
  obtain ⟨h1, h2, -, -⟩ := h
  simp [twArrow, incomingPos, EvenSite, h1, h2]

theorem twArrow_W {a x y : ℤ} (h : TwosClW a x y) : twArrow a (x, y) = (x - 1, y) := by
  obtain ⟨h1, h2, -, -⟩ := h
  have hne : y - x ≠ a - 2 := by omega
  simp [twArrow, incomingNeg, EvenSite, h1, hne]

theorem twGrade_E {a x y : ℤ} (h : TwosClE a x y) : twGrade a (x, y) = (x - 1) + (if x = a then 1 else 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp [twGrade, h1, h2]

theorem twGrade_W {a x y : ℤ} (h : TwosClW a x y) : twGrade a (x, y) = (a - 1 - x) + (if x = 0 then 1 else 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hne : y - x ≠ a - 2 := by omega
  simp [twGrade, h1, hne]

/-- The square step: a white centre forced out of a square whose other white corners point inward with smaller grade. -/
theorem twForced_of_square (k : ℕ) (m : ℕ)
    (ih : ∀ m' < m, ∀ c : Site, (twGrade (2 * (k : ℤ) + 4) c).toNat = m' →
      StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) c → laplacian (twF k) c = 0 →
      ForcedEdgeIn (twF k) (StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5)) (fun _ _ => False) c
        (twArrow (2 * (k : ℤ) + 4) c))
    {x y p q : ℤ} (hm : (twGrade (2 * (k : ℤ) + 4) (x, y)).toNat = m)
    (hz : (x, y) ∈ squareCorners p q) (hw : laplacian (twF k) (x, y) = 0)
    (hR : ∀ c' ∈ squareCorners p q, StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) c')
    (hout : twArrow (2 * (k : ℤ) + 4) (x, y) ∉ squareCorners p q)
    (hcorner : ∀ c' ∈ squareCorners p q, c' ≠ (x, y) → laplacian (twF k) c' = -1 ∨
      (laplacian (twF k) c' = 0 ∧ twArrow (2 * (k : ℤ) + 4) c' ∈ squareCorners p q ∧
        0 ≤ twGrade (2 * (k : ℤ) + 4) c' ∧ twGrade (2 * (k : ℤ) + 4) c' < twGrade (2 * (k : ℤ) + 4) (x, y))) :
    ForcedEdgeIn (twF k) (StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5)) (fun _ _ => False) (x, y)
      (twArrow (2 * (k : ℤ) + 4) (x, y)) := by
  have ho : twArrow (2 * (k : ℤ) + 4) (x, y) = incomingNeg (x, y) ∨ twArrow (2 * (k : ℤ) + 4) (x, y) = incomingPos (x, y) := by
    unfold twArrow
    split_ifs <;> simp
  refine ForcedEdgeIn.unit (twArrow (2 * (k : ℤ) + 4)) hR hz hw ho hout ?_ ?_
  · intro c' hc' hne
    rcases hcorner c' hc' hne with h | ⟨h0, hmem, -, -⟩
    · exact Or.inl h
    · refine Or.inr ⟨h0, hmem, ?_⟩
      unfold twArrow
      split_ifs <;> simp
  · intro c' hc' hne h0
    rcases hcorner c' hc' hne with h | ⟨h0', hmem, hg0, hlt⟩
    · rw [h] at h0
      norm_num at h0
    · exact ih _ (by omega) c' rfl (hR c' hc') h0'

theorem si_corner_E {k : ℕ} {x y : ℤ} (hx : 2 ≤ x) (hxa : x ≤ 2 * (k : ℤ) + 4)
    (hyx : y - x = 2 * (k : ℤ) + 4 - 2) (hp : (x + y) % 2 = 0) :
    StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x - 1, y - 1) := by
  refine (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) (x - 1) (y - 1)).2
    ⟨⟨by nlinarith, by nlinarith⟩, fun _ => ⟨by nlinarith, by nlinarith⟩, fun h => absurd (by omega) h⟩

theorem twArrow_LN {a x y : ℤ} (h : TwosClLN a x y) : twArrow a (x, y) = (x, y + 1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hnot : ¬ ((y - x ≤ a - 3 ∧ y < a - 1) ∨ (a + 1 ≤ y - x ∧ y < 2 * a - 1)) := by
    rintro (⟨-, hc⟩ | ⟨hc, -⟩)
    · omega
    · omega
  simp only [twArrow, if_neg h1, if_neg hnot, incomingPos, EvenSite]

theorem twGrade_LN {a x y : ℤ} (h : TwosClLN a x y) :
    twGrade a (x, y) = ((y - (a - 1)) : ℤ) + (if x = a ∧ y - x = a - 3 then 1 else 0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hodd : ¬ (x + y) % 2 = 0 := h1
  have hle : y - x ≤ a - 3 := h3
  simp only [twGrade, hodd, hle, if_true, if_false]
  have hn : (((y - (a - 1)).natAbs : ℕ) : ℤ) = y - (a - 1) := by omega
  rw [hn]

theorem si_corner_E_odd_down {k : ℕ} {x y : ℤ} (hx : 2 ≤ x) (hxa : x ≤ 2 * (k : ℤ) + 4)
    (hyx : y - x = 2 * (k : ℤ) + 4 - 2) (hp : (x + y) % 2 = 0) :
    StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x, y - 1) := by
  refine (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) x (y - 1)).2
    ⟨⟨by nlinarith, by nlinarith⟩, fun h => absurd h (by omega), fun _ => ⟨by nlinarith, by nlinarith⟩⟩

theorem si_corner_E_odd_left {k : ℕ} {x y : ℤ} (hx : 2 ≤ x) (hxa : x ≤ 2 * (k : ℤ) + 4)
    (hyx : y - x = 2 * (k : ℤ) + 4 - 2) (hp : (x + y) % 2 = 0) :
    StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x - 1, y) := by
  refine (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) (x - 1) y).2
    ⟨⟨by nlinarith, by nlinarith⟩, fun h => absurd h (by omega), fun _ => ⟨by nlinarith, by nlinarith⟩⟩

theorem twos_sub_E (k m : ℕ)
    (ih : ∀ m' < m, ∀ c : Site, (twGrade (2 * (k : ℤ) + 4) c).toNat = m' →
      StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) c → laplacian (twF k) c = 0 →
      ForcedEdgeIn (twF k) (StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5)) (fun _ _ => False) c
        (twArrow (2 * (k : ℤ) + 4) c))
    {x y : ℤ} (hm : (twGrade (2 * (k : ℤ) + 4) (x, y)).toNat = m)
    (hE : TwosClE (2 * (k : ℤ) + 4) x y)
    (hS : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x, y)) :
    ForcedEdgeIn (twF k) (StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5)) (fun _ _ => False) (x, y)
      (twArrow (2 * (k : ℤ) + 4) (x, y)) := by
  obtain ⟨c1, c2, c3, c4⟩ := hE
  have hE' : TwosClE (2 * (k : ℤ) + 4) x y := ⟨c1, c2, c3, c4⟩
  have hw : laplacian (twF k) (x, y) = 0 := (twos_lap_even_iff hS c1).2 (Or.inl hE')
  refine twForced_of_square k m ih hm (p := x - 1) (q := y - 1) (by simp [squareCorners]) hw ?_ ?_ ?_
  · intro c' hc'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl | rfl <;> try simp only [sub_add_cancel]
    · exact si_corner_E c3 c4 c2 c1
    · exact si_corner_E_odd_down c3 c4 c2 c1
    · exact si_corner_E_odd_left c3 c4 c2 c1
    · exact hS
  · rw [twArrow_E hE']
    simp [squareCorners]
    omega
  · intro c' hc' hne
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl | rfl <;> try simp only [sub_add_cancel] at hne ⊢
    · -- the corner (x-1, y-1): even, white `E` for x ≥ 3
      have hSc := si_corner_E c3 c4 c2 c1
      have hpc : ((x - 1) + (y - 1)) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg hSc with h0 | h1
      · rcases (twos_lap_even_iff hSc hpc).1 h0 with hc | hc
        · obtain ⟨d1, d2, d3, d4⟩ := hc
          right
          refine ⟨h0, ?_, ?_, ?_⟩
          · rw [twArrow_E ⟨d1, d2, d3, d4⟩]
            simp [squareCorners]
          · rw [twGrade_E ⟨d1, d2, d3, d4⟩]
            split_ifs <;> omega
          · rw [twGrade_E ⟨d1, d2, d3, d4⟩, twGrade_E hE']
            split_ifs <;> omega
        · obtain ⟨d1, d2, -, -⟩ := hc
          exfalso
          omega
      · exact Or.inl h1
    · -- the corner (x, y-1): odd, white `LN` for x ≥ 3
      have hSc := si_corner_E_odd_down c3 c4 c2 c1
      have hpc : ¬ (x + (y - 1)) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg hSc with h0 | h1
      · rcases (twos_lap_odd_iff hSc hpc).1 h0 with hc | hc | hc | hc
        · obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hc
          exfalso
          omega
        · obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hc
          right
          refine ⟨h0, ?_, ?_, ?_⟩
          · rw [twArrow_LN ⟨d1, d2, d3, d4, d5, d6, d7⟩]
            simp [squareCorners]
          · rw [twGrade_LN ⟨d1, d2, d3, d4, d5, d6, d7⟩]
            split_ifs <;> omega
          · rw [twGrade_LN ⟨d1, d2, d3, d4, d5, d6, d7⟩, twGrade_E hE']
            split_ifs <;> omega
        · obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hc
          exfalso
          omega
        · obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hc
          exfalso
          omega
      · exact Or.inl h1
    · -- the corner (x-1, y): odd, black
      have hSc := si_corner_E_odd_left c3 c4 c2 c1
      have hpc : ¬ ((x - 1) + y) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg hSc with h0 | h1
      · exfalso
        rcases (twos_lap_odd_iff hSc hpc).1 h0 with hc | hc | hc | hc <;>
          (obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hc; omega)
      · exact Or.inl h1
    · exact absurd rfl hne

theorem twArrow_US {a x y : ℤ} (h : TwosClUS a x y) : twArrow a (x, y) = (x, y - 1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hc : (y - x ≤ a - 3 ∧ y < a - 1) ∨ (a + 1 ≤ y - x ∧ y < 2 * a - 1) := Or.inr ⟨h2, h6⟩
  simp only [twArrow, if_neg (show ¬ (x + y) % 2 = 0 from h1), if_pos hc, incomingNeg, EvenSite]

theorem twArrow_UN {a x y : ℤ} (h : TwosClUN a x y) : twArrow a (x, y) = (x, y + 1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hnot : ¬ ((y - x ≤ a - 3 ∧ y < a - 1) ∨ (a + 1 ≤ y - x ∧ y < 2 * a - 1)) := by
    rintro (⟨hc, -⟩ | ⟨-, hc⟩)
    · omega
    · omega
  simp only [twArrow, if_neg (show ¬ (x + y) % 2 = 0 from h1), if_neg hnot, incomingPos, EvenSite]

theorem twArrow_LS {a x y : ℤ} (h : TwosClLS a x y) : twArrow a (x, y) = (x, y - 1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hc : (y - x ≤ a - 3 ∧ y < a - 1) ∨ (a + 1 ≤ y - x ∧ y < 2 * a - 1) := Or.inl ⟨h3, h6⟩
  simp only [twArrow, if_neg (show ¬ (x + y) % 2 = 0 from h1), if_pos hc, incomingNeg, EvenSite]

theorem twGrade_US {a x y : ℤ} (h : TwosClUS a x y) :
    twGrade a (x, y) = (2 * a - 1 - y) + (if x = 0 ∧ y - x = a + 1 then 1 else 0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hodd : ¬ (x + y) % 2 = 0 := h1
  have hgt : ¬ (y - x ≤ a - 3) := by omega
  unfold twGrade
  dsimp only
  rw [if_neg hodd, if_neg hgt]
  have hn : (((y - (2 * a - 1)).natAbs : ℕ) : ℤ) = 2 * a - 1 - y := by omega
  rw [hn]

theorem twGrade_LS {a x y : ℤ} (h : TwosClLS a x y) :
    twGrade a (x, y) = (a - 1 - y) + (if x = a ∧ y - x = a - 3 then 1 else 0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hodd : ¬ (x + y) % 2 = 0 := h1
  unfold twGrade
  dsimp only
  rw [if_neg hodd, if_pos h3]
  have hn : (((y - (a - 1)).natAbs : ℕ) : ℤ) = a - 1 - y := by omega
  rw [hn]

theorem twGrade_UN {a x y : ℤ} (h : TwosClUN a x y) :
    twGrade a (x, y) = (y - (2 * a - 1)) + (if x = 0 ∧ y - x = a + 1 then 1 else 0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hodd : ¬ (x + y) % 2 = 0 := h1
  have hgt : ¬ (y - x ≤ a - 3) := by omega
  unfold twGrade
  dsimp only
  rw [if_neg hodd, if_neg hgt]
  have hn : (((y - (2 * a - 1)).natAbs : ℕ) : ℤ) = y - (2 * a - 1) := by omega
  rw [hn]


theorem si_W_right_odd {k : ℕ} {x y : ℤ} (c1 : (x + y) % 2 = 0) (c2 : y - x = 2 * (k : ℤ) + 4)
    (c3 : 0 ≤ x) (c4 : x ≤ 2 * (k : ℤ) + 4 - 2) :
    StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x + 1, y) := by
  refine (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) (x + 1) y).2
    ⟨⟨by nlinarith, by nlinarith⟩, fun h => absurd h (by omega), fun _ => ⟨by nlinarith, by nlinarith⟩⟩

theorem si_W_up_odd {k : ℕ} {x y : ℤ} (c1 : (x + y) % 2 = 0) (c2 : y - x = 2 * (k : ℤ) + 4)
    (c3 : 0 ≤ x) (c4 : x ≤ 2 * (k : ℤ) + 4 - 2) :
    StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x, y + 1) := by
  refine (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) x (y + 1)).2
    ⟨⟨by nlinarith, by nlinarith⟩, fun h => absurd h (by omega), fun _ => ⟨by nlinarith, by nlinarith⟩⟩

theorem si_W_diag_even {k : ℕ} {x y : ℤ} (c1 : (x + y) % 2 = 0) (c2 : y - x = 2 * (k : ℤ) + 4)
    (c3 : 0 ≤ x) (c4 : x ≤ 2 * (k : ℤ) + 4 - 2) :
    StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x + 1, y + 1) := by
  refine (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) (x + 1) (y + 1)).2
    ⟨⟨by nlinarith, by nlinarith⟩, fun _ => ⟨by nlinarith, by nlinarith⟩, fun h => absurd (by omega) h⟩


/-- The sub-case `W`: the square with `z` as its south-west corner. -/
theorem twos_sub_W (k m : ℕ)
    (ih : ∀ m' < m, ∀ c : Site, (twGrade (2 * (k : ℤ) + 4) c).toNat = m' →
      StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) c → laplacian (twF k) c = 0 →
      ForcedEdgeIn (twF k) (StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5)) (fun _ _ => False) c
        (twArrow (2 * (k : ℤ) + 4) c))
    {x y : ℤ} (hm : (twGrade (2 * (k : ℤ) + 4) (x, y)).toNat = m)
    (hW : TwosClW (2 * (k : ℤ) + 4) x y)
    (hS : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x, y)) :
    ForcedEdgeIn (twF k) (StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5)) (fun _ _ => False) (x, y)
      (twArrow (2 * (k : ℤ) + 4) (x, y)) := by
  obtain ⟨c1, c2, c3, c4⟩ := hW
  have hW' : TwosClW (2 * (k : ℤ) + 4) x y := ⟨c1, c2, c3, c4⟩
  have hw : laplacian (twF k) (x, y) = 0 := (twos_lap_even_iff hS c1).2 (Or.inr hW')
  refine twForced_of_square k m ih hm (p := x) (q := y) (by simp [squareCorners]) hw ?_ ?_ ?_
  · intro c' hc'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl | rfl
    · exact hS
    · exact si_W_right_odd c1 c2 c3 c4
    · exact si_W_up_odd c1 c2 c3 c4
    · exact si_W_diag_even c1 c2 c3 c4
  · rw [twArrow_W hW']
    simp [squareCorners]
    omega
  · intro c' hc' hne
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · -- the corner (x+1, y): odd, black
      have hSc := si_W_right_odd c1 c2 c3 c4
      have hpc : ¬ (x + 1 + y) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg hSc with h0 | h1
      · exfalso
        rcases (twos_lap_odd_iff hSc hpc).1 h0 with hc | hc | hc | hc <;>
          (obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hc; omega)
      · exact Or.inl h1
    · -- the corner (x, y+1): odd, US for x < a-2
      have hSc := si_W_up_odd c1 c2 c3 c4
      have hpc : ¬ (x + (y + 1)) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg hSc with h0 | h1
      · rcases (twos_lap_odd_iff hSc hpc).1 h0 with hc | hc | hc | hc
        · obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hc
          exfalso
          omega
        · obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hc
          exfalso
          omega
        · obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hc
          right
          refine ⟨h0, ?_, ?_, ?_⟩
          · rw [twArrow_US ⟨d1, d2, d3, d4, d5, d6, d7⟩]
            simp [squareCorners]
          · rw [twGrade_US ⟨d1, d2, d3, d4, d5, d6, d7⟩]
            split_ifs <;> omega
          · rw [twGrade_US ⟨d1, d2, d3, d4, d5, d6, d7⟩, twGrade_W hW']
            split_ifs <;> omega
        · obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hc
          exfalso
          omega
      · exact Or.inl h1
    · -- the corner (x+1, y+1): even, white W for x <= a-3
      have hSc := si_W_diag_even c1 c2 c3 c4
      have hpc : ((x + 1) + (y + 1)) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg hSc with h0 | h1
      · rcases (twos_lap_even_iff hSc hpc).1 h0 with hc | hc
        · obtain ⟨d1, d2, -, -⟩ := hc
          exfalso
          omega
        · obtain ⟨d1, d2, d3, d4⟩ := hc
          right
          refine ⟨h0, ?_, ?_, ?_⟩
          · rw [twArrow_W ⟨d1, d2, d3, d4⟩]
            simp [squareCorners]
          · rw [twGrade_W ⟨d1, d2, d3, d4⟩]
            split_ifs <;> omega
          · rw [twGrade_W ⟨d1, d2, d3, d4⟩, twGrade_W hW']
            split_ifs <;> omega
      · exact Or.inl h1


/-- The sub-case `LS` with `h = -1`: the square with its south-west corner `(x - 1, y)`. -/
theorem twos_sub_LS_m1 (k m : ℕ)
    (ih : ∀ m' < m, ∀ c : Site, (twGrade (2 * (k : ℤ) + 4) c).toNat = m' →
      StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) c → laplacian (twF k) c = 0 →
      ForcedEdgeIn (twF k) (StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5)) (fun _ _ => False) c
        (twArrow (2 * (k : ℤ) + 4) c))
    {x y : ℤ} (hm : (twGrade (2 * (k : ℤ) + 4) (x, y)).toNat = m)
    (hcl : TwosClLS (2 * (k : ℤ) + 4) x y) (hh : y - x = -1)
    (hS : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x, y)) :
    ForcedEdgeIn (twF k) (StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5)) (fun _ _ => False) (x, y)
      (twArrow (2 * (k : ℤ) + 4) (x, y)) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hcl
  have hx2 : 2 ≤ x := by omega
  have hcl' : TwosClLS (2 * (k : ℤ) + 4) x y := ⟨d1, d2, d3, d4, d5, d6, d7⟩
  have hw : laplacian (twF k) (x, y) = 0 := (twos_lap_odd_iff hS d1).2 (Or.inl hcl')
  obtain ⟨⟨hu1, hu2⟩, -, hOd⟩ := (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) x y).1 hS
  obtain ⟨ht1, ht2⟩ := hOd d1
  have s1 : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x - 1, y) :=
    (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) (x - 1) y).2
      ⟨⟨by nlinarith, by nlinarith⟩, fun _ => ⟨by nlinarith, by nlinarith⟩, fun h => absurd (by omega) h⟩
  have s2 : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x - 1, y + 1) :=
    (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) (x - 1) (y + 1)).2
      ⟨⟨by nlinarith, by nlinarith⟩, fun h => absurd h (by omega), fun _ => ⟨by nlinarith, by nlinarith⟩⟩
  have s3 : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x, y + 1) :=
    (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) x (y + 1)).2
      ⟨⟨by nlinarith, by nlinarith⟩, fun _ => ⟨by nlinarith, by nlinarith⟩, fun h => absurd (by omega) h⟩
  refine twForced_of_square k m ih hm (p := x - 1) (q := y) (by simp [squareCorners]) hw ?_ ?_ ?_
  · intro c' hc'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl | rfl <;> try simp only [sub_add_cancel]
    · exact s1
    · exact hS
    · exact s2
    · exact s3
  · rw [twArrow_LS hcl']
    simp [squareCorners]
    omega
  · intro c' hc' hne
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl | rfl <;> try simp only [sub_add_cancel] at hne ⊢
    · -- the corner (x-1, y): even, black
      have hpc : ((x - 1) + y) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg s1 with h0 | h1
      · rcases (twos_lap_even_iff s1 hpc).1 h0 with hc | hc
        · obtain ⟨e1, e2, e3, e4⟩ := hc
          exfalso
          omega
        · obtain ⟨e1, e2, e3, e4⟩ := hc
          exfalso
          omega
      · exact Or.inl h1
    · exact absurd rfl hne
    · -- the corner (x-1, y+1): odd, white `LS` (arrow south into the square)
      have hpc : ¬ ((x - 1) + (y + 1)) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg s2 with h0 | h1
      · rcases (twos_lap_odd_iff s2 hpc).1 h0 with hc | hc | hc | hc
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc
          right
          refine ⟨h0, ?_, ?_, ?_⟩
          · rw [twArrow_LS ⟨e1, e2, e3, e4, e5, e6, e7⟩]
            simp [squareCorners]
          · rw [twGrade_LS ⟨e1, e2, e3, e4, e5, e6, e7⟩]
            split_ifs <;> omega
          · rw [twGrade_LS ⟨e1, e2, e3, e4, e5, e6, e7⟩, twGrade_LS hcl']
            split_ifs <;> omega
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc
          exfalso
          omega
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc
          exfalso
          omega
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc
          exfalso
          omega
      · exact Or.inl h1
    · -- the corner (x, y+1): even, black
      have hpc : (x + (y + 1)) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg s3 with h0 | h1
      · rcases (twos_lap_even_iff s3 hpc).1 h0 with hc | hc
        · obtain ⟨e1, e2, e3, e4⟩ := hc
          exfalso
          omega
        · obtain ⟨e1, e2, e3, e4⟩ := hc
          exfalso
          omega
      · exact Or.inl h1



/-- The sub-case `LS` with `h ≠ -1`: the square with its south-west corner `z`. -/
theorem twos_sub_LS (k m : ℕ)
    (ih : ∀ m' < m, ∀ c : Site, (twGrade (2 * (k : ℤ) + 4) c).toNat = m' →
      StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) c → laplacian (twF k) c = 0 →
      ForcedEdgeIn (twF k) (StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5)) (fun _ _ => False) c
        (twArrow (2 * (k : ℤ) + 4) c))
    {x y : ℤ} (hm : (twGrade (2 * (k : ℤ) + 4) (x, y)).toNat = m)
    (hcl : TwosClLS (2 * (k : ℤ) + 4) x y) (hh : y - x ≠ -1)
    (hS : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x, y)) :
    ForcedEdgeIn (twF k) (StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5)) (fun _ _ => False) (x, y)
      (twArrow (2 * (k : ℤ) + 4) (x, y)) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hcl
  have hcl' : TwosClLS (2 * (k : ℤ) + 4) x y := ⟨d1, d2, d3, d4, d5, d6, d7⟩
  have hw : laplacian (twF k) (x, y) = 0 := (twos_lap_odd_iff hS d1).2 (Or.inl hcl')
  have hh1 : 1 ≤ y - x := by omega
  have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
  obtain ⟨⟨hu1, hu2⟩, -, hOd⟩ := (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) x y).1 hS
  obtain ⟨ht1, ht2⟩ := hOd d1
  have s1 : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x + 1, y) :=
    (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) (x + 1) y).2
      ⟨⟨by nlinarith, by nlinarith⟩, fun _ => ⟨by nlinarith, by nlinarith⟩, fun h => absurd (by omega) h⟩
  have s2 : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x, y + 1) :=
    (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) x (y + 1)).2
      ⟨⟨by nlinarith, by nlinarith⟩, fun _ => ⟨by nlinarith, by nlinarith⟩, fun h => absurd (by omega) h⟩
  have s3 : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x + 1, y + 1) :=
    (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) (x + 1) (y + 1)).2
      ⟨⟨by nlinarith, by nlinarith⟩, fun h => absurd h (by omega), fun _ => ⟨by nlinarith, by nlinarith⟩⟩
  refine twForced_of_square k m ih hm (p := x) (q := y) (by simp [squareCorners]) hw ?_ ?_ ?_
  · intro c' hc'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl | rfl <;> try simp only [sub_add_cancel]
    · exact hS
    · exact s1
    · exact s2
    · exact s3
  · rw [twArrow_LS hcl']
    simp [squareCorners]
    omega
  · intro c' hc' hne
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · -- the corner (x+1, y): even, black
      have hpc : (x + 1 + y) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg s1 with h0 | h1
      · rcases (twos_lap_even_iff s1 hpc).1 h0 with hc | hc
        · obtain ⟨e1, e2, e3, e4⟩ := hc
          exfalso
          omega
        · obtain ⟨e1, e2, e3, e4⟩ := hc
          exfalso
          omega
      · exact Or.inl h1
    · -- the corner (x, y+1): even, black
      have hpc : (x + (y + 1)) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg s2 with h0 | h1
      · rcases (twos_lap_even_iff s2 hpc).1 h0 with hc | hc
        · obtain ⟨e1, e2, e3, e4⟩ := hc
          exfalso
          omega
        · obtain ⟨e1, e2, e3, e4⟩ := hc
          exfalso
          omega
      · exact Or.inl h1
    · -- the corner (x+1, y+1): odd, white `LS` (arrow south into the square)
      have hpc : ¬ (x + 1 + (y + 1)) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg s3 with h0 | h1
      · rcases (twos_lap_odd_iff s3 hpc).1 h0 with hc | hc | hc | hc
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc
          right
          refine ⟨h0, ?_, ?_, ?_⟩
          · rw [twArrow_LS ⟨e1, e2, e3, e4, e5, e6, e7⟩]
            simp [squareCorners]
          · rw [twGrade_LS ⟨e1, e2, e3, e4, e5, e6, e7⟩]
            split_ifs <;> omega
          · rw [twGrade_LS ⟨e1, e2, e3, e4, e5, e6, e7⟩, twGrade_LS hcl']
            split_ifs <;> omega
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc
          exfalso
          omega
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc
          exfalso
          omega
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc
          exfalso
          omega
      · exact Or.inl h1

/-- The sub-case `LN` with `x = a`: the square with its south-west corner `(x-1, y-1)`. -/
theorem twos_sub_LN_a (k m : ℕ)
    (ih : ∀ m' < m, ∀ c : Site, (twGrade (2 * (k : ℤ) + 4) c).toNat = m' →
      StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) c → laplacian (twF k) c = 0 →
      ForcedEdgeIn (twF k) (StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5)) (fun _ _ => False) c
        (twArrow (2 * (k : ℤ) + 4) c))
    {x y : ℤ} (hm : (twGrade (2 * (k : ℤ) + 4) (x, y)).toNat = m)
    (hcl : TwosClLN (2 * (k : ℤ) + 4) x y) (hxa : x = 2 * (k : ℤ) + 4)
    (hS : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x, y)) :
    ForcedEdgeIn (twF k) (StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5)) (fun _ _ => False) (x, y)
      (twArrow (2 * (k : ℤ) + 4) (x, y)) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hcl
  have hcl' : TwosClLN (2 * (k : ℤ) + 4) x y := ⟨d1, d2, d3, d4, d5, d6, d7⟩
  have hw : laplacian (twF k) (x, y) = 0 := (twos_lap_odd_iff hS d1).2 (Or.inr (Or.inl hcl'))
  have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
  obtain ⟨⟨hu1, hu2⟩, -, hOd⟩ := (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) x y).1 hS
  obtain ⟨ht1, ht2⟩ := hOd d1
  have s1 : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x - 1, y - 1) :=
    (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) (x - 1) (y - 1)).2
      ⟨⟨by nlinarith, by nlinarith⟩, fun h => absurd h (by omega), fun _ => ⟨by nlinarith, by nlinarith⟩⟩
  have s2 : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x, y - 1) :=
    (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) x (y - 1)).2
      ⟨⟨by nlinarith, by nlinarith⟩, fun _ => ⟨by nlinarith, by nlinarith⟩, fun h => absurd (by omega) h⟩
  have s3 : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x - 1, y) :=
    (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) (x - 1) y).2
      ⟨⟨by nlinarith, by nlinarith⟩, fun _ => ⟨by nlinarith, by nlinarith⟩, fun h => absurd (by omega) h⟩
  refine twForced_of_square k m ih hm (p := x - 1) (q := y - 1) (by simp [squareCorners]) hw ?_ ?_ ?_
  · intro c' hc'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl | rfl <;> try simp only [sub_add_cancel]
    · exact s1
    · exact s2
    · exact s3
    · exact hS
  · rw [twArrow_LN hcl']
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  · intro c' hc' hne
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl | rfl <;> try simp only [sub_add_cancel] at hne ⊢
    · -- the corner (x-1, y-1): odd, white `LN` (arrow north into the square)
      have hpc : ¬ (x - 1 + (y - 1)) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg s1 with h0 | h1
      · rcases (twos_lap_odd_iff s1 hpc).1 h0 with hc | hc | hc | hc
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc
          exfalso
          omega
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc
          right
          refine ⟨h0, ?_, ?_, ?_⟩
          · rw [twArrow_LN ⟨e1, e2, e3, e4, e5, e6, e7⟩]
            simp [squareCorners]
          · rw [twGrade_LN ⟨e1, e2, e3, e4, e5, e6, e7⟩]
            split_ifs <;> omega
          · rw [twGrade_LN ⟨e1, e2, e3, e4, e5, e6, e7⟩, twGrade_LN hcl']
            split_ifs <;> omega
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc
          exfalso
          omega
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc
          exfalso
          omega
      · exact Or.inl h1
    · -- the corner (x, y-1): even, black
      have hpc : (x + (y - 1)) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg s2 with h0 | h1
      · rcases (twos_lap_even_iff s2 hpc).1 h0 with hc | hc
        · obtain ⟨e1, e2, e3, e4⟩ := hc
          exfalso
          omega
        · obtain ⟨e1, e2, e3, e4⟩ := hc
          exfalso
          omega
      · exact Or.inl h1
    · -- the corner (x-1, y): even, white `E` for x = a (arrow east, into the square)
      have hpc : (x - 1 + y) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg s3 with h0 | h1
      · rcases (twos_lap_even_iff s3 hpc).1 h0 with hc | hc
        · obtain ⟨e1, e2, e3, e4⟩ := hc
          right
          refine ⟨h0, ?_, ?_, ?_⟩
          · rw [twArrow_E ⟨e1, e2, e3, e4⟩]
            simp [squareCorners]
          · rw [twGrade_E ⟨e1, e2, e3, e4⟩]
            split_ifs <;> omega
          · rw [twGrade_E ⟨e1, e2, e3, e4⟩, twGrade_LN hcl']
            split_ifs <;> omega
        · obtain ⟨e1, e2, e3, e4⟩ := hc
          exfalso
          omega
      · exact Or.inl h1
    · exact absurd rfl hne

/-- The sub-case `LN` with `x ≠ a`: the square with its south-west corner `(x, y-1)`. -/
theorem twos_sub_LN (k m : ℕ)
    (ih : ∀ m' < m, ∀ c : Site, (twGrade (2 * (k : ℤ) + 4) c).toNat = m' →
      StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) c → laplacian (twF k) c = 0 →
      ForcedEdgeIn (twF k) (StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5)) (fun _ _ => False) c
        (twArrow (2 * (k : ℤ) + 4) c))
    {x y : ℤ} (hm : (twGrade (2 * (k : ℤ) + 4) (x, y)).toNat = m)
    (hcl : TwosClLN (2 * (k : ℤ) + 4) x y) (hxa : x ≠ 2 * (k : ℤ) + 4)
    (hS : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x, y)) :
    ForcedEdgeIn (twF k) (StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5)) (fun _ _ => False) (x, y)
      (twArrow (2 * (k : ℤ) + 4) (x, y)) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hcl
  have hcl' : TwosClLN (2 * (k : ℤ) + 4) x y := ⟨d1, d2, d3, d4, d5, d6, d7⟩
  have hw : laplacian (twF k) (x, y) = 0 := (twos_lap_odd_iff hS d1).2 (Or.inr (Or.inl hcl'))
  have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
  have hx1 : x ≤ 2 * (k : ℤ) + 3 := by omega
  have hax : (2 * (k : ℤ) + 4) * x ≤ (2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 3) :=
    mul_le_mul_of_nonneg_left hx1 (by omega)
  have hax' : (2 * (k : ℤ) + 5) * x ≤ (2 * (k : ℤ) + 5) * (2 * (k : ℤ) + 3) :=
    mul_le_mul_of_nonneg_left hx1 (by omega)
  obtain ⟨⟨hu1, hu2⟩, -, hOd⟩ := (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) x y).1 hS
  obtain ⟨ht1, ht2⟩ := hOd d1
  have s1 : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x, y - 1) :=
    (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) x (y - 1)).2
      ⟨⟨by nlinarith, by nlinarith⟩, fun _ => ⟨by nlinarith, by nlinarith⟩, fun h => absurd (by omega) h⟩
  have s2 : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x + 1, y - 1) :=
    (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) (x + 1) (y - 1)).2
      ⟨⟨by nlinarith [hax, hax', d3, hk0], by nlinarith [hax, hax', d3, hk0]⟩, fun h => absurd h (by omega),
        fun _ => ⟨by nlinarith [hax, hax', d3, hk0], by nlinarith [hax, hax', d3, hk0]⟩⟩
  have s3 : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x + 1, y) :=
    (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) (x + 1) y).2
      ⟨⟨by nlinarith [hax, hax', d3, hk0], by nlinarith [hax, hax', d3, hk0]⟩,
        fun _ => ⟨by nlinarith [hax, hax', d3, hk0], by nlinarith [hax, hax', d3, hk0]⟩, fun h => absurd (by omega) h⟩
  refine twForced_of_square k m ih hm (p := x) (q := y - 1) (by simp [squareCorners]) hw ?_ ?_ ?_
  · intro c' hc'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl | rfl <;> try simp only [sub_add_cancel]
    · exact s1
    · exact s2
    · exact hS
    · exact s3
  · rw [twArrow_LN hcl']
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  · intro c' hc' hne
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl | rfl <;> try simp only [sub_add_cancel] at hne ⊢
    · -- the corner (x, y-1): even, black
      have hpc : (x + (y - 1)) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg s1 with h0 | h1
      · rcases (twos_lap_even_iff s1 hpc).1 h0 with hc | hc
        · obtain ⟨e1, e2, e3, e4⟩ := hc
          exfalso
          omega
        · obtain ⟨e1, e2, e3, e4⟩ := hc
          exfalso
          omega
      · exact Or.inl h1
    · -- the corner (x+1, y-1): odd, white `LN` (arrow north, to (x+1, y) in the square)
      have hpc : ¬ (x + 1 + (y - 1)) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg s2 with h0 | h1
      · rcases (twos_lap_odd_iff s2 hpc).1 h0 with hc | hc | hc | hc
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc
          exfalso
          omega
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc
          right
          refine ⟨h0, ?_, ?_, ?_⟩
          · rw [twArrow_LN ⟨e1, e2, e3, e4, e5, e6, e7⟩]
            simp [squareCorners]
          · rw [twGrade_LN ⟨e1, e2, e3, e4, e5, e6, e7⟩]
            split_ifs <;> omega
          · rw [twGrade_LN ⟨e1, e2, e3, e4, e5, e6, e7⟩, twGrade_LN hcl']
            split_ifs <;> omega
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc
          exfalso
          omega
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc
          exfalso
          omega
      · exact Or.inl h1
    · exact absurd rfl hne
    · -- the corner (x+1, y): even, black
      have hpc : (x + 1 + y) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg s3 with h0 | h1
      · rcases (twos_lap_even_iff s3 hpc).1 h0 with hc | hc
        · obtain ⟨e1, e2, e3, e4⟩ := hc
          exfalso
          omega
        · obtain ⟨e1, e2, e3, e4⟩ := hc
          exfalso
          omega
      · exact Or.inl h1

/-- The sub-case `US` with `x = 0`: the square with its south-west corner `z`. -/
theorem twos_sub_US_0 (k m : ℕ)
    (ih : ∀ m' < m, ∀ c : Site, (twGrade (2 * (k : ℤ) + 4) c).toNat = m' →
      StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) c → laplacian (twF k) c = 0 →
      ForcedEdgeIn (twF k) (StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5)) (fun _ _ => False) c
        (twArrow (2 * (k : ℤ) + 4) c))
    {x y : ℤ} (hm : (twGrade (2 * (k : ℤ) + 4) (x, y)).toNat = m)
    (hcl : TwosClUS (2 * (k : ℤ) + 4) x y) (hx0 : x = 0)
    (hS : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x, y)) :
    ForcedEdgeIn (twF k) (StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5)) (fun _ _ => False) (x, y)
      (twArrow (2 * (k : ℤ) + 4) (x, y)) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hcl
  have hcl' : TwosClUS (2 * (k : ℤ) + 4) x y := ⟨d1, d2, d3, d4, d5, d6, d7⟩
  have hw : laplacian (twF k) (x, y) = 0 := (twos_lap_odd_iff hS d1).2 (Or.inr (Or.inr (Or.inl hcl')))
  obtain ⟨⟨hu1, hu2⟩, -, hOd⟩ := (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) x y).1 hS
  obtain ⟨ht1, ht2⟩ := hOd d1
  have s1 : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x + 1, y) :=
    (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) (x + 1) y).2
      ⟨⟨by nlinarith, by nlinarith⟩, fun _ => ⟨by nlinarith, by nlinarith⟩, fun h => absurd (by omega) h⟩
  have s2 : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x, y + 1) :=
    (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) x (y + 1)).2
      ⟨⟨by nlinarith, by nlinarith⟩, fun _ => ⟨by nlinarith, by nlinarith⟩, fun h => absurd (by omega) h⟩
  have s3 : StrictInterior (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 5) (x + 1, y + 1) :=
    (strictInterior_twos_iff (a := 2 * (k : ℤ) + 4) (by ring) (by ring) (x + 1) (y + 1)).2
      ⟨⟨by nlinarith, by nlinarith⟩, fun h => absurd h (by omega), fun _ => ⟨by nlinarith, by nlinarith⟩⟩
  refine twForced_of_square k m ih hm (p := x) (q := y) (by simp [squareCorners]) hw ?_ ?_ ?_
  · intro c' hc'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl | rfl <;> try simp only [sub_add_cancel]
    · exact hS
    · exact s1
    · exact s2
    · exact s3
  · rw [twArrow_US hcl']
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  · intro c' hc' hne
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl | rfl <;> try simp only [sub_add_cancel] at hne ⊢
    · exact absurd rfl hne
    · -- the corner (x+1, y): even, white `W` (arrow west, into the square) when y = a+1
      have hpc : (x + 1 + y) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg s1 with h0 | h1
      · rcases (twos_lap_even_iff s1 hpc).1 h0 with hc | hc
        · obtain ⟨e1, e2, e3, e4⟩ := hc
          exfalso
          omega
        · obtain ⟨e1, e2, e3, e4⟩ := hc
          right
          refine ⟨h0, ?_, ?_, ?_⟩
          · rw [twArrow_W ⟨e1, e2, e3, e4⟩]
            simp [squareCorners]
          · rw [twGrade_W ⟨e1, e2, e3, e4⟩]
            split_ifs <;> omega
          · rw [twGrade_W ⟨e1, e2, e3, e4⟩, twGrade_US hcl']
            split_ifs <;> omega
      · exact Or.inl h1
    · -- the corner (x, y+1): even, black
      have hpc : (x + (y + 1)) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg s2 with h0 | h1
      · rcases (twos_lap_even_iff s2 hpc).1 h0 with hc | hc
        · obtain ⟨e1, e2, e3, e4⟩ := hc
          exfalso
          omega
        · obtain ⟨e1, e2, e3, e4⟩ := hc
          exfalso
          omega
      · exact Or.inl h1
    · -- the corner (x+1, y+1): odd, white `US` (arrow south, to (x+1, y) in the square)
      have hpc : ¬ (x + 1 + (y + 1)) % 2 = 0 := by omega
      rcases twos_lap_zero_or_neg s3 with h0 | h1
      · rcases (twos_lap_odd_iff s3 hpc).1 h0 with hc | hc | hc | hc
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc
          exfalso
          omega
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc
          exfalso
          omega
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc
          right
          refine ⟨h0, ?_, ?_, ?_⟩
          · rw [twArrow_US ⟨e1, e2, e3, e4, e5, e6, e7⟩]
            simp [squareCorners]
          · rw [twGrade_US ⟨e1, e2, e3, e4, e5, e6, e7⟩]
            split_ifs <;> omega
          · rw [twGrade_US ⟨e1, e2, e3, e4, e5, e6, e7⟩, twGrade_US hcl']
            split_ifs <;> omega
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hc
          exfalso
          omega
      · exact Or.inl h1

end FLatticePaper.W1Twos
