import FLatticePaper.Tiles.PairEvenRefl

/-! Task 53, item 2 (covering reduction), section 13 (end): the cover of the cell of the even child `X = 2P + Q` and `propEven`.

For flag false (`δ = +1`) the cell `[0,1]²` is covered by six boxes, each owned by one source of `evenChildS false`
(`F1`, `RF2`, `F3L`, `F3H`, `RF4L`, `RF4H`). For flag true (`δ = −1`) the cover uses `T1`, `RT2`, `T3L`, `T3H`, `RT4L`, `RT4H`.
`propEven` follows from `quotientCover_of_cell`. -/

namespace FLatticePaper.Tiles.PairEvenCover

open FLatticePaper.Farey FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SiteCell FLatticePaper.Construction
  FLatticePaper.Tiles.PairEvenRefl FLatticePaper.Tiles.PairEvenW0Q FLatticePaper.Tiles.PairEvenW0P
  FLatticePaper.Tiles.PairEvenW1P FLatticePaper.Tiles.PairEvenW1Q

/-- A shifted H-set membership, from the point `w = z − v` with `InH f w`. -/
theorem mem_shift_of {f : Fraction} (z v w : ℤ × ℤ) (hw : z - v = w) (h : InH f w) :
    z ∈ shiftS (HSet f) v :=
  ⟨w, h, by show w + v = z; rw [← hw, sub_add_cancel]⟩

/-- The six boxes of the flag-false cover of `[0,1]²`. -/
theorem cover_F (u v α β : ℚ) :
    (u ≤ β ∧ v ≤ β) ∨ (α ≤ u ∧ α ≤ v) ∨ (β ≤ u ∧ 2 * v ≤ α) ∨ (β ≤ u ∧ α ≤ 2 * v ∧ v ≤ α) ∨
      (u ≤ α ∧ β ≤ v ∧ 2 * v ≤ 2 - α) ∨ (u ≤ α ∧ 2 - α ≤ 2 * v) := by
  rcases le_total u β with h1 | h1
  · rcases le_total v β with h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · rcases le_total u α with h3 | h3
      · rcases le_total (2 * v) (2 - α) with h4 | h4
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, h2, h4⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h3, h4⟩))))
      · exact Or.inr (Or.inl ⟨h3, by linarith⟩)
  · rcases le_total (2 * v) α with h2 | h2
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
    · rcases le_total v α with h3 | h3
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩)))
      · rcases le_total α u with h4 | h4
        · exact Or.inr (Or.inl ⟨h4, by linarith⟩)
        · rcases le_total (2 * v) (2 - α) with h5 | h5
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h4, by linarith, h5⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h4, h5⟩))))

/-- The six boxes of the flag-true cover of `[0,1]²`. -/
theorem cover_T (u v α β : ℚ) :
    (α ≤ u ∧ v ≤ β) ∨ (u ≤ β ∧ α ≤ v) ∨ (u ≤ α ∧ 2 * v ≤ α) ∨ (u ≤ α ∧ α ≤ 2 * v ∧ v ≤ α) ∨
      (β ≤ u ∧ β ≤ v ∧ 2 * v ≤ 2 - α) ∨ (β ≤ u ∧ 2 - α ≤ 2 * v) := by
  rcases le_total u α with h1 | h1
  · rcases le_total (2 * v) α with h2 | h2
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
    · rcases le_total v α with h3 | h3
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩)))
      · rcases le_total u β with h4 | h4
        · exact Or.inr (Or.inl ⟨h4, by linarith⟩)
        · rcases le_total (2 * v) (2 - α) with h5 | h5
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h4, by linarith, h5⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h4, h5⟩))))
  · rcases le_total v β with h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · rcases le_total u β with h3 | h3
      · exact Or.inr (Or.inl ⟨h3, by linarith⟩)
      · rcases le_total (2 * v) (2 - α) with h4 | h4
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, h2, h4⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h3, h4⟩))))

/-- **Membership, flag false.** Every integer point of the cell lies in `evenChildS false`. -/
theorem memF (d n e r : ℤ) (hd : 2 ≤ d) (hdn : d ≠ 2 * n ∨ 2 * d < e) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (u v α β : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * (d : ℚ) + e) + v * ((2 * (n : ℚ) + r) - (2 * (d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * (n : ℚ) + r) + v * ((2 * (d : ℚ) + e) + (2 * (n : ℚ) + r)))
    (hα : α * (2 * (d : ℚ) + e) = 2 * (d : ℚ)) (hβ : β * (2 * (d : ℚ) + e) = (e : ℚ))
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    z ∈ evenChildS false (HSet ⟨n, d⟩) (HSet ⟨r, e⟩) ⟨n, d⟩ ⟨r, e⟩ := by
  have hcov := cover_F u v α β
  rcases hcov with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · simp only [evenChildS, Set.mem_union]
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (?_)))))
    exact F1_box d n e r hd hn hnd hr hre hdet hodd heven z u v β hz1 hz2 hβ hu0 h1 hv0 h2
  · simp only [evenChildS, Set.mem_union]
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (?_)))))
    exact mem_shift_of (f := ⟨r, e⟩) z (texV1Odd ⟨n, d⟩ + (texV2 ⟨n, d⟩ + texV2 ⟨n, d⟩)) ((z.1 - 2 * n, z.2 - (4 * n + 2 * d)))
      (by ext <;> simp [texV1Odd, texV2] <;> try ring)
      (RF2 d n e r hd hn hnd hr hre hdet hodd heven z u v α β hz1 hz2 hα hβ h1 hu1 h2 hv1)
  · simp only [evenChildS, Set.mem_union]
    refine Or.inl (Or.inl (Or.inl (Or.inr (?_))))
    exact mem_shift_of (f := ⟨n, d⟩) z (texV1Even ⟨r, e⟩) ((z.1 - e, z.2 - r))
      (by ext <;> simp [texV1Even])
      (F3L_box d n e r hn hnd hr hre hdet hodd heven z u v α β hz1 hz2 hα hβ h1 hu1 hv0 h2)
  · simp only [evenChildS, Set.mem_union]
    refine Or.inl (Or.inl (Or.inr (?_)))
    exact mem_shift_of (f := ⟨n, d⟩) z (texV1Even ⟨r, e⟩ + texV2 ⟨n, d⟩) ((z.1 - (e + (n - d)), z.2 - (r + (n + d))))
      (by ext <;> simp [texV1Even, texV2])
      (F3H_box d n e r hn hnd hdn hr hre hdet hodd heven z u v α β hz1 hz2 hα hβ h1 hu1 h2 h3)
  · simp only [evenChildS, Set.mem_union]
    refine Or.inl (Or.inr (?_))
    exact mem_shift_of (f := ⟨n, d⟩) z (texV2 ⟨r, e⟩) ((z.1 - (r - e), z.2 - (r + e)))
      (by ext <;> simp [texV2])
      (RF4L d n e r hdn hn hnd hr hre hdet hodd heven z u v α β hz1 hz2 hα hβ hu0 h1 h2 h3)
  · simp only [evenChildS, Set.mem_union]
    refine Or.inr (?_)
    exact mem_shift_of (f := ⟨n, d⟩) z (texV2 ⟨r, e⟩ + texV2 ⟨n, d⟩) ((z.1 - (r - e + n - d), z.2 - (r + e + n + d)))
      (by ext <;> simp [texV2] <;> try ring)
      (RF4H d n e r hn hnd hr hre hdet hodd heven z u v α β hz1 hz2 hα hβ hu0 h1 h2 hv1)

/-- **Membership, flag true.** Every integer point of the cell lies in `evenChildS true`. -/
theorem memT (d n e r : ℤ) (hd : 2 ≤ d) (hdn : d ≠ 2 * n ∨ 2 * d < e) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (u v α β : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * (d : ℚ) + e) + v * ((2 * (n : ℚ) + r) - (2 * (d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * (n : ℚ) + r) + v * ((2 * (d : ℚ) + e) + (2 * (n : ℚ) + r)))
    (hα : α * (2 * (d : ℚ) + e) = 2 * (d : ℚ)) (hβ : β * (2 * (d : ℚ) + e) = (e : ℚ))
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    z ∈ evenChildS true (HSet ⟨n, d⟩) (HSet ⟨r, e⟩) ⟨n, d⟩ ⟨r, e⟩ := by
  have hcov := cover_T u v α β
  rcases hcov with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · simp only [evenChildS, Set.mem_union]
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (?_)))))
    exact mem_shift_of (f := ⟨r, e⟩) z (texV1Odd ⟨n, d⟩) ((z.1 - 2 * d, z.2 - 2 * n))
      (by ext <;> simp [texV1Odd])
      (T1_box d n e r hd hn hnd hr hre hdet heven z u v α β hz1 hz2 hα hβ h1 hu1 hv0 h2)
  · simp only [evenChildS, Set.mem_union]
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (?_)))))
    exact mem_shift_of (f := ⟨r, e⟩) z (texV2 ⟨n, d⟩ + texV2 ⟨n, d⟩) ((z.1 - 2 * (n - d), z.2 - 2 * (n + d)))
      (by ext <;> simp [texV2] <;> try ring)
      (RT2 d n e r hd hn hnd hr hre hdet heven z u v α β hz1 hz2 hα hβ hu0 h1 h2 hv1)
  · simp only [evenChildS, Set.mem_union]
    refine Or.inl (Or.inl (Or.inl (Or.inr (?_))))
    exact T3L_box d n e r hn hnd hr hre hdet hodd heven z u v α hz1 hz2 hα hu0 h1 hv0 h2
  · simp only [evenChildS, Set.mem_union]
    refine Or.inl (Or.inl (Or.inr (?_)))
    exact mem_shift_of (f := ⟨n, d⟩) z (texV2 ⟨n, d⟩) ((z.1 - (n - d), z.2 - (n + d)))
      (by ext <;> simp [texV2])
      (T3H_box d n e r hn hnd hdn hr hre hdet hodd heven z u v α hz1 hz2 hα hu0 h1 h2 h3)
  · simp only [evenChildS, Set.mem_union]
    refine Or.inl (Or.inr (?_))
    exact mem_shift_of (f := ⟨n, d⟩) z (texV1Even ⟨r, e⟩ + texV2 ⟨r, e⟩) ((z.1 - r, z.2 - (2 * r + e)))
      (by ext <;> (simp [texV1Even, texV2]; try ring))
      (RT4L d n e r hdn hn hnd hr hre hdet hodd heven z u v α β hz1 hz2 hα hβ h1 hu1 h2 h3)
  · simp only [evenChildS, Set.mem_union]
    refine Or.inr (?_)
    exact mem_shift_of (f := ⟨n, d⟩) z (texV1Even ⟨r, e⟩ + texV2 ⟨r, e⟩ + texV2 ⟨n, d⟩) ((z.1 - (r + n - d), z.2 - (2 * r + e + n + d)))
      (by ext <;> simp [texV1Even, texV2] <;> try ring)
      (RT4H d n e r hn hnd hr hre hdet hodd heven z u v α β hz1 hz2 hα hβ h1 hu1 h2 hv1)

/-- The cell of `X = 2P + Q` (with `μ_X = 1`): the cell coordinates of an integer point. -/
theorem inCell_even (d n e r : ℤ) (heven : (e + r) % 2 = 0) (z : ℤ × ℤ)
    (h : InCell (perU ⟨2 * n + r, 2 * d + e⟩) (perV ⟨2 * n + r, 2 * d + e⟩) z) :
    ∃ u v : ℚ, 0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 ∧
      (z.1 : ℚ) - 1 / 2 = u * (2 * (d : ℚ) + e) + v * ((2 * (n : ℚ) + r) - (2 * (d : ℚ) + e)) ∧
      (z.2 : ℚ) + 1 / 2 = u * (2 * (n : ℚ) + r) + v * ((2 * (d : ℚ) + e) + (2 * (n : ℚ) + r)) := by
  obtain ⟨u, v, hu0, hu1, hv0, hv1, e1, e2⟩ := h
  have hm : muOf (⟨2 * n + r, 2 * d + e⟩ : Fraction) = 1 := by
    show (if (2 * n + r + (2 * d + e)) % 2 = 1 then 2 else 1) = 1
    rw [if_neg (by omega)]
  simp only [perU, perV, hm] at e1 e2
  push_cast at e1 e2
  exact ⟨u, v, hu0, hu1.le, hv0, hv1.le, by linear_combination e1, by linear_combination e2⟩

/-- The even parent of the pair `(⟨n,d⟩, ⟨r,e⟩)` is `2P + Q`. -/
theorem parents_even_eq (d n e r : ℤ) :
    (Parents.mk (⟨n, d⟩ : Fraction) ⟨r, e⟩).current .even = ⟨2 * n + r, 2 * d + e⟩ := by
  simp [Parents.current, Parents.combine]

/-- The orientation flag of `(⟨n,d⟩, ⟨r,e⟩)` is `false` when `dr − ne = 1`. -/
theorem flag_false (d n e r : ℤ) (hdet : d * r - n * e = 1) :
    decide ((⟨n, d⟩ : Fraction).det ⟨r, e⟩ = 1) = false := by
  have h : (⟨n, d⟩ : Fraction).det ⟨r, e⟩ = -1 := by
    unfold Fraction.det
    linear_combination (-1 : ℤ) * hdet
  rw [h]
  decide

/-- The orientation flag of `(⟨n,d⟩, ⟨r,e⟩)` is `true` when `dr − ne = −1`. -/
theorem flag_true (d n e r : ℤ) (hdet : d * r - n * e = -1) :
    decide ((⟨n, d⟩ : Fraction).det ⟨r, e⟩ = 1) = true := by
  have h : (⟨n, d⟩ : Fraction).det ⟨r, e⟩ = 1 := by
    unfold Fraction.det
    linear_combination (-1 : ℤ) * hdet
  rw [h]
  decide

/-- **`propEven`, flag false.** The even child `evenChildS` of the pair covers the deck of `X = 2P + Q`. -/
theorem propEven_F (d n e r : ℤ) (hd : 2 ≤ d) (hdn : d ≠ 2 * n ∨ 2 * d < e) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    QuotientCover (evenChildS false (HSet ⟨n, d⟩) (HSet ⟨r, e⟩) ⟨n, d⟩ ⟨r, e⟩)
      (perU ⟨2 * n + r, 2 * d + e⟩) (perV ⟨2 * n + r, 2 * d + e⟩) := by
  have hDi : (0 : ℤ) < 2 * d + e := by omega
  have hD : (0 : ℚ) < 2 * (d : ℚ) + e := by exact_mod_cast hDi
  obtain ⟨α, hα⟩ : ∃ α : ℚ, α * (2 * (d : ℚ) + e) = 2 * (d : ℚ) :=
    ⟨2 * (d : ℚ) / (2 * (d : ℚ) + e), div_mul_cancel₀ _ (ne_of_gt hD)⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℚ, β * (2 * (d : ℚ) + e) = (e : ℚ) :=
    ⟨(e : ℚ) / (2 * (d : ℚ) + e), div_mul_cancel₀ _ (ne_of_gt hD)⟩
  refine quotientCover_of_cell ⟨2 * n + r, 2 * d + e⟩ ?_ ?_ _ ?_
  · show 0 < 2 * n + r
    omega
  · show 2 * n + r < 2 * d + e
    omega
  · intro z hz
    obtain ⟨u, v, hu0, hu1, hv0, hv1, hz1, hz2⟩ := inCell_even d n e r heven z hz
    exact memF d n e r hd hdn hn hnd hr hre hdet hodd heven z u v α β hz1 hz2 hα hβ hu0 hu1 hv0 hv1

/-- **`propEven`, flag true.** -/
theorem propEven_T (d n e r : ℤ) (hd : 2 ≤ d) (hdn : d ≠ 2 * n ∨ 2 * d < e) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    QuotientCover (evenChildS true (HSet ⟨n, d⟩) (HSet ⟨r, e⟩) ⟨n, d⟩ ⟨r, e⟩)
      (perU ⟨2 * n + r, 2 * d + e⟩) (perV ⟨2 * n + r, 2 * d + e⟩) := by
  have hDi : (0 : ℤ) < 2 * d + e := by omega
  have hD : (0 : ℚ) < 2 * (d : ℚ) + e := by exact_mod_cast hDi
  obtain ⟨α, hα⟩ : ∃ α : ℚ, α * (2 * (d : ℚ) + e) = 2 * (d : ℚ) :=
    ⟨2 * (d : ℚ) / (2 * (d : ℚ) + e), div_mul_cancel₀ _ (ne_of_gt hD)⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℚ, β * (2 * (d : ℚ) + e) = (e : ℚ) :=
    ⟨(e : ℚ) / (2 * (d : ℚ) + e), div_mul_cancel₀ _ (ne_of_gt hD)⟩
  refine quotientCover_of_cell ⟨2 * n + r, 2 * d + e⟩ ?_ ?_ _ ?_
  · show 0 < 2 * n + r
    omega
  · show 2 * n + r < 2 * d + e
    omega
  · intro z hz
    obtain ⟨u, v, hu0, hu1, hv0, hv1, hz1, hz2⟩ := inCell_even d n e r heven z hz
    exact memT d n e r hd hdn hn hnd hr hre hdet hodd heven z u v α β hz1 hz2 hα hβ hu0 hu1 hv0 hv1

/-- `propEven` in the form of `PairHyps`, flag false (the parent `X` is `2P + Q`). -/
theorem propEven_parents_F (d n e r : ℤ) (hd : 2 ≤ d) (hdn : d ≠ 2 * n ∨ 2 * d < e) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    QuotientCover (evenChildS (decide ((⟨n, d⟩ : Fraction).det ⟨r, e⟩ = 1)) (HSet ⟨n, d⟩) (HSet ⟨r, e⟩) ⟨n, d⟩ ⟨r, e⟩)
      (perU ((Parents.mk ⟨n, d⟩ ⟨r, e⟩).current .even)) (perV ((Parents.mk ⟨n, d⟩ ⟨r, e⟩).current .even)) := by
  rw [flag_false d n e r hdet, parents_even_eq d n e r]
  exact propEven_F d n e r hd hdn hn hnd hr hre hdet hodd heven

/-- `propEven` in the form of `PairHyps`, flag true. -/
theorem propEven_parents_T (d n e r : ℤ) (hd : 2 ≤ d) (hdn : d ≠ 2 * n ∨ 2 * d < e) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    QuotientCover (evenChildS (decide ((⟨n, d⟩ : Fraction).det ⟨r, e⟩ = 1)) (HSet ⟨n, d⟩) (HSet ⟨r, e⟩) ⟨n, d⟩ ⟨r, e⟩)
      (perU ((Parents.mk ⟨n, d⟩ ⟨r, e⟩).current .even)) (perV ((Parents.mk ⟨n, d⟩ ⟨r, e⟩).current .even)) := by
  rw [flag_true d n e r hdet, parents_even_eq d n e r]
  exact propEven_T d n e r hd hdn hn hnd hr hre hdet hodd heven

end FLatticePaper.Tiles.PairEvenCover
