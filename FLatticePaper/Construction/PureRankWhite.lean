import FLatticePaper.Construction.PureRank

/-!
# The white predicate of the Q_minus edge rule, and the Q_minus gate (task 118, W1 base, step (iii))

The edge predicate of prove_rank.py, transcribed: `starV`, `lapV`, `corrV` (the corner correction), `cgAt` (the corner
white), `freeHit`/`cgHit`/`hasWhite`, and `Retained` (parity-axis, and no white or a matching hit). The exclusion lemmas show
that a unit edge outside the listed directions of each family is not retained; the family lemmas then assemble the gate
`qminus_gate`: every rank of a retained unit edge target is below `qRank` of the source.
-/

namespace FLatticePaper.PureRank

open Classical

/-- The corner correction of the edge predicate (prove_rank.py `corr`). -/
def corrV (d X Y : ℤ) : ℤ :=
  min (X - 1) 0 + (if (X = 0 ∧ Y = 0) ∨ (X = 2 ∧ Y = d + 1) then 1 else 0)

/-- The Laplacian of the correction, by parity (prove_rank.py `lap`). -/
def lapV (d X Y : ℤ) : ℤ :=
  if (X + Y) % 2 = 0 then corrV d (X - 1) Y + corrV d (X + 1) Y - 2 * corrV d X Y
  else -1 + corrV d X (Y - 1) + corrV d X (Y + 1) - 2 * corrV d X Y

/-- The star predicate (prove_rank.py `star`). -/
def starV (d X Y : ℤ) : Prop :=
  NativeP d (X, Y) ∧
    (((X + Y) % 2 = 0 ∧ NativeP d (X - 1, Y) ∧ NativeP d (X + 1, Y)) ∨
     ((X + Y) % 2 ≠ 0 ∧ NativeP d (X, Y - 1) ∧ NativeP d (X, Y + 1)))

/-- The source `(X,Y)` has no free translate by an alias. -/
def noFree (d X Y : ℤ) : Prop := ∀ i j, IsAlias i j → ¬ IsFreeP d (shiftP d (X, Y) i j)

/-- The corner-type white at a translate `q` of the source (prove_rank.py `cg`). -/
def cgAt (d X Y : ℤ) (q : Pt) : Prop :=
  starV d q.1 q.2 ∧ lapV d q.1 q.2 = 0 ∧ (q.1 + q.2) % 2 = 0 ∧ (q.1 ≤ 0 ∨ 2 ≤ q.1) ∧ noFree d X Y

/-- A translate by `(i,j)` of an interior point has no free translate. -/
theorem interior_noFree (d x y : ℤ) (hd : 3 ≤ d) (hn : NativeP d (x, y)) (hf : ¬ IsFreeP d (x, y))
    (hy : y ≤ d) (h4 : x + y ≠ d + 2) (h5 : ¬ (x = d ∧ y = 1)) : noFree d x y := by
  intro i j hij hfree
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hij
  unfold NativeP at hn
  simp only [Prod.mk.injEq] at hn
  unfold IsFreeP IsHc IsVc at hf hfree
  simp only [shiftP, Prod.mk.injEq] at hf hfree
  interval_cases i <;> interval_cases j <;> omega

/-- The corner white at the origin of an interior even point with `x ≤ 0`. -/
theorem cg_origin_left (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y))
    (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (h4 : x + y ≠ d + 2) (h5 : ¬ (x = d ∧ y = 1))
    (hpar : (x + y) % 2 = 0) (hx : x ≤ 0) : cgAt d x y (x, y) := by
  have hnf := interior_noFree d x y hd hn hf hy h4 h5
  have hb : 3 - d ≤ x ∧ 1 ≤ y ∧ 2 ≤ x + y ∧ x + y ≤ d := by
    unfold NativeP at hn
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hn hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  refine ⟨?_, ?_, hpar, Or.inl hx, hnf⟩
  · refine ⟨hn, Or.inl ⟨hpar, ?_, ?_⟩⟩
    · unfold NativeP
      simp only [Prod.mk.injEq]
      omega
    · unfold NativeP
      simp only [Prod.mk.injEq]
      omega
  · unfold lapV corrV
    split_ifs <;> omega


/-- The corner correction at a point with positive first coordinate is an equality indicator. -/
theorem corrV_pos (d a b : ℤ) (ha : 1 ≤ a) :
    corrV d a b = if a = 2 ∧ b = d + 1 then 1 else 0 := by
  unfold corrV
  rw [min_eq_right (show (0:ℤ) ≤ a - 1 by omega)]
  split_ifs <;> omega

/-- The Laplacian at a point with first coordinate at least `2`, as indicators. -/
theorem lapV_ge2 (d a b : ℤ) (ha : 2 ≤ a) :
    lapV d a b =
      if (a + b) % 2 = 0 then
        (if a - 1 = 2 ∧ b = d + 1 then 1 else 0) + (if a + 1 = 2 ∧ b = d + 1 then 1 else 0)
          - 2 * (if a = 2 ∧ b = d + 1 then 1 else 0)
      else
        -1 + (if a = 2 ∧ b - 1 = d + 1 then 1 else 0) + (if a = 2 ∧ b + 1 = d + 1 then 1 else 0)
          - 2 * (if a = 2 ∧ b = d + 1 then 1 else 0) := by
  unfold lapV
  simp only [corrV_pos d (a - 1) b (by omega), corrV_pos d (a + 1) b (by omega),
    corrV_pos d a b (by omega), corrV_pos d a (b - 1) (by omega), corrV_pos d a (b + 1) (by omega)]

set_option maxHeartbeats 400000 in
/-- No corner white with `a ≥ 2` at any alias translate of an interior even point with `x ≤ 0`. -/
theorem no_cg_right_of_left (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y))
    (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d)
    (hpar : (x + y) % 2 = 0) (hx : x ≤ 0) (i j : ℤ) (hij : IsAlias i j)
    (hcg : cgAt d x y (shiftP d (x, y) i j)) (hq : 2 ≤ (shiftP d (x, y) i j).1) : False := by
  have hb : 3 - d ≤ x ∧ 1 ≤ y ∧ 2 ≤ x + y ∧ x + y ≤ d := by
    unfold NativeP at hn
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hn hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hij
  obtain ⟨hstar, hlap, -, -, -⟩ := hcg
  clear hn hf
  rw [lapV_ge2 d _ _ hq] at hlap
  unfold starV NativeP at hstar
  interval_cases i <;> interval_cases j <;>
    (simp only [shiftP, Prod.mk.injEq] at hq hlap hstar; split_ifs at hlap <;> omega)

/-- A free translate of the source rules out the corner white at every translate. -/
theorem cgAt_free_false (d X Y : ℤ) (i j : ℤ) (hij : IsAlias i j)
    (hfree : IsFreeP d (shiftP d (X, Y) i j)) (q : Pt) (hq : q = shiftP d (X, Y) i j) :
    ¬ cgAt d X Y q := by
  intro hcg
  exact (hcg.2.2.2.2 i j hij) (hq ▸ hfree)

/-- Prescribed directions are never `(1, 0)`. -/
theorem prescribed_ne_one_zero (d : ℤ) (q : Pt) : prescribedFree d q ≠ (1, 0) := by
  unfold prescribedFree
  split_ifs <;> simp

/-- The free-translate hits: some alias translate is free with prescribed direction `e`. -/
def freeHit (d X Y dx dy : ℤ) : Prop :=
  ∃ i j, IsAlias i j ∧ IsFreeP d (shiftP d (X, Y) i j) ∧ prescribedFree d (shiftP d (X, Y) i j) = (dx, dy)

/-- The corner hits: some alias translate is a corner white with horizontal direction `(±1, 0)` by its side. -/
def cgHit (d X Y dx dy : ℤ) : Prop :=
  ∃ i j, IsAlias i j ∧ cgAt d X Y (shiftP d (X, Y) i j) ∧
    (((shiftP d (X, Y) i j).1 ≤ 0 ∧ dx = -1 ∧ dy = 0) ∨ (2 ≤ (shiftP d (X, Y) i j).1 ∧ dx = 1 ∧ dy = 0))

/-- Some alias translate is a white (a free translate, or a corner white). -/
def hasWhite (d X Y : ℤ) : Prop :=
  ∃ i j, IsAlias i j ∧ (IsFreeP d (shiftP d (X, Y) i j) ∨ cgAt d X Y (shiftP d (X, Y) i j))

/-- The retained-edge predicate of prove_rank.py `edge`: parity-axis, and no white or a matching hit. -/
def Retained (d X Y dx dy : ℤ) : Prop :=
  (((X + Y) % 2 = 0 ∧ dy = 0) ∨ ((X + Y) % 2 ≠ 0 ∧ dx = 0)) ∧
    (¬ hasWhite d X Y ∨ freeHit d X Y dx dy ∨ cgHit d X Y dx dy)

/-- The corner white at the point of an interior even point with `x ≥ 2`. -/
theorem cg_origin_right (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y))
    (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (h4 : x + y ≠ d + 2) (h5 : ¬ (x = d ∧ y = 1))
    (hpar : (x + y) % 2 = 0) (hx : 2 ≤ x) : cgAt d x y (x, y) := by
  have hnf := interior_noFree d x y hd hn hf hy h4 h5
  have hb : 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 1 := by
    unfold NativeP at hn
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hn hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  refine ⟨?_, ?_, hpar, Or.inr hx, hnf⟩
  · refine ⟨hn, Or.inl ⟨hpar, ?_, ?_⟩⟩
    · unfold NativeP
      simp only [Prod.mk.injEq]
      omega
    · unfold NativeP
      simp only [Prod.mk.injEq]
      omega
  · rw [lapV_ge2 d x y hx, if_pos hpar]
    split_ifs <;> omega

set_option maxHeartbeats 400000 in
/-- No corner white with `a ≤ 0` at any alias translate of an interior even point with `x ≥ 2`. -/
theorem no_cg_left_of_right (d x y : ℤ) (hd : 3 ≤ d) (hn : NativeP d (x, y))
    (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (h4 : x + y ≠ d + 2) (h5 : ¬ (x = d ∧ y = 1))
    (hpar : (x + y) % 2 = 0) (hx : 2 ≤ x) (i j : ℤ) (hij : IsAlias i j)
    (hcg : cgAt d x y (shiftP d (x, y) i j)) (hq : (shiftP d (x, y) i j).1 ≤ 0) : False := by
  have hb : 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 1 := by
    unfold NativeP at hn
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hn hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hij
  obtain ⟨hstar, -, hpar', -, -⟩ := hcg
  clear hn hf
  unfold starV NativeP at hstar
  interval_cases i <;> interval_cases j <;>
    (simp only [shiftP, Prod.mk.injEq] at hq hstar hpar'; omega)

/-- Interior even point with `x ≤ 0`: the rightward edge `(1, 0)` is not retained. -/
theorem excl_left_even_one_zero (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y))
    (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (h4 : x + y ≠ d + 2) (h5 : ¬ (x = d ∧ y = 1))
    (hpar : (x + y) % 2 = 0) (hx : x ≤ 0) : ¬ Retained d x y 1 0 := by
  rintro ⟨-, hW | hH | hH⟩
  · exact hW ⟨0, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, Or.inr (by
      rw [show shiftP d (x, y) 0 0 = (x, y) by simp [shiftP]]
      exact cg_origin_left d x y hd hdodd hn hf hy h4 h5 hpar hx)⟩
  · obtain ⟨i, j, -, -, hpres⟩ := hH
    exact prescribed_ne_one_zero d _ hpres
  · obtain ⟨i, j, hij, hcg, hdir⟩ := hH
    rcases hdir with ⟨-, hdx, -⟩ | ⟨hq, -, -⟩
    · omega
    · exact no_cg_right_of_left d x y hd hdodd hn hf hy hpar hx i j hij hcg hq

/-- A free translate of the source rules out every corner white. -/
theorem cgAt_false_of_witness (d X Y : ℤ) (q : Pt)
    (hw : ∃ i j, IsAlias i j ∧ IsFreeP d (shiftP d (X, Y) i j)) : ¬ cgAt d X Y q := by
  obtain ⟨i, j, hij, hfree⟩ := hw
  intro h
  exact h.2.2.2.2 i j hij hfree

/-- With a free translate, every retained edge is a free hit. -/
theorem retained_witness (d X Y dx dy : ℤ)
    (hw : ∃ i j, IsAlias i j ∧ IsFreeP d (shiftP d (X, Y) i j)) (hR : Retained d X Y dx dy) :
    freeHit d X Y dx dy := by
  obtain ⟨-, h⟩ := hR
  rcases h with hnW | hH | hH
  · exfalso
    apply hnW
    obtain ⟨i, j, hij, hfree⟩ := hw
    exact ⟨i, j, hij, Or.inl hfree⟩
  · exact hH
  · exfalso
    obtain ⟨i, j, -, hc, -⟩ := hH
    exact cgAt_false_of_witness d X Y _ hw hc

/-- With a free translate, the edge `(1, 0)` is not retained. -/
theorem not_retained_one_zero_of_witness (d X Y : ℤ)
    (hw : ∃ i j, IsAlias i j ∧ IsFreeP d (shiftP d (X, Y) i j)) : ¬ Retained d X Y 1 0 := by
  intro hR
  obtain ⟨i, j, -, -, hpres⟩ := retained_witness d X Y 1 0 hw hR
  exact prescribed_ne_one_zero d _ hpres

/-- A retained unit edge at a free native point is its prescribed direction. -/
theorem retained_free_root_eq (d x y dx dy : ℤ) (hd : 3 ≤ d) (hf : IsFreeP d (x, y))
    (hR : Retained d x y dx dy) : prescribedFree d (x, y) = (dx, dy) := by
  have hself : shiftP d (x, y) 0 0 = (x, y) := by simp [shiftP]
  have hw : ∃ i j, IsAlias i j ∧ IsFreeP d (shiftP d (x, y) i j) :=
    ⟨0, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, by rw [hself]; exact hf⟩
  obtain ⟨i, j, hij, hfree, hpres⟩ := retained_witness d x y dx dy hw hR
  by_cases h0 : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h0
    rw [hself] at hpres
    exact hpres
  · exact absurd hfree (free_translate_not_free d hd (x, y) hf i j hij h0)

set_option maxHeartbeats 400000 in
/-- The top row point `(x, d+1)` with `x` odd, `x ≤ 0`: no free translate has prescribed direction `(0, 1)`. -/
theorem top_odd_no_up (d x : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 0)
    (hodd : x % 2 = 1) (i j : ℤ) (hij : IsAlias i j) (hfree : IsFreeP d (shiftP d (x, d + 1) i j)) :
    prescribedFree d (shiftP d (x, d + 1) i j) ≠ (0, 1) := by
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hij
  intro hpres
  unfold IsFreeP IsHc IsVc at hfree
  unfold prescribedFree IsHc at hpres
  simp only [shiftP, Prod.mk.injEq] at hfree hpres
  interval_cases i <;> interval_cases j <;> (split_ifs at hpres <;> simp only [Prod.mk.injEq] at hpres <;> omega)

set_option maxHeartbeats 400000 in
/-- The top row point `(1, d+1)`: no free translate has prescribed direction `(0, −1)`. -/
theorem top_one_no_down (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (i j : ℤ) (hij : IsAlias i j)
    (hfree : IsFreeP d (shiftP d (1, d + 1) i j)) :
    prescribedFree d (shiftP d (1, d + 1) i j) ≠ (0, -1) := by
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hij
  intro hpres
  unfold IsFreeP IsHc IsVc at hfree
  unfold prescribedFree IsHc at hpres
  simp only [shiftP, Prod.mk.injEq] at hfree hpres
  interval_cases i <;> interval_cases j <;> (split_ifs at hpres <;> simp only [Prod.mk.injEq] at hpres <;> omega)

set_option maxHeartbeats 400000 in
/-- The anti-diagonal point `(x, y)` with `x + y = d+2`, `2 ≤ x`, `y ≤ d`: no free translate has prescribed direction `(0, −1)`. -/
theorem anti_no_down (d x y : ℤ) (hdodd : d % 2 = 1) (hs : x + y = d + 2)
    (hx : 2 ≤ x) (hxd : x ≤ d) (i j : ℤ) (hij : IsAlias i j)
    (hfree : IsFreeP d (shiftP d (x, y) i j)) : prescribedFree d (shiftP d (x, y) i j) ≠ (0, -1) := by
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hij
  intro hpres
  unfold IsFreeP IsHc IsVc at hfree
  unfold prescribedFree IsHc at hpres
  simp only [shiftP, Prod.mk.injEq] at hfree hpres
  interval_cases i <;> interval_cases j <;> (split_ifs at hpres <;> simp only [Prod.mk.injEq] at hpres <;> omega)

/-- Interior even point with `x ≥ 2`: the leftward edge `(−1, 0)` is not retained. -/
theorem excl_right_even_neg_one (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y))
    (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (h4 : x + y ≠ d + 2) (h5 : ¬ (x = d ∧ y = 1))
    (hpar : (x + y) % 2 = 0) (hx : 2 ≤ x) : ¬ Retained d x y (-1) 0 := by
  rintro ⟨-, hW | hH | hH⟩
  · exact hW ⟨0, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, Or.inr (by
      rw [show shiftP d (x, y) 0 0 = (x, y) by simp [shiftP]]
      exact cg_origin_right d x y hd hdodd hn hf hy h4 h5 hpar hx)⟩
  · obtain ⟨i, j, hij, hfree, -⟩ := hH
    exact interior_noFree d x y hd hn hf hy h4 h5 i j hij hfree
  · obtain ⟨i, j, hij, hcg, hdir⟩ := hH
    rcases hdir with ⟨hq, -, -⟩ | ⟨-, hdx, -⟩
    · exact no_cg_left_of_right d x y hd hn hf hy h4 h5 hpar hx i j hij hcg hq
    · omega

/-! ### Rank values and witnesses of the boundary families -/

theorem native_top (d x : ℤ) (hd : 3 ≤ d) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 1) : NativeP d (x, d + 1) := by
  unfold NativeP
  simp only [Prod.mk.injEq]
  omega

theorem qRank_free (d x y : ℤ) (hf : IsFreeP d (x, y)) : qRank d (x, y) = valMinus d (x, y) := by
  unfold qRank
  exact if_pos hf

theorem qRank_interior (d x y : ℤ) (hd : 3 ≤ d) (hn : NativeP d (x, y)) (hf : ¬ IsFreeP d (x, y))
    (hy : y ≤ d) (h4 : x + y ≠ d + 2) (h5 : ¬ (x = d ∧ y = 1)) : qRank d (x, y) = valMinus d (x, y) :=
  (rankOf_eq_qRank d hd x y hn _ (rankOf_self d (x, y) (rep_interior d x y hn hf hy h4 h5))).symm

theorem qRank_top_even (d x : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 0)
    (hev : x % 2 = 0) : qRank d (x, d + 1) = 2 * x - 4 := by
  have h := rankOf_eq_qRank d hd x (d + 1) (native_top d x hd hx1 (by omega)) _ (rankOf_top d x hx1 (by omega))
  rw [valMinus_H_even d (x + d - 1) (by omega) (by omega) (by omega)] at h
  rw [← h]
  ring

theorem qRank_top_odd (d x : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 0)
    (hod : x % 2 = 1) : qRank d (x, d + 1) = 2 * x - 3 := by
  have h := rankOf_eq_qRank d hd x (d + 1) (native_top d x hd hx1 (by omega)) _ (rankOf_top d x hx1 (by omega))
  rw [valMinus_H_odd d (x + d - 1) (by omega) (by omega) (by omega)] at h
  rw [← h]
  ring

theorem qRank_top_one (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) : qRank d (1, d + 1) = -1 := by
  have h := rankOf_eq_qRank d hd 1 (d + 1) (native_top d 1 hd (by omega) (by omega)) _
    (rankOf_top d 1 (by omega) (by omega))
  rw [show (1 : ℤ) + d - 1 = d by ring, valMinus_H_odd d d (by omega) le_rfl hdodd] at h
  rw [← h]
  ring

theorem qRank_corner (d : ℤ) (hd : 3 ≤ d) : qRank d (2, d + 1) = 0 := by
  have hn : NativeP d (2, d + 1) := by
    unfold NativeP
    exact Or.inr (Or.inr rfl)
  have h := rankOf_eq_qRank d hd 2 (d + 1) hn _ (rankOf_corner d)
  rw [valMinus_Vlast d hd] at h
  rw [← h]
  ring

theorem qRank_anti (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hs : x + y = d + 2) (hx : 2 ≤ x)
    (hxd : x ≤ d) (hyd : y ≤ d) : qRank d (x, y) = 2 * x - 3 := by
  have hn : NativeP d (x, y) := by
    unfold NativeP
    simp only [Prod.mk.injEq]
    omega
  have h := rankOf_eq_qRank d hd x y hn _ (rankOf_anti d x y hs hxd hyd)
  have e : y - 1 = 1 - (x - d) := by omega
  rw [e, valMinus_V_odd d (x - d) (by omega) (by omega)] at h
  rw [← h]
  ring

theorem qRank_fifth (d : ℤ) (hd : 3 ≤ d) : qRank d (d, 1) = 2 * d := by
  have hn : NativeP d (d, 1) := by
    unfold NativeP
    simp only [Prod.mk.injEq]
    omega
  have h := rankOf_eq_qRank d hd d 1 hn _ (rankOf_fifth d)
  rw [valMinus_origin d] at h
  rw [← h]
  ring

theorem top_H_witness (d x : ℤ) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 0) :
    ∃ i j, IsAlias i j ∧ IsFreeP d (shiftP d (x, d + 1) i j) := by
  refine ⟨0, -1, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  have e : shiftP d (x, d + 1) 0 (-1) = (x + d - 1, 0) := by
    simp only [shiftP, Prod.mk.injEq]
    constructor <;> ring
  rw [e]
  unfold IsFreeP
  left
  unfold IsHc
  exact ⟨rfl, by show 1 ≤ x + d - 1; omega, by show x + d - 1 ≤ d; omega⟩

theorem top_one_witness (d : ℤ) (hd : 3 ≤ d) : ∃ i j, IsAlias i j ∧ IsFreeP d (shiftP d (1, d + 1) i j) := by
  refine ⟨0, -1, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  have e : shiftP d (1, d + 1) 0 (-1) = (d, 0) := by
    simp only [shiftP, Prod.mk.injEq]
    constructor <;> ring
  rw [e]
  unfold IsFreeP
  left
  unfold IsHc
  exact ⟨rfl, by show 1 ≤ d; omega, by show d ≤ d; omega⟩

theorem corner_witness (d : ℤ) : ∃ i j, IsAlias i j ∧ IsFreeP d (shiftP d (2, d + 1) i j) := by
  refine ⟨-1, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  have e : shiftP d (2, d + 1) (-1) 0 = (2 - d, d) := by
    simp only [shiftP, Prod.mk.injEq]
    constructor <;> ring
  rw [e]
  unfold IsFreeP
  right
  unfold IsVc
  exact Or.inr (Or.inr rfl)

theorem fifth_witness (d : ℤ) : ∃ i j, IsAlias i j ∧ IsFreeP d (shiftP d (d, 1) i j) := by
  refine ⟨-1, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  have e : shiftP d (d, 1) (-1) 0 = (0, 0) := by
    simp only [shiftP, Prod.mk.injEq]
    constructor <;> ring
  rw [e]
  unfold IsFreeP
  right
  unfold IsVc
  exact Or.inl rfl

theorem anti_witness (d x y : ℤ) (hs : x + y = d + 2) (hx : 2 ≤ x) (hxd : x ≤ d) :
    ∃ i j, IsAlias i j ∧ IsFreeP d (shiftP d (x, y) i j) := by
  refine ⟨-1, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  have e : shiftP d (x, y) (-1) 0 = (x - d, y - 1) := by
    simp only [shiftP, Prod.mk.injEq]
    constructor <;> ring
  rw [e]
  unfold IsFreeP
  right
  unfold IsVc
  right
  left
  exact ⟨by show x - d + (y - 1) = 1; omega, by show 1 ≤ y - 1; omega, by show y - 1 < d; omega⟩

/-! ### The family lemmas: every unit retained edge of a boundary family drops below its rank -/

theorem L_top_even (d x dx dy : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 0)
    (hev : x % 2 = 0)
    (hunit : (dx, dy) = (1, 0) ∨ (dx, dy) = (-1, 0) ∨ (dx, dy) = (0, 1) ∨ (dx, dy) = (0, -1))
    (hR : Retained d x (d + 1) dx dy) (r : ℤ) (hr : RankOf d (x + dx, d + 1 + dy) r) :
    r < qRank d (x, d + 1) := by
  rw [qRank_top_even d x hd hdodd hx1 hx2 hev]
  rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · exact absurd hR (not_retained_one_zero_of_witness d x (d + 1) (top_H_witness d x hx1 hx2))
  · have hr' : RankOf d (x - 1, d + 1) r := by
      rwa [show x + -1 = x - 1 by ring, show d + 1 + 0 = d + 1 by ring] at hr
    exact gate_top_even d x hd hdodd hx1 hx2 hev r hr'
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem L_top_odd (d x dx dy : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 0)
    (hod : x % 2 = 1)
    (hunit : (dx, dy) = (1, 0) ∨ (dx, dy) = (-1, 0) ∨ (dx, dy) = (0, 1) ∨ (dx, dy) = (0, -1))
    (hR : Retained d x (d + 1) dx dy) (r : ℤ) (hr : RankOf d (x + dx, d + 1 + dy) r) :
    r < qRank d (x, d + 1) := by
  rw [qRank_top_odd d x hd hdodd hx1 hx2 hod]
  rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · obtain ⟨i, j, hij, hfree, hpres⟩ :=
      retained_witness d x (d + 1) 0 1 (top_H_witness d x hx1 hx2) hR
    exact absurd hpres (top_odd_no_up d x hd hdodd hx1 hx2 hod i j hij hfree)
  · have hr' : RankOf d (x, d) r := by
      rwa [show x + 0 = x by ring, show d + 1 + -1 = d by ring] at hr
    exact gate_top_odd d x hd hdodd hx1 hx2 hod r hr'

theorem L_top_one (d dx dy : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1)
    (hunit : (dx, dy) = (1, 0) ∨ (dx, dy) = (-1, 0) ∨ (dx, dy) = (0, 1) ∨ (dx, dy) = (0, -1))
    (hR : Retained d 1 (d + 1) dx dy) (r : ℤ) (hr : RankOf d (1 + dx, d + 1 + dy) r) :
    r < qRank d (1, d + 1) := by
  rw [qRank_top_one d hd hdodd]
  rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · have hr' : RankOf d (1, d + 2) r := by
      rwa [show (1 : ℤ) + 0 = 1 by ring, show d + 1 + 1 = d + 2 by ring] at hr
    exact gate_top_one d hd hdodd r hr'
  · obtain ⟨i, j, hij, hfree, hpres⟩ :=
      retained_witness d 1 (d + 1) 0 (-1) (top_one_witness d hd) hR
    exact absurd hpres (top_one_no_down d hd hdodd i j hij hfree)

theorem L_corner (d dx dy : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1)
    (hunit : (dx, dy) = (1, 0) ∨ (dx, dy) = (-1, 0) ∨ (dx, dy) = (0, 1) ∨ (dx, dy) = (0, -1))
    (hR : Retained d 2 (d + 1) dx dy) (r : ℤ) (hr : RankOf d (2 + dx, d + 1 + dy) r) :
    r < qRank d (2, d + 1) := by
  rw [qRank_corner d hd]
  rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · exact absurd hR (not_retained_one_zero_of_witness d 2 (d + 1) (corner_witness d))
  · have hr' : RankOf d (1, d + 1) r := by
      rwa [show (2 : ℤ) + -1 = 1 by ring, show d + 1 + 0 = d + 1 by ring] at hr
    exact gate_corner d hd hdodd r hr'
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem L_anti (d x y dx dy : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hs : x + y = d + 2) (hx : 2 ≤ x)
    (hxd : x ≤ d) (hyd : y ≤ d)
    (hunit : (dx, dy) = (1, 0) ∨ (dx, dy) = (-1, 0) ∨ (dx, dy) = (0, 1) ∨ (dx, dy) = (0, -1))
    (hR : Retained d x y dx dy) (r : ℤ) (hr : RankOf d (x + dx, y + dy) r) :
    r < qRank d (x, y) := by
  rw [qRank_anti d x y hd hdodd hs hx hxd hyd]
  rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · obtain rfl : y = d + 2 - x := by omega
    have hr' : RankOf d (x, d + 3 - x) r := by
      rwa [show x + 0 = x by ring, show d + 2 - x + 1 = d + 3 - x by ring] at hr
    exact gate_anti d x hd hdodd hx hxd r hr'
  · obtain ⟨i, j, hij, hfree, hpres⟩ :=
      retained_witness d x y 0 (-1) (anti_witness d x y hs hx hxd) hR
    exact absurd hpres (anti_no_down d x y hdodd hs hx hxd i j hij hfree)

theorem L_fifth (d dx dy : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1)
    (hunit : (dx, dy) = (1, 0) ∨ (dx, dy) = (-1, 0) ∨ (dx, dy) = (0, 1) ∨ (dx, dy) = (0, -1))
    (hR : Retained d d 1 dx dy) (r : ℤ) (hr : RankOf d (d + dx, 1 + dy) r) :
    r < qRank d (d, 1) := by
  rw [qRank_fifth d hd]
  rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · exact absurd hR (not_retained_one_zero_of_witness d d 1 (fifth_witness d))
  · have hr' : RankOf d (d - 1, 1) r := by
      rwa [show d + -1 = d - 1 by ring, show (1 : ℤ) + 0 = 1 by ring] at hr
    exact gate_fifth d hd hdodd r hr'
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem L_interior (d x y dx dy : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y))
    (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (h4 : x + y ≠ d + 2) (h5 : ¬ (x = d ∧ y = 1))
    (hunit : (dx, dy) = (1, 0) ∨ (dx, dy) = (-1, 0) ∨ (dx, dy) = (0, 1) ∨ (dx, dy) = (0, -1))
    (hR : Retained d x y dx dy) (r : ℤ) (hr : RankOf d (x + dx, y + dy) r) :
    r < qRank d (x, y) := by
  rw [qRank_interior d x y hd hn hf hy h4 h5]
  rcases (show (x + y) % 2 = 0 ∨ (x + y) % 2 = 1 by omega) with hpar | hodd
  · rcases (show x ≤ 0 ∨ x = 1 ∨ 2 ≤ x by omega) with hx0 | hx1 | hx2
    · rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
      · exact absurd hR (excl_left_even_one_zero d x y hd hdodd hn hf hy h4 h5 hpar hx0)
      · have hr' : RankOf d (x - 1, y) r := by
          rwa [show x + -1 = x - 1 by ring, show y + 0 = y by ring] at hr
        exact gate_int_left_even d x y hd hn hf hpar hx0 r hr'
      · obtain ⟨hp, -⟩ := hR
        rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · obtain ⟨hp, -⟩ := hR
        rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
      · by_cases hdiag : x + y = d + 1
        · have hr' : RankOf d (x + 1, y) r := by rwa [show y + 0 = y by ring] at hr
          exact gate_int_diag_right d x y hd hdodd hn hf h5 (by omega) hdiag r hr'
        · exact gate_int_right_even d x y hd hdodd hn hf hy hdiag h5 (by omega) hpar r
            (by rwa [show y + 0 = y by ring] at hr)
      · by_cases hdiag : x + y = d + 1
        · have hr' : RankOf d (x - 1, y) r := by
            rwa [show x + -1 = x - 1 by ring, show y + 0 = y by ring] at hr
          exact gate_int_one_diag_left d x y hd hdodd hf hy hx1 hdiag r hr'
        · have hr' : RankOf d (x - 1, y) r := by
            rwa [show x + -1 = x - 1 by ring, show y + 0 = y by ring] at hr
          exact gate_int_one_left d x y hd hdodd hn hf hy hx1 hdiag hpar r hr'
      · obtain ⟨hp, -⟩ := hR
        rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · obtain ⟨hp, -⟩ := hR
        rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
      · by_cases hdiag : x + y = d + 1
        · have hr' : RankOf d (x + 1, y) r := by rwa [show y + 0 = y by ring] at hr
          exact gate_int_diag_right d x y hd hdodd hn hf h5 (by omega) hdiag r hr'
        · exact gate_int_right_even d x y hd hdodd hn hf hy hdiag h5 (by omega) hpar r
            (by rwa [show y + 0 = y by ring] at hr)
      · exact absurd hR (excl_right_even_neg_one d x y hd hdodd hn hf hy h4 h5 hpar hx2)
      · obtain ⟨hp, -⟩ := hR
        rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · obtain ⟨hp, -⟩ := hR
        rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · rcases (show x ≤ 0 ∨ 1 ≤ x by omega) with hx0 | hx1
    · rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
      · obtain ⟨hp, -⟩ := hR
        rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · obtain ⟨hp, -⟩ := hR
        rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · have hr' : RankOf d (x, y + 1) r := by rwa [show x + 0 = x by ring] at hr
        exact gate_int_odd_left_up d x y hd hdodd hn hf hy hx0 hodd r hr'
      · have hr' : RankOf d (x, y - 1) r := by
          rwa [show x + 0 = x by ring, show y + -1 = y - 1 by ring] at hr
        exact gate_int_odd_left_down d x y hd hdodd hn hf hy hx0 hodd r hr'
    · rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
      · obtain ⟨hp, -⟩ := hR
        rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · obtain ⟨hp, -⟩ := hR
        rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · have hr' : RankOf d (x, y + 1) r := by rwa [show x + 0 = x by ring] at hr
        exact gate_int_odd_right_up d x y hd hdodd hn hf hy hx1 hodd r hr'
      · have hr' : RankOf d (x, y - 1) r := by
          rwa [show x + 0 = x by ring, show y + -1 = y - 1 by ring] at hr
        exact gate_int_odd_right_down d x y hd hdodd hn hf hy h4 hx1 hodd r hr'

/-- **The Q_minus gate on retained unit edges.** For every native point and every unit edge retained by the white predicate, every
rank of the target is below the rank of the source. -/
theorem qminus_gate (d x y dx dy : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y))
    (hunit : (dx, dy) = (1, 0) ∨ (dx, dy) = (-1, 0) ∨ (dx, dy) = (0, 1) ∨ (dx, dy) = (0, -1))
    (hR : Retained d x y dx dy) (r : ℤ) (hr : RankOf d (x + dx, y + dy) r) : r < qRank d (x, y) := by
  by_cases hf : IsFreeP d (x, y)
  · rw [qRank_free d x y hf]
    exact free_root_gate d hd x y dx dy hf (retained_free_root_eq d x y dx dy hd hf hR) r hr
  · by_cases htop : y = d + 1 ∧ x ≤ 1
    · obtain ⟨rfl, hx1⟩ := htop
      have hb : 2 - d ≤ x := by
        unfold NativeP at hn
        simp only [Prod.mk.injEq] at hn
        omega
      rcases (show (x % 2 = 0 ∧ x ≤ 0) ∨ (x % 2 = 1 ∧ x ≤ 0) ∨ x = 1 by omega) with
        ⟨hev, hx0⟩ | ⟨hod, hx0⟩ | hx1'
      · exact L_top_even d x dx dy hd hdodd hb hx0 hev hunit hR r hr
      · exact L_top_odd d x dx dy hd hdodd hb hx0 hod hunit hR r hr
      · subst hx1'
        exact L_top_one d dx dy hd hdodd hunit hR r hr
    by_cases hc : x = 2 ∧ y = d + 1
    · obtain ⟨rfl, rfl⟩ := hc
      exact L_corner d dx dy hd hdodd hunit hR r hr
    by_cases ha : x + y = d + 2 ∧ y ≤ d
    · obtain ⟨hs, hyd⟩ := ha
      have hx2 : 2 ≤ x := by omega
      have hxd : x ≤ d := by
        unfold NativeP at hn
        simp only [Prod.mk.injEq] at hn
        omega
      exact L_anti d x y dx dy hd hdodd hs hx2 hxd hyd hunit hR r hr
    by_cases hfi : x = d ∧ y = 1
    · obtain ⟨hxd, rfl⟩ := hfi
      rw [hxd] at hR hr ⊢
      exact L_fifth d dx dy hd hdodd hunit hR r hr
    · have hyd : y ≤ d := by
        unfold NativeP at hn
        simp only [Prod.mk.injEq] at hn
        omega
      have h4 : x + y ≠ d + 2 := fun h => ha ⟨h, hyd⟩
      exact L_interior d x y dx dy hd hdodd hn hf hyd h4 hfi hunit hR r hr


end FLatticePaper.PureRank
