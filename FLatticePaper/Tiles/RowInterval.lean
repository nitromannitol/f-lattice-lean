import FLatticePaper.Tiles.WalkRows

/-! Row intervals of a tile. For the boundary word `w1 * w2 * hat(rev w1) * hat(rev w2)` with `w1` in `{1, i}` and `w2` in
`{i, -1}`, the first part of the walk has only north steps and the second part only south steps. Each row `b` of the tile
then has at most one north step (on the right) and one south step (on the left), so the tile's row is the interval
`[colS b, colN b)`. -/

namespace FLatticePaper.Tiles

/-- The number of north steps `i` of a word. -/
def cntI : F2Word → ℤ
  | [] => 0
  | x :: u => (if x = .i then 1 else 0) + cntI u

/-- The number of south steps `-i` of a word. -/
def cntNegI : F2Word → ℤ
  | [] => 0
  | x :: u => (if x = .negI then 1 else 0) + cntNegI u

/-- The column of the north step, starting in row `b`, of a word walked from `p`. -/
def colN : F2Word → GInt → ℤ → ℤ
  | [], _, _ => 0
  | x :: u, p, b => if x = .i ∧ p.2 = b then p.1 else colN u (p + x.vec) b

/-- The column of the south step, ending in row `b` (starting in row `b + 1`), of a word walked from `p`. -/
def colS : F2Word → GInt → ℤ → ℤ
  | [], _, _ => 0
  | x :: u, p, b => if x = .negI ∧ p.2 = b + 1 then p.1 else colS u (p + x.vec) b

theorem cntI_nonneg (u : F2Word) : 0 ≤ cntI u := by
  induction u with
  | nil => simp [cntI]
  | cons x u ih => unfold cntI; split_ifs <;> omega

theorem cntNegI_nonneg (u : F2Word) : 0 ≤ cntNegI u := by
  induction u with
  | nil => simp [cntNegI]
  | cons x u ih => unfold cntNegI; split_ifs <;> omega

theorem cntI_append (u v : F2Word) : cntI (u ++ v) = cntI u + cntI v := by
  induction u with
  | nil => simp [cntI]
  | cons x u ih => simp only [List.cons_append, cntI, ih]; ring

theorem cntNegI_append (u v : F2Word) : cntNegI (u ++ v) = cntNegI u + cntNegI v := by
  induction u with
  | nil => simp [cntNegI]
  | cons x u ih => simp only [List.cons_append, cntNegI, ih]; ring

theorem cntNegI_map_neg (u : F2Word) : cntNegI (u.map Unit4.neg) = cntI u := by
  induction u with
  | nil => simp [cntNegI, cntI]
  | cons x u ih => cases x <;> simp [cntNegI, cntI, Unit4.neg, ih]

theorem hat_rev (w : F2Word) : (F2Word.rev w).hat = w.map Unit4.neg := by
  simp [F2Word.hat, F2Word.rev, List.map_reverse]

/-- The sum of a word without south steps has second coordinate the number of north steps. -/
theorem sum_snd (u : F2Word) (hu : ∀ x ∈ u, x ≠ .negI) : (F2Word.sum u).2 = cntI u := by
  induction u with
  | nil => simp [F2Word.sum, cntI]
  | cons x u ih =>
    have hx : x ≠ .negI := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y ≠ .negI := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    have hs : F2Word.sum (x :: u) = x.vec + F2Word.sum u := by simp [F2Word.sum]
    rw [hs, Prod.snd_add, ih hu']
    cases x <;> simp [Unit4.vec, cntI] at hx ⊢

/-- The north contributions of a word without south steps: the step in row `b` counts when its column is at most `a`. -/
theorem sum_north (u : F2Word) (hu : ∀ x ∈ u, x ≠ .negI) (p : GInt) (b a : ℤ) :
    ((edgesFrom p u).map (vsgn b a)).sum =
      if p.2 ≤ b ∧ b < p.2 + cntI u ∧ colN u p b ≤ a then 1 else 0 := by
  induction u generalizing p with
  | nil => simp only [edgesFrom, List.map_nil, List.sum_nil, cntI, colN]; split_ifs <;> omega
  | cons x u ih =>
    have hx : x ≠ .negI := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y ≠ .negI := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    simp only [edgesFrom, List.map_cons, List.sum_cons]
    cases x with
    | one =>
      have hp : (p + Unit4.vec .one).2 = p.2 := by simp [Unit4.vec]
      have hc : colN (Unit4.one :: u) p b = colN u (p + Unit4.vec .one) b := by simp [colN]
      have hcnt : cntI (Unit4.one :: u) = cntI u := by simp [cntI]
      rw [vsgn_one, zero_add, ih hu' (p + Unit4.vec .one), hp, hc, hcnt]
    | negOne =>
      have hp : (p + Unit4.vec .negOne).2 = p.2 := by simp [Unit4.vec]
      have hc : colN (Unit4.negOne :: u) p b = colN u (p + Unit4.vec .negOne) b := by simp [colN]
      have hcnt : cntI (Unit4.negOne :: u) = cntI u := by simp [cntI]
      rw [vsgn_negOne, zero_add, ih hu' (p + Unit4.vec .negOne), hp, hc, hcnt]
    | i =>
      have hp : (p + Unit4.vec .i).2 = p.2 + 1 := by simp [Unit4.vec]
      have hc : colN (Unit4.i :: u) p b = if p.2 = b then p.1 else colN u (p + Unit4.vec .i) b := by
        simp only [colN, true_and]
      have hcnt : cntI (Unit4.i :: u) = 1 + cntI u := by simp [cntI]
      rw [vsgn_i, ih hu' (p + Unit4.vec .i), hp, hc, hcnt]
      have h0 := cntI_nonneg u
      by_cases h : p.2 = b
      · simp only [h, if_true, true_and]
        split_ifs <;> omega
      · simp only [h, if_false, false_and]
        split_ifs <;> omega
    | negI => exact absurd rfl hx

/-- The south contributions of a word without north steps: the step ending in row `b` counts with sign `-1`
when its column is at most `a`. -/
theorem sum_south (u : F2Word) (hu : ∀ x ∈ u, x ≠ .i) (p : GInt) (b a : ℤ) :
    ((edgesFrom p u).map (vsgn b a)).sum =
      if p.2 - cntNegI u ≤ b ∧ b + 1 ≤ p.2 ∧ colS u p b ≤ a then -1 else 0 := by
  induction u generalizing p with
  | nil => simp only [edgesFrom, List.map_nil, List.sum_nil, cntNegI, colS]; split_ifs <;> omega
  | cons x u ih =>
    have hx : x ≠ .i := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y ≠ .i := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    simp only [edgesFrom, List.map_cons, List.sum_cons]
    cases x with
    | one =>
      have hp : (p + Unit4.vec .one).2 = p.2 := by simp [Unit4.vec]
      have hc : colS (Unit4.one :: u) p b = colS u (p + Unit4.vec .one) b := by simp [colS]
      have hcnt : cntNegI (Unit4.one :: u) = cntNegI u := by simp [cntNegI]
      rw [vsgn_one, zero_add, ih hu' (p + Unit4.vec .one), hp, hc, hcnt]
    | negOne =>
      have hp : (p + Unit4.vec .negOne).2 = p.2 := by simp [Unit4.vec]
      have hc : colS (Unit4.negOne :: u) p b = colS u (p + Unit4.vec .negOne) b := by simp [colS]
      have hcnt : cntNegI (Unit4.negOne :: u) = cntNegI u := by simp [cntNegI]
      rw [vsgn_negOne, zero_add, ih hu' (p + Unit4.vec .negOne), hp, hc, hcnt]
    | i => exact absurd rfl hx
    | negI =>
      have hp : (p + Unit4.vec .negI).2 = p.2 - 1 := by simp only [Unit4.vec, Prod.snd_add]; ring
      have hc : colS (Unit4.negI :: u) p b = if p.2 = b + 1 then p.1 else colS u (p + Unit4.vec .negI) b := by
        simp only [colS, true_and]
      have hcnt : cntNegI (Unit4.negI :: u) = 1 + cntNegI u := by simp [cntNegI]
      rw [vsgn_negI, ih hu' (p + Unit4.vec .negI), hp, hc, hcnt]
      have h0 := cntNegI_nonneg u
      by_cases h : p.2 = b + 1
      · simp only [h, if_true, true_and]
        split_ifs <;> omega
      · simp only [h, if_false, false_and]
        split_ifs <;> omega

end FLatticePaper.Tiles
