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
  | [], p, _ => p.1
  | x :: u, p, b => if x = .i ∧ p.2 = b then p.1 else colN u (p + x.vec) b

/-- The column of the south step, ending in row `b` (starting in row `b + 1`), of a word walked from `p`. -/
def colS : F2Word → GInt → ℤ → ℤ
  | [], p, _ => p.1
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

/-- An integer equation of two indicator sums: `M` holds exactly when `P1` fails and `P2` holds. -/
theorem ite_sum_iff (P1 P2 M : Prop) [Decidable P1] [Decidable P2] [Decidable M]
    (h : (if P1 then (1 : ℤ) else 0) + (if P2 then -1 else 0) = -(if M then 1 else 0)) :
    M ↔ (¬P1 ∧ P2) := by
  by_cases hP1 : P1 <;> by_cases hP2 : P2 <;> by_cases hM : M <;> simp_all

/-- The row-interval description of a tile whose boundary word is `w1 * w2 * hat(rev w1) * hat(rev w2)`, with `w1` in
`{1, i}` and `w2` in `{i, -1}`: the cell `(a, b)` lies in the tile exactly when the row `b` is in the range of the
walk's north steps and `colS ≤ a < colN`. -/
theorem mem_iff_interval {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) (a b : ℤ) :
    ((a, b) : GInt) ∈ T ↔
      (c.2 ≤ b ∧ b < c.2 + cntI (w1 ++ w2)) ∧
        colS (w1.map Unit4.neg ++ w2.map Unit4.neg) (c + F2Word.sum (w1 ++ w2)) b ≤ a ∧
        a < colN (w1 ++ w2) c b := by
  have hrc := row_scan T b a
  rw [rowCount_eq_edges hT b a] at hrc
  have hword : boundaryWordOf w1 w2 = (w1 ++ w2) ++ (w1.map Unit4.neg ++ w2.map Unit4.neg) := by
    simp [boundaryWordOf, hat_rev, List.append_assoc]
  rw [hword, edgesFrom_append, List.map_append, List.sum_append] at hrc
  have hnoNeg : ∀ x ∈ w1 ++ w2, x ≠ .negI := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases h1 x hx with rfl | rfl <;> simp
    · rcases h2 x hx with rfl | rfl <;> simp
  have hnoI : ∀ x ∈ w1.map Unit4.neg ++ w2.map Unit4.neg, x ≠ .i := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rcases h1 y hy with rfl | rfl <;> simp [Unit4.neg]
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rcases h2 y hy with rfl | rfl <;> simp [Unit4.neg]
  rw [sum_north (w1 ++ w2) hnoNeg c b a, sum_south _ hnoI (c + F2Word.sum (w1 ++ w2)) b a] at hrc
  have hsnd : (c + F2Word.sum (w1 ++ w2)).2 = c.2 + cntI (w1 ++ w2) := by
    rw [Prod.snd_add, sum_snd _ hnoNeg]
  have hneg : cntNegI (w1.map Unit4.neg ++ w2.map Unit4.neg) = cntI (w1 ++ w2) := by
    rw [cntNegI_append, cntNegI_map_neg, cntNegI_map_neg, cntI_append]
  rw [hsnd, hneg] at hrc
  unfold cellInd at hrc
  have key := ite_sum_iff _ _ _ hrc
  rw [key]
  constructor
  · rintro ⟨hn, g1, g2, g3⟩
    refine ⟨⟨by omega, by omega⟩, g3, ?_⟩
    by_contra hc
    exact hn ⟨by omega, by omega, by omega⟩
  · rintro ⟨⟨h1', h2'⟩, h3, h4⟩
    refine ⟨fun hP1 => absurd hP1.2.2 (not_le.mpr h4), ?_⟩
    exact ⟨by omega, by omega, h3⟩

end FLatticePaper.Tiles
