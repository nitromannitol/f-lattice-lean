import FLatticePaper.GeneralK.ColumnCycles

namespace FLatticePaper.GeneralK.ColumnSlice

open Finset

/-- After centering by the largest simple-cycle mean over all sectors, the
weight of any finite directed walk is bounded by its simple remainder. -/
theorem sum_centered_edgeWeight_le (slice : ColumnSlice) (sector : slice.Sector)
    (bound : ℚ) (hnonneg : 0 ≤ bound)
    (hbound : ∀ left right : slice.Vertex sector.val,
      (slice.edgeWeight sector.val left right : ℚ) - (slice.cyclePeak - slice.a₀) ≤ bound)
    (length : ℕ) (path : ℕ → slice.Vertex sector.val)
    (hedge : ∀ i < length, IsEdge (path i) (path (i + 1))) :
    ∑ i ∈ range length, ((slice.edgeWeight sector.val (path i) (path (i + 1)) : ℚ) -
      (slice.cyclePeak - slice.a₀)) ≤ Fintype.card (slice.Vertex sector.val) * bound := by
  classical
  induction length using Nat.strong_induction_on generalizing path with
  | h length ih =>
    let adjusted (left right : slice.Vertex sector.val) : ℚ :=
      (slice.edgeWeight sector.val left right : ℚ) - (slice.cyclePeak - slice.a₀)
    let cost (path : ℕ → slice.Vertex sector.val) (i : ℕ) : ℚ := adjusted (path i) (path (i + 1))
    change ∑ i ∈ range length, cost path i ≤ _
    by_cases hrepeat : ∃ distance : ℕ, 0 < distance ∧
        ∃ first, first + distance ≤ length ∧ path first = path (first + distance)
    · let distance := Nat.find hrepeat
      obtain ⟨hdist, first, hlast, hloop⟩ := Nat.find_spec hrepeat
      change 0 < distance at hdist
      change first + distance ≤ length at hlast
      change path first = path (first + distance) at hloop
      have hshorter {d start : ℕ} (hd : 0 < d) (hlt : d < distance) (hend : start + d ≤ length) :
          path start ≠ path (start + d) := by
        intro heq
        exact Nat.find_min hrepeat hlt ⟨hd, start, hend, heq⟩
      let vertices (i : Fin distance) := path (first + i.val)
      have hinj : Function.Injective vertices := by
        intro i j h
        apply Fin.ext
        change path (first + i.val) = path (first + j.val) at h
        have hlt (p q : Fin distance) (hpq : p.val < q.val)
            (heq : path (first + p.val) = path (first + q.val)) : False := by
          have hs : (first + p.val) + (q.val - p.val) = first + q.val := by omega
          exact hshorter (by omega) (by have := q.isLt; omega) (by rw [hs]; have := q.isLt; omega)
            (hs ▸ heq)
        by_contra! hne
        rcases lt_or_gt_of_ne hne with hlt' | hlt'
        · exact hlt i j hlt' h
        · exact hlt j i hlt' h.symm
      have hcard : distance ≤ Fintype.card (slice.Vertex sector.val) := by
        simpa using Fintype.card_le_of_injective vertices hinj
      have hnext (i : Fin distance) : vertices (cyclicSucc i) = path (first + i.val + 1) := by
        change path (first + ((i.val + 1) % distance)) = _
        by_cases hi : i.val + 1 < distance
        · rw [Nat.mod_eq_of_lt hi, Nat.add_assoc]
        · have heq : i.val + 1 = distance := by have := i.isLt; omega
          rw [heq, Nat.mod_self, add_zero, hloop]
          congr 1
          omega
      let cycle : slice.SimpleCycle sector.val := ⟨⟨distance, by omega⟩, vertices,
        hdist, hinj, fun i => by
          change IsEdge (vertices i) (vertices (cyclicSucc i))
          rw [hnext]
          exact hedge (first + i.val) ((Nat.add_lt_add_left (show i.val < distance from i.isLt) first).trans_le hlast)⟩
      have hcycle : ∑ i ∈ range distance, cost path (first + i) ≤ 0 := by
        have h := slice.le_cyclePeak sector cycle
        have hmean : slice.cycleMean sector.val cycle ≤ slice.cyclePeak - slice.a₀ := by linarith only [h]
        have hsum := (div_le_iff₀ (show (0 : ℚ) < distance by exact_mod_cast hdist)).mp hmean
        rw [sum_range, sum_sub_distrib]
        change (∑ i : Fin distance, (slice.edgeWeight sector.val (vertices i) (path (first + i.val + 1)) : ℚ)) -
          (∑ _ : Fin distance, (slice.cyclePeak - slice.a₀)) ≤ 0
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        apply sub_nonpos.mpr
        calc
          _ = ∑ i : Fin distance, (slice.edgeWeight sector.val (vertices i) (vertices (cyclicSucc i)) : ℚ) :=
            sum_congr rfl (fun i _ => by rw [hnext])
          _ ≤ (slice.cyclePeak - slice.a₀) * distance := hsum
          _ = _ := mul_comm ..
      let short (i : ℕ) := if i < first then path i else path (i + distance)
      have hbefore (i : ℕ) (hi : i < first) : cost short i = cost path i := by
        unfold cost short
        rw [if_pos hi]
        by_cases hnext : i + 1 < first
        · rw [if_pos hnext]
        · have heq : i + 1 = first := by omega
          rw [if_neg hnext, heq, ← hloop]
      have hafter (i : ℕ) : cost short (first + i) = cost path (first + distance + i) := by
        unfold cost short
        rw [if_neg (by omega), if_neg (by omega)]
        congr 2 <;> omega
      have hpath : ∀ i < length - distance, IsEdge (short i) (short (i + 1)) := by
        intro i hi
        by_cases hfirst : i < first
        · unfold short
          rw [if_pos hfirst]
          by_cases hnext : i + 1 < first
          · rw [if_pos hnext]
            exact hedge _ (by omega)
          · have heq : i + 1 = first := by omega
            rw [if_neg hnext, heq, ← hloop, ← heq]
            exact hedge _ (by omega)
        · unfold short
          rw [if_neg hfirst, if_neg (by omega)]
          rw [show i + 1 + distance = i + distance + 1 by omega]
          exact hedge _ (by omega)
      have hboundShort := ih (length - distance) (by omega) short hpath
      let tail := length - (first + distance)
      have hfull : first + distance + tail = length := by dsimp [tail]; omega
      have herased : first + tail = length - distance := by dsimp [tail]; omega
      rw [← herased, sum_range_add] at hboundShort
      have hfirstSum : ∑ i ∈ range first, cost short i = ∑ i ∈ range first, cost path i :=
        sum_congr rfl (fun i hi => hbefore i (mem_range.mp hi))
      have hlastSum : ∑ i ∈ range tail, cost short (first + i) =
          ∑ i ∈ range tail, cost path (first + distance + i) :=
        sum_congr rfl (fun i _ => hafter i)
      rw [hfirstSum, hlastSum] at hboundShort
      rw [← hfull, sum_range_add, sum_range_add]
      linarith only [hboundShort, hcycle]
    · let vertices (i : Fin (length + 1)) := path i.val
      have hinj : Function.Injective vertices := by
        intro i j heq
        apply Fin.ext
        by_contra! hne
        have hlt (p q : Fin (length + 1)) (hpq : p.val < q.val) (h : path p.val = path q.val) : False := by
          have hs : p.val + (q.val - p.val) = q.val := by omega
          exact hrepeat ⟨q.val - p.val, by omega, p.val, by rw [hs]; have := q.isLt; omega, by rw [hs]; exact h⟩
        rcases lt_or_gt_of_ne hne with hlt' | hlt'
        · exact hlt i j hlt' heq
        · exact hlt j i hlt' heq.symm
      have hcard : length + 1 ≤ Fintype.card (slice.Vertex sector.val) := by
        simpa using Fintype.card_le_of_injective vertices hinj
      calc
        ∑ i ∈ range length, cost path i ≤ ∑ _ ∈ range length, bound :=
          sum_le_sum (fun i _ => hbound (path i) (path (i + 1)))
        _ = length * bound := by simp
        _ ≤ Fintype.card (slice.Vertex sector.val) * bound :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (show length ≤ Fintype.card (slice.Vertex sector.val) by omega)) hnonneg

/-- A common additive error for every path in a sector. The error is independent
of the starting column and the number of edges. -/
theorem exists_pathWeight_bound (slice : ColumnSlice) (sector : slice.Sector) :
    ∃ bound : ℚ, ∀ length : ℕ, ∀ path : ℕ → slice.Vertex sector.val,
      (∀ i < length, IsEdge (path i) (path (i + 1))) →
      ∑ i ∈ range length, (slice.edgeWeight sector.val (path i) (path (i + 1)) : ℚ) ≤
        length * (slice.cyclePeak - slice.a₀) + bound := by
  classical
  let adjusted (pair : slice.Vertex sector.val × slice.Vertex sector.val) : ℚ :=
    (slice.edgeWeight sector.val pair.1 pair.2 : ℚ) - (slice.cyclePeak - slice.a₀)
  let weights := insert 0 (univ.image adjusted)
  let bound := weights.max' ⟨0, mem_insert_self ..⟩
  have hnonneg : 0 ≤ bound := le_max' _ _ (mem_insert_self ..)
  have hbound (left right : slice.Vertex sector.val) : adjusted (left, right) ≤ bound :=
    le_max' _ _ (mem_insert_of_mem (mem_image_of_mem _ (mem_univ (left, right))))
  refine ⟨Fintype.card (slice.Vertex sector.val) * bound, fun length path hedge => ?_⟩
  have h := slice.sum_centered_edgeWeight_le sector bound hnonneg hbound length path hedge
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at h
  linarith only [h]

end FLatticePaper.GeneralK.ColumnSlice
