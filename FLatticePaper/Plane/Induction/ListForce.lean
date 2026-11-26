import FLatticePaper.Plane.Induction.ListPrefix

/-! # The per-entry trichotomy of the first list entries, from the route

For an entry `e` of the first `r` positions of a displayed list, its route ends at the next port `y` (along the arc). If `y ∈ S`
(the route stays in `S`), then either `y` is an earlier entry of the list (the pair is `(c₀, 0)`), or `y` has pair `(c₀, −1)` (minus) or
`(c₀, −1)` (plus), so `y` is a componentwise lower site of `S` with `K(y) < c₀`, which contradicts the minimum of `K` on `S`. This is the
trichotomy with no fan branch. -/

namespace FLatticePaper.ListForce

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.ContactCone

/-- **Prefix removal without a fan branch.** -/
theorem prefix_removal_nofan (S : Set Site) (P J : Site → ℤ) (c0 : ℤ) (ent : ℕ → Site) (N : ℕ)
    (hKmin : ∀ w ∈ S, c0 ≤ P w + J w)
    (hent : ∀ k < N, P (ent k) = c0 ∧ J (ent k) = 0)
    (hforce : ∀ k < N, ent k ∈ S →
      (∃ w ∈ S, P w ≤ P (ent k) ∧ J w ≤ J (ent k) ∧ (P w < P (ent k) ∨ J w < J (ent k))) ∨
      (∃ j < k, ent j ∈ S)) :
    ∀ k < N, ent k ∉ S := by
  refine FreeSchedule.ordered_removal S ent N ?_
  intro k hk hmem hIH
  rcases hforce k hk hmem with ⟨w, hwS, hwP, hwJ, hlt⟩ | ⟨j, hj, hjS⟩
  · have h1 := hKmin w hwS
    have h2 := hent k hk
    rcases hlt with hlt | hlt <;> linarith [h2.1, h2.2]
  · exact hIH j hj hjS

/-- **The minus trichotomy.** The entry at position `k < r` is `vAt (r − k)`; its route exit is `vAt (r − k + 1)`. If the route stays in
`S`, the entry has a componentwise lower site in `S` (only at `k = 0`, where the exit is `V_{r+1}` with `J = −1`) or an earlier entry in `S`. -/
theorem minus_hforce_route (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (r : ℤ) (hr0 : 0 ≤ r)
    (hrL2 : r ≤ frame.child.den + frame.child.num - 2)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F (-1) (VChain.vpath frame k) = if (k : ℤ) ≤ r then 0 else -1)
    (S : Set Site)
    (hroute : ∀ k : ℕ, (k : ℤ) < r → RowAt.vAt frame (r - (k : ℤ)) ∈ S →
      RowAt.vAt frame (r - (k : ℤ) + 1) ∈ S) :
    ∀ k : ℕ, k < r.toNat → RowAt.vAt frame (r - (k : ℤ)) ∈ S →
      (∃ w ∈ S, frame.price F w ≤ frame.price F (RowAt.vAt frame (r - (k : ℤ))) ∧
        frame.roundedSlip F (-1) w ≤ frame.roundedSlip F (-1) (RowAt.vAt frame (r - (k : ℤ))) ∧
        (frame.price F w < frame.price F (RowAt.vAt frame (r - (k : ℤ))) ∨
          frame.roundedSlip F (-1) w < frame.roundedSlip F (-1) (RowAt.vAt frame (r - (k : ℤ))))) ∨
      (∃ j < k, RowAt.vAt frame (r - (j : ℤ)) ∈ S) := by
  intro k hk hin
  have hkr : (k : ℤ) < r := by omega
  have hy := hroute k hkr hin
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    left
    have hr1 : (1 : ℤ) ≤ r := by omega
    have he := ListPrefix.minus_entry_pair frame F hP r (by omega) hpat r hr1 le_rfl
    have hrL : r + 1 < frame.child.den + frame.child.num := by omega
    have hwV : RowAt.vAt frame (r + 1) = VChain.vpath frame (r + 1).toNat := by
      have h := RowAt.vAt_nat frame (r + 1).toNat (by omega)
      rw [Int.toNat_of_nonneg (by omega)] at h
      exact h
    have hPw : frame.price F (RowAt.vAt frame (r + 1)) = frame.cutPrice := by
      rw [hwV]
      exact PriceDeck.price_on_freeV frame F hP.strips (ListPrefix.vpath_freeV_all frame _ (by omega))
    have hJw : frame.roundedSlip F (-1) (RowAt.vAt frame (r + 1)) = -1 := by
      rw [hwV, hpat (r + 1).toNat (by omega), if_neg (by omega)]
    refine ⟨RowAt.vAt frame (r - ((0 : ℕ) : ℤ) + 1), hy, ?_, ?_, ?_⟩
    · simp only [Nat.cast_zero, sub_zero]
      rw [hPw, he.1]
    · simp only [Nat.cast_zero, sub_zero]
      rw [hJw, he.2]
      norm_num
    · right
      simp only [Nat.cast_zero, sub_zero]
      rw [hJw, he.2]
      norm_num
  · right
    refine ⟨k - 1, by omega, ?_⟩
    have e2 : r - ((k - 1 : ℕ) : ℤ) = r - (k : ℤ) + 1 := by omega
    rw [e2]
    exact hy

/-- **The plus trichotomy.** The entry at position `k < r` is `vAt (−r − 1 + k)`; its route exit is `vAt (−r − 2 + k)`. If the route stays
in `S`, the first entry has the lower site `vAt (−r − 2)` (pair `(c₀, −1)`), and the others have an earlier entry in `S`. -/
theorem plus_hforce_route (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (r : ℤ) (hr0 : 0 ≤ r)
    (hr2 : r ≤ frame.child.den + frame.child.num - 2)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F 1 (VChain.vpath frame k) =
        if (k : ℤ) ≤ frame.child.den + frame.child.num - r - 2 then 0 else 1)
    (S : Set Site)
    (hroute : ∀ k : ℕ, (k : ℤ) < r → RowAt.vAt frame (-r - 1 + (k : ℤ)) ∈ S →
      RowAt.vAt frame (-r - 2 + (k : ℤ)) ∈ S) :
    ∀ k : ℕ, k < r.toNat → RowAt.vAt frame (-r - 1 + (k : ℤ)) ∈ S →
      (∃ w ∈ S, frame.price F w ≤ frame.price F (RowAt.vAt frame (-r - 1 + (k : ℤ))) ∧
        frame.roundedSlip F 1 w ≤ frame.roundedSlip F 1 (RowAt.vAt frame (-r - 1 + (k : ℤ))) ∧
        (frame.price F w < frame.price F (RowAt.vAt frame (-r - 1 + (k : ℤ))) ∨
          frame.roundedSlip F 1 w < frame.roundedSlip F 1 (RowAt.vAt frame (-r - 1 + (k : ℤ))))) ∨
      (∃ j < k, RowAt.vAt frame (-r - 1 + (j : ℤ)) ∈ S) := by
  intro k hk hin
  have hkr : (k : ℤ) < r := by omega
  have hy := hroute k hkr hin
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    left
    have hr1 : (1 : ℤ) ≤ r := by omega
    have he := ListPrefix.plus_entry_pair frame F hP r hr2 hpat (-r - 1) (le_refl _) (by omega)
    -- the exit `vAt (−r − 2)`: its pair is `(c₀, −1)`
    have hk0 : (-r - 2 + (frame.child.den + frame.child.num)) =
        ((frame.child.den + frame.child.num - r - 2).toNat : ℤ) := by omega
    have hVA : RowAt.vAt frame (-r - 2 + (frame.child.den + frame.child.num)) =
        VChain.vpath frame (frame.child.den + frame.child.num - r - 2).toNat := by
      rw [hk0]
      exact RowAt.vAt_nat frame _ (by omega)
    have hJ0 : frame.roundedSlip F 1 (RowAt.vAt frame (-r - 2 + (frame.child.den + frame.child.num))) = 0 := by
      rw [hVA, hpat _ (by omega), if_pos (by omega)]
    have hPV : frame.price F (RowAt.vAt frame (-r - 2 + (frame.child.den + frame.child.num))) =
        frame.cutPrice := by
      rw [hVA]
      exact PriceDeck.price_on_freeV frame F hP.strips (ListPrefix.vpath_freeV_all frame _ (by omega))
    have hsh := RowAt.vAt_add_len frame (-r - 2)
    have hsh2 : RowAt.vAt frame (-r - 2) + ((frame.child.num - frame.child.den, frame.child.num + frame.child.den) : Site) =
        RowAt.vAt frame (-r - 2 + (frame.child.den + frame.child.num)) := hsh.symm
    have hJsh := HPaidInputs.roundedSlip_V frame F hP 1 (RowAt.vAt frame (-r - 2))
    have hPsh := HPaidInputs.price_V frame F hP (RowAt.vAt frame (-r - 2))
    rw [hsh2, hJ0] at hJsh
    rw [hsh2, hPV] at hPsh
    have hJw : frame.roundedSlip F 1 (RowAt.vAt frame (-r - 2)) = -1 := by linarith
    have hPw : frame.price F (RowAt.vAt frame (-r - 2)) = frame.cutPrice := by linarith
    have hy' : RowAt.vAt frame (-r - 2 + ((0 : ℕ) : ℤ)) ∈ S := by simpa using hy
    refine ⟨RowAt.vAt frame (-r - 2 + ((0 : ℕ) : ℤ)), hy', ?_, ?_, ?_⟩
    · simp only [Nat.cast_zero, add_zero]
      rw [hPw, he.1]
    · simp only [Nat.cast_zero, add_zero]
      rw [hJw, he.2]
      norm_num
    · right
      simp only [Nat.cast_zero, add_zero]
      rw [hJw, he.2]
      norm_num
  · right
    refine ⟨k - 1, by omega, ?_⟩
    have e2 : -r - 1 + ((k - 1 : ℕ) : ℤ) = -r - 2 + (k : ℤ) := by omega
    rw [e2]
    exact hy

/-- **The minus entries are removed.** The first `r` minus entries are not in `S` (given the minimum of `K` and the route). -/
theorem minus_removed_route (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (r : ℤ) (hr0 : 0 ≤ r)
    (hrL2 : r ≤ frame.child.den + frame.child.num - 2)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F (-1) (VChain.vpath frame k) = if (k : ℤ) ≤ r then 0 else -1)
    (S : Set Site)
    (hKmin : ∀ w ∈ S, frame.cutPrice ≤ frame.price F w + frame.roundedSlip F (-1) w)
    (hroute : ∀ k : ℕ, (k : ℤ) < r → RowAt.vAt frame (r - (k : ℤ)) ∈ S →
      RowAt.vAt frame (r - (k : ℤ) + 1) ∈ S) :
    ∀ k : ℕ, k < r.toNat → RowAt.vAt frame (r - (k : ℤ)) ∉ S := by
  refine prefix_removal_nofan S (fun w => frame.price F w) (fun w => frame.roundedSlip F (-1) w) frame.cutPrice
    (fun i : ℕ => RowAt.vAt frame (r - (i : ℤ))) r.toNat hKmin ?_
    (minus_hforce_route frame F hP r hr0 hrL2 hpat S hroute)
  intro i hi
  exact ListPrefix.minus_entry_pair frame F hP r (by omega) hpat (r - (i : ℤ)) (by omega) (by omega)

/-- **The plus entries are removed.** The first `r` plus entries are not in `S`. -/
theorem plus_removed_route (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (r : ℤ) (hr0 : 0 ≤ r)
    (hr2 : r ≤ frame.child.den + frame.child.num - 2)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F 1 (VChain.vpath frame k) =
        if (k : ℤ) ≤ frame.child.den + frame.child.num - r - 2 then 0 else 1)
    (S : Set Site)
    (hKmin : ∀ w ∈ S, frame.cutPrice ≤ frame.price F w + frame.roundedSlip F 1 w)
    (hroute : ∀ k : ℕ, (k : ℤ) < r → RowAt.vAt frame (-r - 1 + (k : ℤ)) ∈ S →
      RowAt.vAt frame (-r - 2 + (k : ℤ)) ∈ S) :
    ∀ k : ℕ, k < r.toNat → RowAt.vAt frame (-r - 1 + (k : ℤ)) ∉ S := by
  refine prefix_removal_nofan S (fun w => frame.price F w) (fun w => frame.roundedSlip F 1 w) frame.cutPrice
    (fun i : ℕ => RowAt.vAt frame (-r - 1 + (i : ℤ))) r.toNat hKmin ?_
    (plus_hforce_route frame F hP r hr0 hr2 hpat S hroute)
  intro i hi
  exact ListPrefix.plus_entry_pair frame F hP r hr2 hpat (-r - 1 + (i : ℤ)) (by omega) (by omega)

/-- **The minus core candidates from the route.** A boundary site of `S` with `K ≥ c₀` is `H_0` or `V_0`, given that the first minus entries
are removed (by the route trichotomy). -/
theorem minus_hcand_route (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (r : ℤ) (hr0 : 0 ≤ r)
    (hrL2 : r ≤ frame.child.den + frame.child.num - 2)
    (hPH : ∀ h : Site, frame.freeH h → frame.price F h ≤ frame.cutPrice ∧
      (frame.price F h = frame.cutPrice → h = FLatticePaper.Induction.hFirst))
    (hJH : ∀ h : Site, frame.freeH h → frame.roundedSlip F (-1) h = 0)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F (-1) (VChain.vpath frame k) = if (k : ℤ) ≤ r then 0 else -1)
    (S : Set Site)
    (hKmin : ∀ w ∈ S, frame.cutPrice ≤ frame.price F w + frame.roundedSlip F (-1) w)
    (hroute : ∀ k : ℕ, (k : ℤ) < r → RowAt.vAt frame (r - (k : ℤ)) ∈ S →
      RowAt.vAt frame (r - (k : ℤ) + 1) ∈ S)
    (b : Site) (hbS : b ∈ S) (hbC : b ∈ frame.closedPolygon) (hbO : ¬ frame.openRect b) :
    b = FLatticePaper.Induction.hFirst ∨ b = FLatticePaper.Induction.vFirst := by
  have hK := hKmin b hbS
  rcases BoundaryPair.minus_boundary_K frame F hP r hPH hJH hpat b hbC hbO hK with hH | ⟨k, hkr, hkL, hbk⟩
  · exact Or.inl hH
  · by_cases hk0 : k = 0
    · right
      rw [hbk, hk0, VChain.vpath_zero]
    · exfalso
      have hvk : RowAt.vAt frame (k : ℤ) = b := by
        rw [RowAt.vAt_nat frame k hkL, hbk]
      have e : r - (((r - (k : ℤ)).toNat : ℕ) : ℤ) = (k : ℤ) := by omega
      apply minus_removed_route frame F hP r hr0 hrL2 hpat S hKmin hroute ((r - (k : ℤ)).toNat) (by omega)
      rw [e, hvk]
      exact hbS

/-- **The plus core candidates from the route.** A boundary site of `E − V` in `S` with `K ≥ c₀` is `H_0` or `V_{−1}`, given the removal of
the first plus entries. -/
theorem plus_hcand_route (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (r : ℤ) (hr0 : 0 ≤ r)
    (hr2 : r ≤ frame.child.den + frame.child.num - 2)
    (hPH : ∀ h : Site, frame.freeH h → frame.price F h ≤ frame.cutPrice ∧
      (frame.price F h = frame.cutPrice → h = FLatticePaper.Induction.hFirst))
    (hJH : ∀ h : Site, frame.freeH h → frame.roundedSlip F 1 h = 0)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F 1 (VChain.vpath frame k) =
        if (k : ℤ) ≤ frame.child.den + frame.child.num - r - 2 then 0 else 1)
    (S : Set Site)
    (hKmin : ∀ w ∈ S, frame.cutPrice ≤ frame.price F w + frame.roundedSlip F 1 w)
    (hroute : ∀ k : ℕ, (k : ℤ) < r → RowAt.vAt frame (-r - 1 + (k : ℤ)) ∈ S →
      RowAt.vAt frame (-r - 2 + (k : ℤ)) ∈ S)
    (b : Site) (hbS : b ∈ S)
    (hw : (b.1 + (frame.child.num - frame.child.den), b.2 + (frame.child.num + frame.child.den)) ∈
      frame.closedPolygon)
    (hnot : ¬ frame.openRect (b.1 + (frame.child.num - frame.child.den), b.2 + (frame.child.num + frame.child.den))) :
    b = FLatticePaper.Induction.hFirst ∨ b = RowAt.vAt frame (-1) := by
  have hK := hKmin b hbS
  rcases BoundaryPair.plus_boundary_K frame F hP r hPH hJH hpat b hw hnot hK with hH | ⟨j, hj1, hj2, hbj⟩
  · exact Or.inl hH
  · by_cases hj : j = -1
    · right
      rw [hbj, hj]
    · exfalso
      have e : -r - 1 + (((j + r + 1).toNat : ℕ) : ℤ) = j := by omega
      apply plus_removed_route frame F hP r hr0 hr2 hpat S hKmin hroute ((j + r + 1).toNat) (by omega)
      rw [e, ← hbj]
      exact hbS

end FLatticePaper.ListForce
