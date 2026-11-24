import FLatticePaper.Plane.Induction.EPolicyTransfer

/-!
# The native covering of the value inequalities (task 118, W1 base)

The three edge inequalities of the signed policy are stated in increments: `SE` (slip), `PE` (price) and `CE` (chain) at a centre
`r` along a unit step `e`. They are invariant under the deck (`EPolicyTransfer`). At a native centre the policy keeps the step
`ECover`: the white rule gives `selDisp`, the black rule gives the two axis neighbours. This module proves the translation between
the increment forms and the slip, price and chain forms, and the policy hypothesis `ePolicy` at a native centre from `ECover`.
-/

namespace FLatticePaper.EPolicy

open FLatticePaper FLatticePaper.Induction
open FLatticePaper.Construction
open FLatticePaper.PureRank
open FLatticePaper.Farey

/-- The slip inequality of the step `e` at `r`, in increments. -/
def SE (k : ℕ) (η : ℤ) (r e : Site) : Prop :=
  incr (reciprocalField k) e r ≤ incr (reciprocalField k) e (r + η • (reciprocalFrame k).shortShift)

/-- The price inequality of the step `e` at `r`, in increments. -/
def PE (k : ℕ) (r e : Site) : Prop :=
  incr (reciprocalField k) e r - incr (reciprocalField k) e (r - (1, -1)) ≤ e.2

/-- The chain inequality of the step `e` at `r`, in increments. -/
def CE (k : ℕ) (η : ℤ) (r e : Site) : Prop :=
  incr (reciprocalField k) e r - incr (reciprocalField k) e (r + η • (reciprocalFrame k).shortShift - (1, -1)) ≤ e.2

/-- The policy keeps the step `e` at the native centre `r`: the white rule gives `selDisp`, the black rule the axis neighbours. -/
def ECover (k : ℕ) (η : ℤ) (r e : Site) : Prop :=
  (laplacian (reciprocalField k) r = 0 ∧ e = selDisp (2 * (k : ℤ) + 3) η r) ∨
    (laplacian (reciprocalField k) r = -1 ∧ (e = incomingNeg r - r ∨ e = incomingPos r - r))

theorem SE_of_slip (k : ℕ) (η : ℤ) (r e : Site)
    (h : (reciprocalFrame k).slip (reciprocalField k) η (r + e) ≤ (reciprocalFrame k).slip (reciprocalField k) η r) :
    SE k η r e := by
  have := slip_edge_sub (reciprocalField k) (reciprocalFrame k) η r e
  unfold SE
  linarith

theorem PE_of_price (k : ℕ) (r e : Site)
    (h : (reciprocalFrame k).price (reciprocalField k) (r + e) ≤ (reciprocalFrame k).price (reciprocalField k) r) :
    PE k r e := by
  have := price_edge_sub k (reciprocalField k) r e
  unfold PE
  linarith

theorem CE_of_chain (k : ℕ) (η : ℤ) (r e : Site)
    (h : (reciprocalFrame k).chainPotential (reciprocalField k) η (r + e) ≤
      (reciprocalFrame k).chainPotential (reciprocalField k) η r) :
    CE k η r e := by
  have := chain_edge_sub k (reciprocalField k) η r e
  unfold CE
  linarith

theorem slip_of_SE (k : ℕ) (η : ℤ) (r e : Site) (h : SE k η r e) :
    (reciprocalFrame k).slip (reciprocalField k) η (r + e) ≤ (reciprocalFrame k).slip (reciprocalField k) η r :=
  slip_edge_le (reciprocalField k) (reciprocalFrame k) η r e h

theorem price_of_PE (k : ℕ) (r e : Site) (h : PE k r e) :
    (reciprocalFrame k).price (reciprocalField k) (r + e) ≤ (reciprocalFrame k).price (reciprocalField k) r :=
  price_edge_le k (reciprocalField k) r e h

theorem chain_of_CE (k : ℕ) (η : ℤ) (r e : Site) (h : CE k η r e) :
    (reciprocalFrame k).chainPotential (reciprocalField k) η (r + e) ≤
      (reciprocalFrame k).chainPotential (reciprocalField k) η r :=
  chain_edge_le k (reciprocalField k) η r e h

/-- The policy edge at a native centre, from the covering data: the white rule (`ePolicy_white`) or the black rule
(`ePolicy_black`). -/
theorem ePolicy_of_ECover (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (r e : Site)
    (hr : NativeP (2 * (k : ℤ) + 3) r) (hc : ECover k η r e) :
    ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) r (r + e) := by
  rcases hc with ⟨hl, he⟩ | ⟨hl, he | he⟩
  · rw [ePolicy_white k η hη r (r + e) hl]
    rw [selDisp_nativeRep k η hη hr, add_sub_cancel_left, he]
  · have hb := ePolicy_black (d := 2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) η
      (laplacian (reciprocalField k)) r hl
    rw [he, add_sub_cancel]
    exact hb.1
  · have hb := ePolicy_black (d := 2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) η
      (laplacian (reciprocalField k)) r hl
    rw [he, add_sub_cancel]
    exact hb.2

/-- On an even native centre the covering step is horizontal. -/
theorem ecover_axis_even (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (r e : Site) (hE : EvenSite r)
    (hc : ECover k η r e) : e = (1, 0) ∨ e = (-1, 0) := by
  rcases hc with ⟨-, he⟩ | ⟨-, he | he⟩
  · unfold selDisp at he
    rw [if_pos hE] at he
    split_ifs at he <;> subst he <;> rcases hη with rfl | rfl <;> simp
  · right
    rw [he]
    unfold incomingNeg
    rw [if_pos hE]
    ext <;> (simp; try ring)
  · left
    rw [he]
    unfold incomingPos
    rw [if_pos hE]
    ext <;> (simp; try ring)

/-- On an odd native centre the covering step is vertical. -/
theorem ecover_axis_odd (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (r e : Site) (hE : ¬ EvenSite r)
    (hc : ECover k η r e) : e = (0, 1) ∨ e = (0, -1) := by
  rcases hc with ⟨-, he⟩ | ⟨-, he | he⟩
  · unfold selDisp at he
    rw [if_neg hE] at he
    split_ifs at he <;> subst he <;> rcases hη with rfl | rfl <;> simp
  · right
    rw [he]
    unfold incomingNeg
    rw [if_neg hE]
    ext <;> (simp; try ring)
  · left
    rw [he]
    unfold incomingPos
    rw [if_neg hE]
    ext <;> (simp; try ring)

/-- The step `e` of a covering on an even centre `(x, y)` is `(s, 0)`, with `s = 1` or `s = -1`. -/
theorem ecover_horiz (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (x y : ℤ) (e : Site) (hpar : (x + y) % 2 = 0)
    (hc : ECover k η (x, y) e) : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ e = (s, 0) := by
  have hE : EvenSite (x, y) := by unfold EvenSite; exact hpar
  rcases ecover_axis_even k η hη (x, y) e hE hc with h | h
  · exact ⟨1, Or.inl rfl, h⟩
  · exact ⟨-1, Or.inr rfl, h⟩

/-- The step `e` of a covering on an odd centre `(x, y)` is `(0, s)`, with `s = 1` or `s = -1`. -/
theorem ecover_vert (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (x y : ℤ) (e : Site) (hpar : (x + y) % 2 = 1)
    (hc : ECover k η (x, y) e) : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ e = (0, s) := by
  have hE : ¬ EvenSite (x, y) := by unfold EvenSite; omega
  rcases ecover_axis_odd k η hη (x, y) e hE hc with h | h
  · exact ⟨1, Or.inl rfl, h⟩
  · exact ⟨-1, Or.inr rfl, h⟩

/-- The interior box, even centre: the horizontal slip, price and chain inequalities. -/
theorem cov_interior_even (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (x y : ℤ) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) (x, y))
    (hbox : 6 - (2 * (k : ℤ) + 3) ≤ x ∧ x ≤ 2 * (k : ℤ) + 3 - 3 ∧ 1 ≤ y ∧ y ≤ 2 * (k : ℤ) + 3 - 1 ∧
      4 ≤ x + y ∧ x + y ≤ 2 * (k : ℤ) + 3 - 1)
    (hpar : (x + y) % 2 = 0) (hc : ECover k η (x, y) e) :
    SE k η (x, y) e ∧ PE k (x, y) e ∧ CE k η (x, y) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_horiz k η hη x y e hpar hc
  have hret : x = 1 ∨ (s, 0) = selDisp (2 * (k : ℤ) + 3) η (x, y) := by
    rcases hc with ⟨hl, he⟩ | ⟨hl, he | he⟩
    · exact Or.inr he
    · left
      have h := laplacian_reciprocal_native k hN
      rw [hl] at h
      have hE : EvenSite (x, y) := by unfold EvenSite; exact hpar
      rw [if_pos hE] at h
      by_contra hne
      rw [if_neg hne] at h
      norm_num at h
    · left
      have h := laplacian_reciprocal_native k hN
      rw [hl] at h
      have hE : EvenSite (x, y) := by unfold EvenSite; exact hpar
      rw [if_pos hE] at h
      by_contra hne
      rw [if_neg hne] at h
      norm_num at h
  exact ⟨SE_of_slip k η (x, y) (s, 0) (slip_horiz_le k η x y s hη hs hbox hpar hret),
    PE_of_price k (x, y) (s, 0) (price_horiz_le k η x y s hs hbox hpar hret),
    CE_of_chain k η (x, y) (s, 0) (chain_horiz_le k η x y s hη hs hbox hpar hret)⟩

/-- The interior box, odd centre: the vertical slip, price and chain inequalities. -/
theorem cov_interior_odd (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (x y : ℤ) (e : Site)
    (hbox : 6 - (2 * (k : ℤ) + 3) ≤ x ∧ x ≤ 2 * (k : ℤ) + 3 - 3 ∧ 1 ≤ y ∧ y ≤ 2 * (k : ℤ) + 3 - 1 ∧
      4 ≤ x + y ∧ x + y ≤ 2 * (k : ℤ) + 3 - 1)
    (hpar : (x + y) % 2 = 1) (hc : ECover k η (x, y) e) :
    SE k η (x, y) e ∧ PE k (x, y) e ∧ CE k η (x, y) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_vert k η hη x y e hpar hc
  exact ⟨SE_of_slip k η (x, y) (0, s) (slip_vert_le k η x y s hη hs hbox),
    PE_of_price k (x, y) (0, s) (price_vert_le k x y s hs hbox),
    CE_of_chain k η (x, y) (0, s) (chain_vert_le k η x y s hη hs hbox)⟩

/-- Lower diagonal, sum 1: the vertical inequalities. -/
theorem cov_low1 (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (x y : ℤ) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) (x, y)) (hsum : x + y = 1) (hy : 1 ≤ y) (hx : 6 - (2 * (k : ℤ) + 3) ≤ x)
    (hc : ECover k η (x, y) e) : SE k η (x, y) e ∧ PE k (x, y) e ∧ CE k η (x, y) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_vert k η hη x y e (by omega) hc
  have hpol := ePolicy_of_ECover k η hη (x, y) (0, s) hN hc
  exact ⟨SE_of_slip k η (x, y) (0, s) (slip_low1_v k η x y s hη hN hsum hy hx hpol),
    PE_of_price k (x, y) (0, s) (price_low1_v k η x y s hη hN hsum hy hx hpol),
    CE_of_chain k η (x, y) (0, s) (chain_low1_v k η x y s hη hN hsum hy hx hpol)⟩

/-- Lower diagonal, sum 2: the horizontal inequalities. -/
theorem cov_low2 (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (x y : ℤ) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) (x, y)) (hsum : x + y = 2) (hy : 1 ≤ y) (hx : 6 - (2 * (k : ℤ) + 3) ≤ x)
    (hc : ECover k η (x, y) e) : SE k η (x, y) e ∧ PE k (x, y) e ∧ CE k η (x, y) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_horiz k η hη x y e (by omega) hc
  have hpol := ePolicy_of_ECover k η hη (x, y) (s, 0) hN hc
  exact ⟨SE_of_slip k η (x, y) (s, 0) (slip_low2_h k η x y s hη hs hsum hy hx hpol),
    PE_of_price k (x, y) (s, 0) (price_low2_h k η x y s hη hs hsum hy hx hpol),
    CE_of_chain k η (x, y) (s, 0) (chain_low2_h k η x y s hη hs hsum hy hx hpol)⟩

/-- Lower diagonal, sum 3: the vertical inequalities. -/
theorem cov_low3 (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (x y : ℤ) (e : Site)
    (hsum : x + y = 3) (hy : 1 ≤ y) (hx : 6 - (2 * (k : ℤ) + 3) ≤ x)
    (hc : ECover k η (x, y) e) : SE k η (x, y) e ∧ PE k (x, y) e ∧ CE k η (x, y) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_vert k η hη x y e (by omega) hc
  exact ⟨SE_of_slip k η (x, y) (0, s) (slip_low3_v k η x y s hη hs hsum hy hx),
    PE_of_price k (x, y) (0, s) (price_low3_v k x y s hs hsum hy hx),
    CE_of_chain k η (x, y) (0, s) (chain_low3_v k η x y s hη hs hsum hy hx)⟩

/-- The top diagonal, sum `d + 2`: the vertical inequalities. -/
theorem cov_top (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (x y : ℤ) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) (x, y)) (hsum : x + y = (2 * (k : ℤ) + 3) + 2) (hx : 3 ≤ x)
    (hxd : x ≤ 2 * (k : ℤ) + 3) (hc : ECover k η (x, y) e) :
    SE k η (x, y) e ∧ PE k (x, y) e ∧ CE k η (x, y) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_vert k η hη x y e (by omega) hc
  have hpol := ePolicy_of_ECover k η hη (x, y) (0, s) hN hc
  exact ⟨SE_of_slip k η (x, y) (0, s) (slip_top_v k η x y s hη hsum hx hxd hpol),
    PE_of_price k (x, y) (0, s) (price_top_v k η x y s hη hsum hx hxd hpol),
    CE_of_chain k η (x, y) (0, s) (chain_top_v k η x y s hη hsum hx hxd hpol)⟩

/-- The sum `d` diagonal (`x >= 3`, `y >= 2`): the vertical inequalities. -/
theorem cov_sumd (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (x y : ℤ) (e : Site)
    (hsum : x + y = 2 * (k : ℤ) + 3) (hx : 3 ≤ x) (hy : 2 ≤ y) (hc : ECover k η (x, y) e) :
    SE k η (x, y) e ∧ PE k (x, y) e ∧ CE k η (x, y) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_vert k η hη x y e (by omega) hc
  exact ⟨SE_of_slip k η (x, y) (0, s) (slip_sumd_v k η x y s hη hs hsum hx hy),
    PE_of_price k (x, y) (0, s) (price_sumd_v k x y s hs hsum hx hy),
    CE_of_chain k η (x, y) (0, s) (chain_sumd_v k η x y s hη hs hsum hx hy)⟩

/-- The sum `d + 1` diagonal (`x >= 2`, `y >= 2`): the horizontal inequalities. -/
theorem cov_sumd1 (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (x y : ℤ) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) (x, y)) (hsum : x + y = (2 * (k : ℤ) + 3) + 1) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hc : ECover k η (x, y) e) : SE k η (x, y) e ∧ PE k (x, y) e ∧ CE k η (x, y) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_horiz k η hη x y e (by omega) hc
  have hpol := ePolicy_of_ECover k η hη (x, y) (s, 0) hN hc
  exact ⟨SE_of_slip k η (x, y) (s, 0) (slip_sumd1_h k η x y s hη hsum hx hy hpol),
    PE_of_price k (x, y) (s, 0) (price_sumd1_h k η x y s hη hsum hx hy hpol),
    CE_of_chain k η (x, y) (s, 0) (chain_sumd1_h k η x y s hη hsum hx hy hpol)⟩

/-- The bottom row at the odd centre `(1, 0)`. -/
theorem cov_bot1 (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (0 : ℤ))) (hc : ECover k η ((1 : ℤ), (0 : ℤ)) e) :
    SE k η ((1 : ℤ), (0 : ℤ)) e ∧ PE k ((1 : ℤ), (0 : ℤ)) e ∧ CE k η ((1 : ℤ), (0 : ℤ)) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_vert k η hη 1 0 e (by norm_num) hc
  have hpol := ePolicy_of_ECover k η hη ((1 : ℤ), (0 : ℤ)) (0, s) hN hc
  have hsg : s = s := rfl
  exact ⟨SE_of_slip k η _ (0, s) (slip_bot1 k η s hη hpol),
    PE_of_price k _ (0, s) (price_bot1 k η s hη hpol),
    CE_of_chain k η _ (0, s) (chain_bot1 k η s hη hpol)⟩

/-- The bottom row at the even centre `(2, 0)`. -/
theorem cov_bot2 (k : ℕ) (hk : 1 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (0 : ℤ))) (hc : ECover k η ((2 : ℤ), (0 : ℤ)) e) :
    SE k η ((2 : ℤ), (0 : ℤ)) e ∧ PE k ((2 : ℤ), (0 : ℤ)) e ∧ CE k η ((2 : ℤ), (0 : ℤ)) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_horiz k η hη 2 0 e (by norm_num) hc
  have hpol := ePolicy_of_ECover k η hη ((2 : ℤ), (0 : ℤ)) (s, 0) hN hc
  exact ⟨SE_of_slip k η _ (s, 0) (slip_bot2 k η s hη hk hpol),
    PE_of_price k _ (s, 0) (price_bot2 k η s hη hk hpol),
    CE_of_chain k η _ (s, 0) (chain_bot2 k η s hη hk hpol)⟩

/-- The bottom row, even centre `(x, 0)` with `4 <= x <= d - 3`. -/
theorem cov_bot_even (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (x : ℤ) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) (x, (0 : ℤ))) (hpar : x % 2 = 0) (hx : 4 ≤ x)
    (hxd : x ≤ (2 * (k : ℤ) + 3) - 3) (hc : ECover k η (x, (0 : ℤ)) e) :
    SE k η (x, (0 : ℤ)) e ∧ PE k (x, (0 : ℤ)) e ∧ CE k η (x, (0 : ℤ)) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_horiz k η hη x 0 e (by omega) hc
  have hpol := ePolicy_of_ECover k η hη (x, (0 : ℤ)) (s, 0) hN hc
  exact ⟨SE_of_slip k η _ (s, 0) (slip_bot_E k η x s hη hpar hx hxd hpol),
    PE_of_price k _ (s, 0) (price_bot_E k η x s hη hpar hx hxd hpol),
    CE_of_chain k η _ (s, 0) (chain_bot_E k η x s hη hpar hx hxd hpol)⟩

/-- The bottom row, odd centre `(x, 0)` with `3 <= x <= d - 2`. -/
theorem cov_bot_odd (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (x : ℤ) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) (x, (0 : ℤ))) (hpar : x % 2 = 1) (hx : 3 ≤ x)
    (hxd : x ≤ (2 * (k : ℤ) + 3) - 2) (hc : ECover k η (x, (0 : ℤ)) e) :
    SE k η (x, (0 : ℤ)) e ∧ PE k (x, (0 : ℤ)) e ∧ CE k η (x, (0 : ℤ)) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_vert k η hη x 0 e (by omega) hc
  have hpol := ePolicy_of_ECover k η hη (x, (0 : ℤ)) (0, s) hN hc
  exact ⟨SE_of_slip k η _ (0, s) (slip_bot_O k η x s hη hpar hx hxd hpol),
    PE_of_price k _ (0, s) (price_bot_O k η x s hη hpar hx hxd hpol),
    CE_of_chain k η _ (0, s) (chain_bot_O k η x s hη hpar hx hxd hpol)⟩

/-- The bottom row at `(d - 1, 0)`. -/
theorem cov_botR (k : ℕ) (hk : 1 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (x : ℤ) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) (x, (0 : ℤ))) (hx : x = 2 * (k : ℤ) + 2) (hc : ECover k η (x, (0 : ℤ)) e) :
    SE k η (x, (0 : ℤ)) e ∧ PE k (x, (0 : ℤ)) e ∧ CE k η (x, (0 : ℤ)) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_horiz k η hη x 0 e (by subst hx; omega) hc
  have hpol := ePolicy_of_ECover k η hη (x, (0 : ℤ)) (s, 0) hN hc
  exact ⟨SE_of_slip k η _ (s, 0) (slip_bot_R k η x s hη hk hx hpol),
    PE_of_price k _ (s, 0) (price_bot_R k η x s hη hk hx hpol),
    CE_of_chain k η _ (s, 0) (chain_bot_R k η x s hη hk hx hpol)⟩

/-- The bottom row at `(d, 0)`. -/
theorem cov_botOR (k : ℕ) (hk : 1 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3), (0 : ℤ)))
    (hc : ECover k η ((2 * (k : ℤ) + 3), (0 : ℤ)) e) :
    SE k η ((2 * (k : ℤ) + 3), (0 : ℤ)) e ∧ PE k ((2 * (k : ℤ) + 3), (0 : ℤ)) e ∧
      CE k η ((2 * (k : ℤ) + 3), (0 : ℤ)) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_vert k η hη (2 * (k : ℤ) + 3) 0 e (by omega) hc
  have hpol := ePolicy_of_ECover k η hη ((2 * (k : ℤ) + 3), (0 : ℤ)) (0, s) hN hc
  exact ⟨SE_of_slip k η _ (0, s) (slip_bot_OR k η s hη hk hpol),
    PE_of_price k _ (0, s) (price_bot_OR k η s hη hk hpol),
    CE_of_chain k η _ (0, s) (chain_bot_OR k η s hη hk hpol)⟩

/-- The class of a covered step is shared by deck translates: the covering data transfers along a deck vector. -/
theorem ecover_transfer (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (r0 r e : Site) (i j : ℤ)
    (hr : r = r0 + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j)
    (hn0 : NativeP (2 * (k : ℤ) + 3) r0) (hn : NativeP (2 * (k : ℤ) + 3) r) (hc : ECover k η r e) :
    ECover k η r0 e := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hlap : laplacian (reciprocalField k) r0 = laplacian (reciprocalField k) r := by
    rw [hr]; exact (laplacian_reciprocal_deck k r0 i j).symm
  rcases hc with ⟨hl, he⟩ | ⟨hl, he | he⟩
  · refine Or.inl ⟨by rw [hlap]; exact hl, ?_⟩
    have h1 := selDisp_nativeRep k η hη hn
    have h2 := selDisp_nativeRep_deck k η hη r0 i j
    have h3 := selDisp_nativeRep k η hη hn0
    rw [he, ← h1, hr, h2, h3]
  · refine Or.inr ⟨by rw [hlap]; exact hl, Or.inl ?_⟩
    rw [he, hr, incomingNeg_add (combine_sum_even hd i j)]
    abel
  · refine Or.inr ⟨by rw [hlap]; exact hl, Or.inr ?_⟩
    rw [he, hr, incomingPos_add (combine_sum_even hd i j)]
    abel

/-- The three inequalities are shared by deck translates. -/
theorem cov_shift (k : ℕ) (η : ℤ) (r0 r e : Site) (i j : ℤ)
    (hr : r = r0 + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j)
    (h : SE k η r0 e ∧ PE k r0 e ∧ CE k η r0 e) : SE k η r e ∧ PE k r e ∧ CE k η r e := by
  subst hr
  exact ⟨slip_inc_shift k η e r0 i j h.1, price_inc_shift k e r0 i j h.2.1, chain_inc_shift k η e r0 i j h.2.2⟩

/-- The bottom row `(x, 0)` for every `1 <= x <= d`. -/
theorem cov_bottom (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (x : ℤ) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) (x, (0 : ℤ))) (hx1 : 1 ≤ x) (hxd : x ≤ 2 * (k : ℤ) + 3)
    (hc : ECover k η (x, (0 : ℤ)) e) :
    SE k η (x, (0 : ℤ)) e ∧ PE k (x, (0 : ℤ)) e ∧ CE k η (x, (0 : ℤ)) e := by
  have hk1 : 1 ≤ (k : ℤ) := by omega
  rcases (by omega : x = 1 ∨ x = 2 ∨ (3 ≤ x ∧ x ≤ 2 * (k : ℤ) + 1 ∧ x % 2 = 1) ∨
      (4 ≤ x ∧ x ≤ 2 * (k : ℤ) ∧ x % 2 = 0) ∨ x = 2 * (k : ℤ) + 2 ∨ x = 2 * (k : ℤ) + 3) with
    h | h | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | h | h
  · subst h
    exact cov_bot1 k η hη e hN hc
  · subst h
    exact cov_bot2 k hk1 η hη e hN hc
  · exact cov_bot_odd k η hη x e hN h3 h1 (by omega) hc
  · exact cov_bot_even k η hη x e hN h3 h1 (by omega) hc
  · exact cov_botR k hk1 η hη x e hN h hc
  · subst h
    exact cov_botOR k hk1 η hη e hN hc

/-- A slip inequality at a point, given as a class inequality at the explicit target `q`. -/
theorem SE_of_cls (k : ℕ) (η : ℤ) {r q e : Site}
    (h : incr (reciprocalField k) e r ≤ incr (reciprocalField k) e q) (hab : r + η • (reciprocalFrame k).shortShift = q) :
    SE k η r e := by
  unfold SE
  rw [hab]
  exact h

/-- A price inequality at a point, given as a class inequality at the explicit target `q`. -/
theorem PE_of_cls (k : ℕ) {r q e : Site}
    (h : incr (reciprocalField k) e r - incr (reciprocalField k) e q ≤ e.2) (hab : r - (1, -1) = q) :
    PE k r e := by
  unfold PE
  rw [hab]
  exact h

/-- A chain inequality at a point, given as a class inequality at the explicit target `q`. -/
theorem CE_of_cls (k : ℕ) (η : ℤ) {r q e : Site}
    (h : incr (reciprocalField k) e r - incr (reciprocalField k) e q ≤ e.2)
    (hab : r + η • (reciprocalFrame k).shortShift - (1, -1) = q) : CE k η r e := by
  unfold CE
  rw [hab]
  exact h

/-- The laplacian vanishes on an even native site away from `x = 1`. -/
theorem lap_zero_even (k : ℕ) {p : Site} (hN : NativeP (2 * (k : ℤ) + 3) p) (hE : EvenSite p) (hx : p.1 ≠ 1) :
    laplacian (reciprocalField k) p = 0 := by
  rw [laplacian_reciprocal_native k hN, if_pos hE, if_neg hx]

/-- The laplacian vanishes on an odd native site outside the band. -/
theorem lap_zero_odd (k : ℕ) {p : Site} (hN : NativeP (2 * (k : ℤ) + 3) p) (hO : ¬ EvenSite p)
    (hb : ¬ (0 < p.2 ∧ p.2 < (2 * (k : ℤ) + 3) + 1 ∧ 1 < p.1 + p.2 ∧ p.1 + p.2 < (2 * (k : ℤ) + 3) + 2)) :
    laplacian (reciprocalField k) p = 0 := by
  rw [laplacian_reciprocal_native k hN, if_neg hO, if_neg hb]

/-- The rule at an even site left of the axis, away from the special sites: the step is `(-1, 0)`. -/
theorem selDisp_even_left (d η x y : ℤ) (hE : EvenSite (x, y)) (hx : (x, y).1 ≤ 0)
    (h1 : ¬ ((x, y) = (2 - d, d) ∨ (x, y) = (2, d + 1)))
    (h2 : ¬ (((x, y).2 = 0 ∧ 2 ≤ (x, y).1) ∨ (x, y) = (0, 0) ∨ (x, y) = (d, 1) ∨
      ((x, y).2 = d + 1 ∧ 3 - d ≤ (x, y).1 ∧ (x, y).1 ≤ 0))) :
    selDisp d η (x, y) = (-1, 0) := by
  unfold selDisp
  rw [if_pos hE, if_neg h1, if_neg h2, if_pos hx]

/-- The rule at the origin: the step is `(1, 0)`. -/
theorem selDisp_origin (d η : ℤ) (hd : 3 ≤ d) : selDisp d η (0, 0) = (1, 0) := by
  have hE : EvenSite ((0 : ℤ), (0 : ℤ)) := by unfold EvenSite; norm_num
  have h1 : ¬ (((0 : ℤ), (0 : ℤ)) = (2 - d, d) ∨ ((0 : ℤ), (0 : ℤ)) = (2, d + 1)) := by
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  unfold selDisp
  rw [if_pos hE, if_neg h1, if_pos (Or.inr (Or.inl rfl))]

/-- The alias of type A: the row `(x, d + 1)` is the deck translate `(x + d - 1, 0) + T` of a bottom site. -/
theorem cov_aliasA (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (x : ℤ) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) (x, 2 * (k : ℤ) + 3 + 1)) (hx1 : 2 - (2 * (k : ℤ) + 3) ≤ x) (hx2 : x ≤ 1)
    (hc : ECover k η (x, 2 * (k : ℤ) + 3 + 1) e) :
    SE k η (x, 2 * (k : ℤ) + 3 + 1) e ∧ PE k (x, 2 * (k : ℤ) + 3 + 1) e ∧ CE k η (x, 2 * (k : ℤ) + 3 + 1) e := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hr : (x, 2 * (k : ℤ) + 3 + 1) = (x + (2 * (k : ℤ) + 3) - 1, (0 : ℤ)) +
      (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine 0 1 := by
    rw [combine_mk_one hd]
    ext <;> (simp; try ring)
  have hn0 : NativeP (2 * (k : ℤ) + 3) (x + (2 * (k : ℤ) + 3) - 1, (0 : ℤ)) := by
    unfold NativeP
    left
    dsimp only
    omega
  have hc0 := ecover_transfer k η hη (x + (2 * (k : ℤ) + 3) - 1, (0 : ℤ)) (x, 2 * (k : ℤ) + 3 + 1) e 0 1 hr hn0 hN hc
  exact cov_shift k η _ _ e 0 1 hr (cov_bottom k hk η hη (x + (2 * (k : ℤ) + 3) - 1) e hn0 (by omega) (by omega) hc0)

/-- The alias of type B: the cell `(x, 1 - x)` is the deck translate `(x + d, 2 - x) - U` of a top site. -/
theorem cov_aliasB (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (x : ℤ) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) (x, 1 - x)) (hx1 : 3 - (2 * (k : ℤ) + 3) ≤ x) (hx2 : x ≤ 0)
    (hc : ECover k η (x, 1 - x) e) :
    SE k η (x, 1 - x) e ∧ PE k (x, 1 - x) e ∧ CE k η (x, 1 - x) e := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hr : (x, 1 - x) = (x + (2 * (k : ℤ) + 3), 2 - x) +
      (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine (-1) 0 := by
    rw [combine_mk_one hd]
    ext <;> (simp; try ring)
  have hn0 : NativeP (2 * (k : ℤ) + 3) (x + (2 * (k : ℤ) + 3), 2 - x) := by
    unfold NativeP
    left
    dsimp only
    omega
  have hc0 := ecover_transfer k η hη (x + (2 * (k : ℤ) + 3), 2 - x) (x, 1 - x) e (-1) 0 hr hn0 hN hc
  exact cov_shift k η _ _ e (-1) 0 hr (cov_top k η hη (x + (2 * (k : ℤ) + 3)) (2 - x) e hn0
    (by ring) (by omega) (by omega) hc0)

theorem cov_P1 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hc : ECover k η ((3 - (2 * (k : ℤ) + 3)), (2 * (k : ℤ) + 3)) e) :
    SE k η ((3 - (2 * (k : ℤ) + 3)), (2 * (k : ℤ) + 3)) e ∧ PE k ((3 - (2 * (k : ℤ) + 3)), (2 * (k : ℤ) + 3)) e ∧ CE k η ((3 - (2 * (k : ℤ) + 3)), (2 * (k : ℤ) + 3)) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_vert k η hη (3 - (2 * (k : ℤ) + 3)) (2 * (k : ℤ) + 3) e (by omega) hc
  rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
  · exact ⟨SE_of_cls k (1) (cls_C1_p_py k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C1_p_py k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_C1_p_py k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (1) (cls_C1_p_my k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C1_p_my k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_C1_p_my k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_C1_m_py k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C1_m_py k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_C1_m_py k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_C1_m_my k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C1_m_my k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_C1_m_my k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩

theorem cov_P2 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hc : ECover k η ((4 - (2 * (k : ℤ) + 3)), (2 * (k : ℤ) + 3)) e) :
    SE k η ((4 - (2 * (k : ℤ) + 3)), (2 * (k : ℤ) + 3)) e ∧ PE k ((4 - (2 * (k : ℤ) + 3)), (2 * (k : ℤ) + 3)) e ∧ CE k η ((4 - (2 * (k : ℤ) + 3)), (2 * (k : ℤ) + 3)) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_horiz k η hη (4 - (2 * (k : ℤ) + 3)) (2 * (k : ℤ) + 3) e (by omega) hc
  rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
  · exact ⟨SE_of_cls k (1) (cls_C5_p_px k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C5_p_px k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_C5_p_px k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (1) (cls_C5_p_mx k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C5_p_mx k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_C5_p_mx k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_C5_m_px k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C5_m_px k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_C5_m_px k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_C5_m_mx k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C5_m_mx k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_C5_m_mx k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩

theorem cov_P3 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hc : ECover k η ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 2)) e) :
    SE k η ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 2)) e ∧ PE k ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 2)) e ∧ CE k η ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 2)) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_vert k η hη (5 - (2 * (k : ℤ) + 3)) ((2 * (k : ℤ) + 3) - 2) e (by omega) hc
  rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
  · exact ⟨SE_of_cls k (1) (cls_C7_p_py k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C7_p_py k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_C7_p_py k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (1) (cls_C7_p_my k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C7_p_my k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_C7_p_my k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_C7_m_py k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C7_m_py k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_C7_m_py k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_C7_m_my k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C7_m_my k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_C7_m_my k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩

theorem cov_P4 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hc : ECover k η ((5 - (2 * (k : ℤ) + 3)), (2 * (k : ℤ) + 3)) e) :
    SE k η ((5 - (2 * (k : ℤ) + 3)), (2 * (k : ℤ) + 3)) e ∧ PE k ((5 - (2 * (k : ℤ) + 3)), (2 * (k : ℤ) + 3)) e ∧ CE k η ((5 - (2 * (k : ℤ) + 3)), (2 * (k : ℤ) + 3)) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_vert k η hη (5 - (2 * (k : ℤ) + 3)) (2 * (k : ℤ) + 3) e (by omega) hc
  rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
  · exact ⟨SE_of_cls k (1) (cls_C9_p_py k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C9_p_py k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_C9_p_py k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (1) (cls_C9_p_my k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C9_p_my k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_C9_p_my k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_C9_m_py k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C9_m_py k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_C9_m_py k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_C9_m_my k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C9_m_my k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_C9_m_my k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩

theorem cov_P5 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hc : ECover k η (((2 * (k : ℤ) + 3) - 2), (1)) e) :
    SE k η (((2 * (k : ℤ) + 3) - 2), (1)) e ∧ PE k (((2 * (k : ℤ) + 3) - 2), (1)) e ∧ CE k η (((2 * (k : ℤ) + 3) - 2), (1)) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_horiz k η hη ((2 * (k : ℤ) + 3) - 2) (1) e (by omega) hc
  rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
  · exact ⟨SE_of_cls k (1) (cls_C13_p_px k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C13_p_px k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_C13_p_px k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (1) (cls_C13_p_mx k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C13_p_mx k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_C13_p_mx k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_C13_m_px k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C13_m_px k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_C13_m_px k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_C13_m_mx k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C13_m_mx k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_C13_m_mx k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩

theorem cov_P6 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hc : ECover k η (((2 * (k : ℤ) + 3) - 1), (1)) e) :
    SE k η (((2 * (k : ℤ) + 3) - 1), (1)) e ∧ PE k (((2 * (k : ℤ) + 3) - 1), (1)) e ∧ CE k η (((2 * (k : ℤ) + 3) - 1), (1)) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_vert k η hη ((2 * (k : ℤ) + 3) - 1) (1) e (by omega) hc
  rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
  · exact ⟨SE_of_cls k (1) (cls_C14_p_py k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C14_p_py k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_C14_p_py k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (1) (cls_C14_p_my k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C14_p_my k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_C14_p_my k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_C14_m_py k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C14_m_py k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_C14_m_py k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_C14_m_my k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C14_m_my k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_C14_m_my k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩

theorem cov_P7 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hc : ECover k η ((1), ((2 * (k : ℤ) + 3) - 1)) e) :
    SE k η ((1), ((2 * (k : ℤ) + 3) - 1)) e ∧ PE k ((1), ((2 * (k : ℤ) + 3) - 1)) e ∧ CE k η ((1), ((2 * (k : ℤ) + 3) - 1)) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_vert k η hη (1) ((2 * (k : ℤ) + 3) - 1) e (by omega) hc
  rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
  · exact ⟨SE_of_cls k (1) (cls_C15_p_py k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C15_p_py k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_C15_p_py k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (1) (cls_C15_p_my k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C15_p_my k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_C15_p_my k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_K3_m_py k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_K3_m_py k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_K3_m_py k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_C15_m_my k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C15_m_my k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_C15_m_my k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩

theorem cov_P8 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hc : ECover k η ((0), (2 * (k : ℤ) + 3)) e) :
    SE k η ((0), (2 * (k : ℤ) + 3)) e ∧ PE k ((0), (2 * (k : ℤ) + 3)) e ∧ CE k η ((0), (2 * (k : ℤ) + 3)) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_vert k η hη (0) (2 * (k : ℤ) + 3) e (by omega) hc
  rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
  · exact ⟨SE_of_cls k (1) (cls_C18_p_py k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C18_p_py k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_C18_p_py k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (1) (cls_C18_p_my k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C18_p_my k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_C18_p_my k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_K4_m_py k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_K4_m_py k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_K4_m_py k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_C18_m_my k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_C18_m_my k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_C18_m_my k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩

theorem cov_P12 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hc : ECover k η ((4 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 1)) e) :
    SE k η ((4 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 1)) e ∧ PE k ((4 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 1)) e ∧ CE k η ((4 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 1)) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_vert k η hη (4 - (2 * (k : ℤ) + 3)) ((2 * (k : ℤ) + 3) - 1) e (by omega) hc
  rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
  · exact ⟨SE_of_cls k (1) (cls_R4_p_py k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R4_p_py k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_R4_p_py k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (1) (cls_R4_p_my k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R4_p_my k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_R4_p_my k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_R4_m_py k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R4_m_py k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_R4_m_py k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_R4_m_my k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R4_m_my k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_R4_m_my k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩

theorem cov_P13 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hc : ECover k η ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 1)) e) :
    SE k η ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 1)) e ∧ PE k ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 1)) e ∧ CE k η ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 1)) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_horiz k η hη (5 - (2 * (k : ℤ) + 3)) ((2 * (k : ℤ) + 3) - 1) e (by omega) hc
  rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
  · exact ⟨SE_of_cls k (1) (cls_R5_p_px k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R5_p_px k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_R5_p_px k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (1) (cls_R5_p_mx k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R5_p_mx k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_R5_p_mx k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_R5_m_px k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R5_m_px k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_R5_m_px k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_R5_m_mx k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R5_m_mx k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_R5_m_mx k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩

theorem cov_P14 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hc : ECover k η ((2), ((2 * (k : ℤ) + 3) - 2)) e) :
    SE k η ((2), ((2 * (k : ℤ) + 3) - 2)) e ∧ PE k ((2), ((2 * (k : ℤ) + 3) - 2)) e ∧ CE k η ((2), ((2 * (k : ℤ) + 3) - 2)) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_vert k η hη (2) ((2 * (k : ℤ) + 3) - 2) e (by omega) hc
  rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
  · exact ⟨SE_of_cls k (1) (cls_R6_p_py k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R6_p_py k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_R6_p_py k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (1) (cls_R6_p_my k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R6_p_my k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_R6_p_my k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_R6_m_py k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R6_m_py k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_R6_m_py k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_R6_m_my k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R6_m_my k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_R6_m_my k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩

theorem cov_P16 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hc : ECover k η ((1), (2 * (k : ℤ) + 3)) e) :
    SE k η ((1), (2 * (k : ℤ) + 3)) e ∧ PE k ((1), (2 * (k : ℤ) + 3)) e ∧ CE k η ((1), (2 * (k : ℤ) + 3)) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_horiz k η hη (1) (2 * (k : ℤ) + 3) e (by omega) hc
  rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
  · exact ⟨SE_of_cls k (1) (cls_R8_p_px k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R8_p_px k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_R8_p_px k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (1) (cls_R8_p_mx k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R8_p_mx k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_R8_p_mx k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_R8_m_px k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R8_m_px k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_R8_m_px k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_R8_m_mx k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R8_m_mx k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_R8_m_mx k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩

theorem cov_P18 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hc : ECover k η ((2), ((2 * (k : ℤ) + 3) + 1)) e) :
    SE k η ((2), ((2 * (k : ℤ) + 3) + 1)) e ∧ PE k ((2), ((2 * (k : ℤ) + 3) + 1)) e ∧ CE k η ((2), ((2 * (k : ℤ) + 3) + 1)) e := by
  obtain ⟨s, hs, rfl⟩ := ecover_horiz k η hη (2) ((2 * (k : ℤ) + 3) + 1) e (by omega) hc
  rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
  · exact ⟨SE_of_cls k (1) (cls_K1_p_px k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_K1_p_px k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_K1_p_px k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (1) (cls_K1_p_mx k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_K1_p_mx k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_K1_p_mx k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_K1_m_px k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_K1_m_px k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_K1_m_px k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_K1_m_mx k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_K1_m_mx k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_K1_m_mx k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩

theorem cov_P9 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((3 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 1))) (hc : ECover k η ((3 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 1)) e) :
    SE k η ((3 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 1)) e ∧ PE k ((3 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 1)) e ∧ CE k η ((3 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 1)) e := by
  have hE : EvenSite ((3 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 1)) := by unfold EvenSite; dsimp only; omega
  have hx : (((3 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 1))).1 ≤ 0 := by dsimp only; omega
  have hsel : e = (-1, 0) := by
    rcases hc with ⟨hl, he⟩ | ⟨hl, -⟩
    · rw [he]
      exact selDisp_even_left (2 * (k : ℤ) + 3) η (3 - (2 * (k : ℤ) + 3)) ((2 * (k : ℤ) + 3) - 1) hE hx
        (by intro h; simp only [Prod.mk.injEq] at h; omega)
        (by intro h; simp only [Prod.mk.injEq] at h; omega)
    · exfalso
      rw [lap_zero_even k hN hE (by dsimp only; omega)] at hl
      norm_num at hl
  subst hsel
  rcases hη with rfl | rfl
  · exact ⟨SE_of_cls k (1) (cls_R1_p_mx k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R1_p_mx k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_R1_p_mx k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_R1_m_mx k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R1_m_mx k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_R1_m_mx k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩

theorem cov_P10 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((4 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 2))) (hc : ECover k η ((4 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 2)) e) :
    SE k η ((4 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 2)) e ∧ PE k ((4 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 2)) e ∧ CE k η ((4 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 2)) e := by
  have hE : EvenSite ((4 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 2)) := by unfold EvenSite; dsimp only; omega
  have hx : (((4 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 2))).1 ≤ 0 := by dsimp only; omega
  have hsel : e = (-1, 0) := by
    rcases hc with ⟨hl, he⟩ | ⟨hl, -⟩
    · rw [he]
      exact selDisp_even_left (2 * (k : ℤ) + 3) η (4 - (2 * (k : ℤ) + 3)) ((2 * (k : ℤ) + 3) - 2) hE hx
        (by intro h; simp only [Prod.mk.injEq] at h; omega)
        (by intro h; simp only [Prod.mk.injEq] at h; omega)
    · exfalso
      rw [lap_zero_even k hN hE (by dsimp only; omega)] at hl
      norm_num at hl
  subst hsel
  rcases hη with rfl | rfl
  · exact ⟨SE_of_cls k (1) (cls_R2_p_mx k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R2_p_mx k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_R2_p_mx k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_R2_m_mx k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R2_m_mx k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_R2_m_mx k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩

theorem cov_P11 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 3))) (hc : ECover k η ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 3)) e) :
    SE k η ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 3)) e ∧ PE k ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 3)) e ∧ CE k η ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 3)) e := by
  have hE : EvenSite ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 3)) := by unfold EvenSite; dsimp only; omega
  have hx : (((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 3))).1 ≤ 0 := by dsimp only; omega
  have hsel : e = (-1, 0) := by
    rcases hc with ⟨hl, he⟩ | ⟨hl, -⟩
    · rw [he]
      exact selDisp_even_left (2 * (k : ℤ) + 3) η (5 - (2 * (k : ℤ) + 3)) ((2 * (k : ℤ) + 3) - 3) hE hx
        (by intro h; simp only [Prod.mk.injEq] at h; omega)
        (by intro h; simp only [Prod.mk.injEq] at h; omega)
    · exfalso
      rw [lap_zero_even k hN hE (by dsimp only; omega)] at hl
      norm_num at hl
  subst hsel
  rcases hη with rfl | rfl
  · exact ⟨SE_of_cls k (1) (cls_R3_p_mx k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R3_p_mx k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_R3_p_mx k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_R3_m_mx k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R3_m_mx k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_R3_m_mx k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩

theorem cov_P15 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-1), (2 * (k : ℤ) + 3))) (hc : ECover k η ((-1), (2 * (k : ℤ) + 3)) e) :
    SE k η ((-1), (2 * (k : ℤ) + 3)) e ∧ PE k ((-1), (2 * (k : ℤ) + 3)) e ∧ CE k η ((-1), (2 * (k : ℤ) + 3)) e := by
  have hE : EvenSite ((-1), (2 * (k : ℤ) + 3)) := by unfold EvenSite; dsimp only; omega
  have hx : (((-1), (2 * (k : ℤ) + 3))).1 ≤ 0 := by dsimp only; omega
  have hsel : e = (-1, 0) := by
    rcases hc with ⟨hl, he⟩ | ⟨hl, -⟩
    · rw [he]
      exact selDisp_even_left (2 * (k : ℤ) + 3) η (-1) (2 * (k : ℤ) + 3) hE hx
        (by intro h; simp only [Prod.mk.injEq] at h; omega)
        (by intro h; simp only [Prod.mk.injEq] at h; omega)
    · exfalso
      rw [lap_zero_even k hN hE (by dsimp only; omega)] at hl
      norm_num at hl
  subst hsel
  rcases hη with rfl | rfl
  · exact ⟨SE_of_cls k (1) (cls_R7_p_mx k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R7_p_mx k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_R7_p_mx k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_R7_m_mx k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R7_m_mx k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_R7_m_mx k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩

/-- The rule at the top cell `(2, d)`: the step is `(0, -eta)`. -/
theorem selDisp_top_two (d η : ℤ) (hd : d % 2 = 1) (hd3 : 3 ≤ d) : selDisp d η (2, d) = (0, -η) := by
  have hO : ¬ EvenSite ((2 : ℤ), d) := by unfold EvenSite; dsimp only; omega
  unfold selDisp
  rw [if_neg hO]
  split_ifs with h
  · rfl
  · exfalso
    simp only at h
    omega

/-- The origin: the policy keeps `(1, 0)` (both signs). -/
theorem cov_P17 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (0 : ℤ))) (hc : ECover k η ((0 : ℤ), (0 : ℤ)) e) :
    SE k η ((0 : ℤ), (0 : ℤ)) e ∧ PE k ((0 : ℤ), (0 : ℤ)) e ∧ CE k η ((0 : ℤ), (0 : ℤ)) e := by
  have hE : EvenSite ((0 : ℤ), (0 : ℤ)) := by unfold EvenSite; norm_num
  have hsel : e = (1, 0) := by
    rcases hc with ⟨hl, he⟩ | ⟨hl, -⟩
    · rw [he]
      exact selDisp_origin (2 * (k : ℤ) + 3) η (by omega)
    · exfalso
      rw [lap_zero_even k hN hE (by norm_num)] at hl
      norm_num at hl
  subst hsel
  rcases hη with rfl | rfl
  · exact ⟨SE_of_cls k (1) (cls_R9_p_px k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R9_p_px k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_R9_p_px k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_R9_m_px k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_R9_m_px k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_R9_m_px k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩

/-- The top cell `(2, d)`: the forced vertical step `(0, -eta)`. -/
theorem cov_P19 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), 2 * (k : ℤ) + 3)) (hc : ECover k η ((2 : ℤ), 2 * (k : ℤ) + 3) e) :
    SE k η ((2 : ℤ), 2 * (k : ℤ) + 3) e ∧ PE k ((2 : ℤ), 2 * (k : ℤ) + 3) e ∧
      CE k η ((2 : ℤ), 2 * (k : ℤ) + 3) e := by
  have hO : ¬ EvenSite ((2 : ℤ), 2 * (k : ℤ) + 3) := by unfold EvenSite; dsimp only; omega
  have hsel : e = (0, -η) := by
    rcases hc with ⟨hl, he⟩ | ⟨hl, -⟩
    · rw [he]
      exact selDisp_top_two (2 * (k : ℤ) + 3) η (by omega) (by omega)
    · exfalso
      rw [lap_zero_odd k hN hO (by dsimp only; omega)] at hl
      norm_num at hl
  subst hsel
  rcases hη with rfl | rfl
  · exact ⟨SE_of_cls k (1) (cls_K2_p_my k hk).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_K2_p_my k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (1) (cls_K2_p_my k hk).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
  · exact ⟨SE_of_cls k (-1) (cls_K2_m_py k hk).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
      PE_of_cls k (cls_K2_m_py k hk).2.1 (by ext <;> (simp; try ring)),
      CE_of_cls k (-1) (cls_K2_m_py k hk).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩

/-- The alias of type C: `(d, 1) = (0, 0) + U`. -/
theorem cov_aliasC (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 3, (1 : ℤ))) (hc : ECover k η (2 * (k : ℤ) + 3, (1 : ℤ)) e) :
    SE k η (2 * (k : ℤ) + 3, (1 : ℤ)) e ∧ PE k (2 * (k : ℤ) + 3, (1 : ℤ)) e ∧
      CE k η (2 * (k : ℤ) + 3, (1 : ℤ)) e := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hr : (2 * (k : ℤ) + 3, (1 : ℤ)) = ((0 : ℤ), (0 : ℤ)) +
      (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine 1 0 := by
    rw [combine_mk_one hd]
    ext <;> (simp; try ring)
  have hn0 : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (0 : ℤ)) := Or.inr (Or.inl rfl)
  have hc0 := ecover_transfer k η hη ((0 : ℤ), (0 : ℤ)) _ e 1 0 hr hn0 hN hc
  exact cov_shift k η _ _ e 1 0 hr (cov_P17 k hk η hη e hn0 hc0)

/-- The alias of type B2: `(2 - d, d) = (2, d + 1) - U`. -/
theorem cov_aliasB2 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3))
    (hc : ECover k η (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3) e) :
    SE k η (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3) e ∧ PE k (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3) e ∧
      CE k η (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3) e := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hr : (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3) = ((2 : ℤ), 2 * (k : ℤ) + 3 + 1) +
      (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine (-1) 0 := by
    rw [combine_mk_one hd]
    ext <;> (simp; try ring)
  have hn0 : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), 2 * (k : ℤ) + 3 + 1) := Or.inr (Or.inr rfl)
  have hc0 := ecover_transfer k η hη ((2 : ℤ), 2 * (k : ℤ) + 3 + 1) _ e (-1) 0 hr hn0 hN hc
  exact cov_shift k η _ _ e (-1) 0 hr (cov_P18 k hk η hη e hc0)

/-- The top row `(x, d)` for `6 - d <= x <= -2`. -/
theorem cov_toprow (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (x : ℤ) (e : Site)
    (hx1 : 6 - (2 * (k : ℤ) + 3) ≤ x) (hx2 : x ≤ -2) (hc : ECover k η (x, 2 * (k : ℤ) + 3) e) :
    SE k η (x, 2 * (k : ℤ) + 3) e ∧ PE k (x, 2 * (k : ℤ) + 3) e ∧ CE k η (x, 2 * (k : ℤ) + 3) e := by
  by_cases hpar : (x + (2 * (k : ℤ) + 3)) % 2 = 0
  · obtain ⟨s, hs, rfl⟩ := ecover_horiz k η hη x (2 * (k : ℤ) + 3) e hpar hc
    rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
    · exact ⟨SE_of_cls k (1) (top_p_px_p k hk x hx1 hx2).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
        PE_of_cls k (top_p_px_p k hk x hx1 hx2).2.1 (by ext <;> (simp; try ring)),
        CE_of_cls k (1) (top_p_px_p k hk x hx1 hx2).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
    · exact ⟨SE_of_cls k (1) (top_p_mx_p k hk x hx1 hx2).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
        PE_of_cls k (top_p_mx_p k hk x hx1 hx2).2.1 (by ext <;> (simp; try ring)),
        CE_of_cls k (1) (top_p_mx_p k hk x hx1 hx2).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
    · exact ⟨SE_of_cls k (-1) (top_m_px_m k hk x hx1 hx2).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
        PE_of_cls k (top_m_px_m k hk x hx1 hx2).2.1 (by ext <;> (simp; try ring)),
        CE_of_cls k (-1) (top_m_px_m k hk x hx1 hx2).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩
    · exact ⟨SE_of_cls k (-1) (top_m_mx_m k hk x hx1 hx2).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
        PE_of_cls k (top_m_mx_m k hk x hx1 hx2).2.1 (by ext <;> (simp; try ring)),
        CE_of_cls k (-1) (top_m_mx_m k hk x hx1 hx2).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩
  · obtain ⟨s, hs, rfl⟩ := ecover_vert k η hη x (2 * (k : ℤ) + 3) e (by omega) hc
    rcases hη with rfl | rfl <;> rcases hs with rfl | rfl
    · exact ⟨SE_of_cls k (1) (top_p_py_p k hk x hx1 hx2).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
        PE_of_cls k (top_p_py_p k hk x hx1 hx2).2.1 (by ext <;> (simp; try ring)),
        CE_of_cls k (1) (top_p_py_p k hk x hx1 hx2).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
    · exact ⟨SE_of_cls k (1) (top_p_my_p k hk x hx1 hx2).1 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring)),
        PE_of_cls k (top_p_my_p k hk x hx1 hx2).2.1 (by ext <;> (simp; try ring)),
        CE_of_cls k (1) (top_p_my_p k hk x hx1 hx2).2.2 (by rw [smul_shortShift_recip k (1)]; ext <;> (simp; try ring))⟩
    · exact ⟨SE_of_cls k (-1) (top_m_py_m k hk x hx1 hx2).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
        PE_of_cls k (top_m_py_m k hk x hx1 hx2).2.1 (by ext <;> (simp; try ring)),
        CE_of_cls k (-1) (top_m_py_m k hk x hx1 hx2).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩
    · exact ⟨SE_of_cls k (-1) (top_m_my_m k hk x hx1 hx2).1 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring)),
        PE_of_cls k (top_m_my_m k hk x hx1 hx2).2.1 (by ext <;> (simp; try ring)),
        CE_of_cls k (-1) (top_m_my_m k hk x hx1 hx2).2.2 (by rw [smul_shortShift_recip k (-1)]; ext <;> (simp; try ring))⟩

/-- The alias of type B0: the cell `(2 - d, d - 1)` is the deck translate `(2, d) - U` of the top cell `(2, d)`. -/
theorem cov_aliasB0 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 - 1))
    (hc : ECover k η (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 - 1) e) :
    SE k η (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 - 1) e ∧
      PE k (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 - 1) e ∧
      CE k η (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 - 1) e := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hr : (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3 - 1) = ((2 : ℤ), 2 * (k : ℤ) + 3) +
      (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine (-1) 0 := by
    rw [combine_mk_one hd]
    ext <;> (simp; try ring)
  have hn0 : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), 2 * (k : ℤ) + 3) := by
    unfold NativeP
    left
    dsimp only
    omega
  have hc0 := ecover_transfer k η hη ((2 : ℤ), 2 * (k : ℤ) + 3) _ e (-1) 0 hr hn0 hN hc
  exact cov_shift k η _ _ e (-1) 0 hr (cov_P19 k hk η hη e hn0 hc0)

theorem cover_ge2 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (r : Site)
    (hr : NativeP (2 * (k : ℤ) + 3) r) (e : Site) (hc : ECover k η r e) :
    SE k η r e ∧ PE k r e ∧ CE k η r e := by
  obtain ⟨x, y⟩ := r
  have hN' := hr
  unfold NativeP at hN'
  simp only [Prod.mk.injEq] at hN'
  rcases Int.emod_two_eq_zero_or_one (x + y) with h | h
  · rcases le_or_gt x (2 - (2 * (k : ℤ) + 3)) with h | h
    · obtain rfl : x = 2 - (2 * (k : ℤ) + 3) := by omega
      obtain rfl : y = 2 * (k : ℤ) + 3 := by omega
      exact cov_aliasB2 k hk η hη e hr hc
    · rcases le_or_gt x (3 - (2 * (k : ℤ) + 3)) with h | h
      · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 1) with h | h
        · obtain rfl : x = (3 - (2 * (k : ℤ) + 3)) := by omega
          obtain rfl : y = ((2 * (k : ℤ) + 3) - 1) := by omega
          exact cov_P9 k hk η hη e hr hc
        · obtain rfl : y = 2 * (k : ℤ) + 3 + 1 := by omega
          exact cov_aliasA k hk η hη x e hr (by omega) (by omega) hc
      · rcases le_or_gt x (4 - (2 * (k : ℤ) + 3)) with h | h
        · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 2) with h | h
          · obtain rfl : x = (4 - (2 * (k : ℤ) + 3)) := by omega
            obtain rfl : y = ((2 * (k : ℤ) + 3) - 2) := by omega
            exact cov_P10 k hk η hη e hr hc
          · obtain rfl : x = (4 - (2 * (k : ℤ) + 3)) := by omega
            obtain rfl : y = (2 * (k : ℤ) + 3) := by omega
            exact cov_P2 k hk η hη e hc
        · rcases le_or_gt x (5 - (2 * (k : ℤ) + 3)) with h | h
          · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 3) with h | h
            · obtain rfl : x = (5 - (2 * (k : ℤ) + 3)) := by omega
              obtain rfl : y = ((2 * (k : ℤ) + 3) - 3) := by omega
              exact cov_P11 k hk η hη e hr hc
            · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 1) with h | h
              · obtain rfl : x = (5 - (2 * (k : ℤ) + 3)) := by omega
                obtain rfl : y = ((2 * (k : ℤ) + 3) - 1) := by omega
                exact cov_P13 k hk η hη e hc
              · obtain rfl : y = 2 * (k : ℤ) + 3 + 1 := by omega
                exact cov_aliasA k hk η hη x e hr (by omega) (by omega) hc
          · rcases le_or_gt x (6 - (2 * (k : ℤ) + 3)) with h | h
            · rcases le_or_gt x (-2) with h | h
              · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 3) with h | h
                · exact cov_low2 k η hη x y e hr (by omega) (by omega) (by omega) hc
                · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 2) with h | h
                  · exact cov_interior_even k η hη x y e hr (by omega) (by omega) hc
                  · obtain rfl : y = 2 * (k : ℤ) + 3 := by omega
                    exact cov_toprow k hk η hη x e (by omega) (by omega) hc
              · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 3) with h | h
                · exact cov_low2 k η hη x y e hr (by omega) (by omega) (by omega) hc
                · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 2) with h | h
                  · exact cov_interior_even k η hη x y e hr (by omega) (by omega) hc
                  · obtain rfl : x = (-1) := by omega
                    obtain rfl : y = (2 * (k : ℤ) + 3) := by omega
                    exact cov_P15 k hk η hη e hr hc
            · rcases le_or_gt x ((2 * (k : ℤ) + 3) - 3) with h | h
              · rcases le_or_gt x (-2) with h | h
                · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 3) with h | h
                  · rcases le_or_gt y (4) with h | h
                    · exact cov_low2 k η hη x y e hr (by omega) (by omega) (by omega) hc
                    · rcases le_or_gt (x + y) (2) with h | h
                      · exact cov_low2 k η hη x y e hr (by omega) (by omega) (by omega) hc
                      · exact cov_interior_even k η hη x y e hr (by omega) (by omega) hc
                  · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 2) with h | h
                    · exact cov_interior_even k η hη x y e hr (by omega) (by omega) hc
                    · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 1) with h | h
                      · exact cov_interior_even k η hη x y e hr (by omega) (by omega) hc
                      · rcases le_or_gt y (2 * (k : ℤ) + 3) with h | h
                        · obtain rfl : y = 2 * (k : ℤ) + 3 := by omega
                          exact cov_toprow k hk η hη x e (by omega) (by omega) hc
                        · obtain rfl : y = 2 * (k : ℤ) + 3 + 1 := by omega
                          exact cov_aliasA k hk η hη x e hr (by omega) (by omega) hc
                · rcases le_or_gt x (-1) with h | h
                  · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 3) with h | h
                    · rcases le_or_gt y (3) with h | h
                      · exact cov_low2 k η hη x y e hr (by omega) (by omega) (by omega) hc
                      · exact cov_interior_even k η hη x y e hr (by omega) (by omega) hc
                    · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 2) with h | h
                      · exact cov_interior_even k η hη x y e hr (by omega) (by omega) hc
                      · obtain rfl : x = (-1) := by omega
                        obtain rfl : y = (2 * (k : ℤ) + 3) := by omega
                        exact cov_P15 k hk η hη e hr hc
                  · rcases le_or_gt x (0) with h | h
                    · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 3) with h | h
                      · rcases le_or_gt y (0) with h | h
                        · obtain rfl : x = 0 := by omega
                          obtain rfl : y = 0 := by omega
                          exact cov_P17 k hk η hη e hr hc
                        · rcases le_or_gt y (2) with h | h
                          · exact cov_low2 k η hη x y e hr (by omega) (by omega) (by omega) hc
                          · exact cov_interior_even k η hη x y e hr (by omega) (by omega) hc
                      · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 1) with h | h
                        · exact cov_interior_even k η hη x y e hr (by omega) (by omega) hc
                        · obtain rfl : y = 2 * (k : ℤ) + 3 + 1 := by omega
                          exact cov_aliasA k hk η hη x e hr (by omega) (by omega) hc
                    · rcases le_or_gt x (1) with h | h
                      · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 3) with h | h
                        · rcases le_or_gt y (1) with h | h
                          · exact cov_low2 k η hη x y e hr (by omega) (by omega) (by omega) hc
                          · exact cov_interior_even k η hη x y e hr (by omega) (by omega) hc
                        · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 2) with h | h
                          · exact cov_interior_even k η hη x y e hr (by omega) (by omega) hc
                          · obtain rfl : x = (1) := by omega
                            obtain rfl : y = (2 * (k : ℤ) + 3) := by omega
                            exact cov_P16 k hk η hη e hc
                      · rcases le_or_gt x (2) with h | h
                        · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 3) with h | h
                          · rcases le_or_gt y (0) with h | h
                            · obtain rfl : y = 0 := by omega
                              exact cov_bottom k hk η hη x e hr (by omega) (by omega) hc
                            · exact cov_interior_even k η hη x y e hr (by omega) (by omega) hc
                          · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 1) with h | h
                            · exact cov_sumd1 k η hη x y e hr (by omega) (by omega) (by omega) hc
                            · obtain rfl : x = (2) := by omega
                              obtain rfl : y = ((2 * (k : ℤ) + 3) + 1) := by omega
                              exact cov_P18 k hk η hη e hc
                        · rcases le_or_gt x (3) with h | h
                          · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 3) with h | h
                            · exact cov_interior_even k η hη x y e hr (by omega) (by omega) hc
                            · exact cov_sumd1 k η hη x y e hr (by omega) (by omega) (by omega) hc
                          · rcases le_or_gt y (0) with h | h
                            · obtain rfl : y = 0 := by omega
                              exact cov_bottom k hk η hη x e hr (by omega) (by omega) hc
                            · rcases le_or_gt y (1) with h | h
                              · exact cov_interior_even k η hη x y e hr (by omega) (by omega) hc
                              · rcases le_or_gt y (2) with h | h
                                · exact cov_interior_even k η hη x y e hr (by omega) (by omega) hc
                                · rcases le_or_gt y (3) with h | h
                                  · exact cov_interior_even k η hη x y e hr (by omega) (by omega) hc
                                  · rcases le_or_gt y (4) with h | h
                                    · rcases le_or_gt (x + y) ((2 * (k : ℤ) + 3) - 1) with h | h
                                      · exact cov_interior_even k η hη x y e hr (by omega) (by omega) hc
                                      · exact cov_sumd1 k η hη x y e hr (by omega) (by omega) (by omega) hc
                                    · rcases le_or_gt (x + y) ((2 * (k : ℤ) + 3) - 1) with h | h
                                      · exact cov_interior_even k η hη x y e hr (by omega) (by omega) hc
                                      · exact cov_sumd1 k η hη x y e hr (by omega) (by omega) (by omega) hc
              · rcases le_or_gt x ((2 * (k : ℤ) + 3) - 2) with h | h
                · rcases le_or_gt y (1) with h | h
                  · obtain rfl : x = ((2 * (k : ℤ) + 3) - 2) := by omega
                    obtain rfl : y = (1) := by omega
                    exact cov_P5 k hk η hη e hc
                  · exact cov_sumd1 k η hη x y e hr (by omega) (by omega) (by omega) hc
                · rcases le_or_gt x ((2 * (k : ℤ) + 3) - 1) with h | h
                  · rcases le_or_gt y (0) with h | h
                    · obtain rfl : y = 0 := by omega
                      exact cov_bottom k hk η hη x e hr (by omega) (by omega) hc
                    · exact cov_sumd1 k η hη x y e hr (by omega) (by omega) (by omega) hc
                  · obtain rfl : x = 2 * (k : ℤ) + 3 := by omega
                    obtain rfl : y = 1 := by omega
                    exact cov_aliasC k hk η hη e hr hc
  · rcases le_or_gt x (2 - (2 * (k : ℤ) + 3)) with h | h
    · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 1) with h | h
      · obtain rfl : x = 2 - (2 * (k : ℤ) + 3) := by omega
        obtain rfl : y = 2 * (k : ℤ) + 3 - 1 := by omega
        exact cov_aliasB0 k hk η hη e hr hc
      · obtain rfl : y = 2 * (k : ℤ) + 3 + 1 := by omega
        exact cov_aliasA k hk η hη x e hr (by omega) (by omega) hc
    · rcases le_or_gt x (3 - (2 * (k : ℤ) + 3)) with h | h
      · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 2) with h | h
        · obtain rfl : y = 1 - x := by omega
          exact cov_aliasB k hk η hη x e hr (by omega) (by omega) hc
        · obtain rfl : x = (3 - (2 * (k : ℤ) + 3)) := by omega
          obtain rfl : y = (2 * (k : ℤ) + 3) := by omega
          exact cov_P1 k hk η hη e hc
      · rcases le_or_gt x (4 - (2 * (k : ℤ) + 3)) with h | h
        · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 3) with h | h
          · obtain rfl : y = 1 - x := by omega
            exact cov_aliasB k hk η hη x e hr (by omega) (by omega) hc
          · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 1) with h | h
            · obtain rfl : x = (4 - (2 * (k : ℤ) + 3)) := by omega
              obtain rfl : y = ((2 * (k : ℤ) + 3) - 1) := by omega
              exact cov_P12 k hk η hη e hc
            · obtain rfl : y = 2 * (k : ℤ) + 3 + 1 := by omega
              exact cov_aliasA k hk η hη x e hr (by omega) (by omega) hc
        · rcases le_or_gt x (5 - (2 * (k : ℤ) + 3)) with h | h
          · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 3) with h | h
            · obtain rfl : y = 1 - x := by omega
              exact cov_aliasB k hk η hη x e hr (by omega) (by omega) hc
            · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 2) with h | h
              · obtain rfl : x = (5 - (2 * (k : ℤ) + 3)) := by omega
                obtain rfl : y = ((2 * (k : ℤ) + 3) - 2) := by omega
                exact cov_P3 k hk η hη e hc
              · obtain rfl : x = (5 - (2 * (k : ℤ) + 3)) := by omega
                obtain rfl : y = (2 * (k : ℤ) + 3) := by omega
                exact cov_P4 k hk η hη e hc
          · rcases le_or_gt x (6 - (2 * (k : ℤ) + 3)) with h | h
            · rcases le_or_gt x (-2) with h | h
              · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 3) with h | h
                · rcases le_or_gt y (4) with h | h
                  · exact cov_low1 k η hη x y e hr (by omega) (by omega) (by omega) hc
                  · rcases le_or_gt (x + y) (1) with h | h
                    · exact cov_low1 k η hη x y e hr (by omega) (by omega) (by omega) hc
                    · exact cov_low3 k η hη x y e (by omega) (by omega) (by omega) hc
                · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 1) with h | h
                  · exact cov_interior_odd k η hη x y e (by omega) (by omega) hc
                  · obtain rfl : y = 2 * (k : ℤ) + 3 + 1 := by omega
                    exact cov_aliasA k hk η hη x e hr (by omega) (by omega) hc
              · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 3) with h | h
                · rcases le_or_gt y (2) with h | h
                  · exact cov_low1 k η hη x y e hr (by omega) (by omega) (by omega) hc
                  · exact cov_low3 k η hη x y e (by omega) (by omega) (by omega) hc
                · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 1) with h | h
                  · exact cov_interior_odd k η hη x y e (by omega) (by omega) hc
                  · obtain rfl : y = 2 * (k : ℤ) + 3 + 1 := by omega
                    exact cov_aliasA k hk η hη x e hr (by omega) (by omega) hc
            · rcases le_or_gt x ((2 * (k : ℤ) + 3) - 3) with h | h
              · rcases le_or_gt x (-2) with h | h
                · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 3) with h | h
                  · rcases le_or_gt y (3) with h | h
                    · exact cov_low1 k η hη x y e hr (by omega) (by omega) (by omega) hc
                    · rcases le_or_gt y (4) with h | h
                      · exact cov_low1 k η hη x y e hr (by omega) (by omega) (by omega) hc
                      · rcases le_or_gt (x + y) (1) with h | h
                        · exact cov_low1 k η hη x y e hr (by omega) (by omega) (by omega) hc
                        · rcases le_or_gt (x + y) (3) with h | h
                          · exact cov_low3 k η hη x y e (by omega) (by omega) (by omega) hc
                          · exact cov_interior_odd k η hη x y e (by omega) (by omega) hc
                  · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 2) with h | h
                    · exact cov_interior_odd k η hη x y e (by omega) (by omega) hc
                    · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 1) with h | h
                      · exact cov_interior_odd k η hη x y e (by omega) (by omega) hc
                      · rcases le_or_gt y (2 * (k : ℤ) + 3) with h | h
                        · obtain rfl : y = 2 * (k : ℤ) + 3 := by omega
                          exact cov_toprow k hk η hη x e (by omega) (by omega) hc
                        · obtain rfl : y = 2 * (k : ℤ) + 3 + 1 := by omega
                          exact cov_aliasA k hk η hη x e hr (by omega) (by omega) hc
                · rcases le_or_gt x (-1) with h | h
                  · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 3) with h | h
                    · rcases le_or_gt y (2) with h | h
                      · exact cov_low1 k η hη x y e hr (by omega) (by omega) (by omega) hc
                      · rcases le_or_gt y (4) with h | h
                        · exact cov_low3 k η hη x y e (by omega) (by omega) (by omega) hc
                        · exact cov_interior_odd k η hη x y e (by omega) (by omega) hc
                    · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 1) with h | h
                      · exact cov_interior_odd k η hη x y e (by omega) (by omega) hc
                      · obtain rfl : y = 2 * (k : ℤ) + 3 + 1 := by omega
                        exact cov_aliasA k hk η hη x e hr (by omega) (by omega) hc
                  · rcases le_or_gt x (0) with h | h
                    · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 3) with h | h
                      · rcases le_or_gt y (1) with h | h
                        · exact cov_low1 k η hη x y e hr (by omega) (by omega) (by omega) hc
                        · rcases le_or_gt y (3) with h | h
                          · exact cov_low3 k η hη x y e (by omega) (by omega) (by omega) hc
                          · exact cov_interior_odd k η hη x y e (by omega) (by omega) hc
                      · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 2) with h | h
                        · exact cov_interior_odd k η hη x y e (by omega) (by omega) hc
                        · obtain rfl : x = (0) := by omega
                          obtain rfl : y = (2 * (k : ℤ) + 3) := by omega
                          exact cov_P8 k hk η hη e hc
                    · rcases le_or_gt x (1) with h | h
                      · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 3) with h | h
                        · rcases le_or_gt y (0) with h | h
                          · obtain rfl : y = 0 := by omega
                            exact cov_bottom k hk η hη x e hr (by omega) (by omega) hc
                          · rcases le_or_gt y (2) with h | h
                            · exact cov_low3 k η hη x y e (by omega) (by omega) (by omega) hc
                            · exact cov_interior_odd k η hη x y e (by omega) (by omega) hc
                        · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 1) with h | h
                          · obtain rfl : x = (1) := by omega
                            obtain rfl : y = ((2 * (k : ℤ) + 3) - 1) := by omega
                            exact cov_P7 k hk η hη e hc
                          · obtain rfl : y = 2 * (k : ℤ) + 3 + 1 := by omega
                            exact cov_aliasA k hk η hη x e hr (by omega) (by omega) hc
                      · rcases le_or_gt x (2) with h | h
                        · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 3) with h | h
                          · rcases le_or_gt y (1) with h | h
                            · exact cov_low3 k η hη x y e (by omega) (by omega) (by omega) hc
                            · exact cov_interior_odd k η hη x y e (by omega) (by omega) hc
                          · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 2) with h | h
                            · obtain rfl : x = (2) := by omega
                              obtain rfl : y = ((2 * (k : ℤ) + 3) - 2) := by omega
                              exact cov_P14 k hk η hη e hc
                            · obtain rfl : x = 2 := by omega
                              obtain rfl : y = 2 * (k : ℤ) + 3 := by omega
                              exact cov_P19 k hk η hη e hr hc
                        · rcases le_or_gt x (3) with h | h
                          · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 3) with h | h
                            · rcases le_or_gt y (0) with h | h
                              · obtain rfl : y = 0 := by omega
                                exact cov_bottom k hk η hη x e hr (by omega) (by omega) hc
                              · rcases le_or_gt y (2) with h | h
                                · exact cov_interior_odd k η hη x y e (by omega) (by omega) hc
                                · rcases le_or_gt y (4) with h | h
                                  · rcases le_or_gt (x + y) ((2 * (k : ℤ) + 3) - 1) with h | h
                                    · exact cov_interior_odd k η hη x y e (by omega) (by omega) hc
                                    · exact cov_sumd k η hη x y e (by omega) (by omega) (by omega) hc
                                  · rcases le_or_gt (x + y) ((2 * (k : ℤ) + 3) - 1) with h | h
                                    · exact cov_interior_odd k η hη x y e (by omega) (by omega) hc
                                    · exact cov_sumd k η hη x y e (by omega) (by omega) (by omega) hc
                            · exact cov_top k η hη x y e hr (by omega) (by omega) (by omega) hc
                          · rcases le_or_gt y ((2 * (k : ℤ) + 3) - 3) with h | h
                            · rcases le_or_gt y (0) with h | h
                              · obtain rfl : y = 0 := by omega
                                exact cov_bottom k hk η hη x e hr (by omega) (by omega) hc
                              · rcases le_or_gt y (1) with h | h
                                · exact cov_interior_odd k η hη x y e (by omega) (by omega) hc
                                · rcases le_or_gt y (2) with h | h
                                  · exact cov_interior_odd k η hη x y e (by omega) (by omega) hc
                                  · rcases le_or_gt y (3) with h | h
                                    · rcases le_or_gt (x + y) ((2 * (k : ℤ) + 3) - 1) with h | h
                                      · exact cov_interior_odd k η hη x y e (by omega) (by omega) hc
                                      · exact cov_sumd k η hη x y e (by omega) (by omega) (by omega) hc
                                    · rcases le_or_gt y (4) with h | h
                                      · rcases le_or_gt (x + y) ((2 * (k : ℤ) + 3) - 1) with h | h
                                        · exact cov_interior_odd k η hη x y e (by omega) (by omega) hc
                                        · exact cov_sumd k η hη x y e (by omega) (by omega) (by omega) hc
                                      · rcases le_or_gt (x + y) ((2 * (k : ℤ) + 3) - 1) with h | h
                                        · exact cov_interior_odd k η hη x y e (by omega) (by omega) hc
                                        · rcases le_or_gt (x + y) (2 * (k : ℤ) + 3) with h | h
                                          · exact cov_sumd k η hη x y e (by omega) (by omega) (by omega) hc
                                          · exact cov_top k η hη x y e hr (by omega) (by omega) (by omega) hc
                            · exact cov_top k η hη x y e hr (by omega) (by omega) (by omega) hc
              · rcases le_or_gt x ((2 * (k : ℤ) + 3) - 2) with h | h
                · rcases le_or_gt y (0) with h | h
                  · obtain rfl : y = 0 := by omega
                    exact cov_bottom k hk η hη x e hr (by omega) (by omega) hc
                  · rcases le_or_gt y (2) with h | h
                    · exact cov_sumd k η hη x y e (by omega) (by omega) (by omega) hc
                    · exact cov_top k η hη x y e hr (by omega) (by omega) (by omega) hc
                · rcases le_or_gt x ((2 * (k : ℤ) + 3) - 1) with h | h
                  · rcases le_or_gt y (1) with h | h
                    · obtain rfl : x = ((2 * (k : ℤ) + 3) - 1) := by omega
                      obtain rfl : y = (1) := by omega
                      exact cov_P6 k hk η hη e hc
                    · exact cov_top k η hη x y e hr (by omega) (by omega) (by omega) hc
                  · rcases le_or_gt y (0) with h | h
                    · obtain rfl : y = 0 := by omega
                      exact cov_bottom k hk η hη x e hr (by omega) (by omega) hc
                    · exact cov_top k η hη x y e hr (by omega) (by omega) (by omega) hc

/-- The laplacian of the reciprocal field takes the values `0` and `-1`. -/
theorem lap_cases (k : ℕ) (p : Site) :
    laplacian (reciprocalField k) p = 0 ∨ laplacian (reciprocalField k) p = -1 := by
  rw [laplacian_reciprocal_rep k p]
  obtain ⟨hN, -⟩ := nativeRep_spec (stairEven_valid_reciprocal k) p
  rw [laplacian_reciprocal_native k hN]
  split_ifs <;> simp

/-- A policy edge at any centre is covered at its native representative, with the same step. -/
theorem ecover_of_ePolicy (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (c i : Site)
    (h : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) c i) :
    ECover k η (nativeRep (2 * (k : ℤ) + 3) c) (i - c) := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  obtain ⟨l, hl, hcl⟩ := ePolicy_rep hd (stairEven_valid_reciprocal k) c
  have hlap : laplacian (reciprocalField k) (nativeRep (2 * (k : ℤ) + 3) c) = laplacian (reciprocalField k) c :=
    (laplacian_reciprocal_rep k c).symm
  rcases lap_cases k c with h0 | h1
  · left
    refine ⟨by rw [hlap]; exact h0, ?_⟩
    exact (ePolicy_white k η hη c i h0).mp h
  · right
    refine ⟨by rw [hlap]; exact h1, ?_⟩
    have hE := retNat_edge hl hcl h
    set r := nativeRep (2 * (k : ℤ) + 3) c with hr
    rcases hE with rfl | rfl
    · left
      rw [hcl, incomingNeg_add hl]
      abel
    · right
      rw [hcl, incomingPos_add hl]
      abel

/-- The slip field of the policy at `k >= 2`: the slip does not increase along a policy edge. -/
theorem slip_field_ge2 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (c i : Site)
    (h : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) c i) :
    slipPermits (reciprocalField k) (fun z => reciprocalField k (z + η • (reciprocalFrame k).shortShift)) c i := by
  have hE := ecover_of_ePolicy k η hη c i h
  obtain ⟨hN, i0, j0, hcr⟩ := nativeRep_spec (stairEven_valid_reciprocal k) c
  have hT := cov_shift k η (nativeRep (2 * (k : ℤ) + 3) c) c (i - c) i0 j0 hcr (cover_ge2 k hk η hη _ hN (i - c) hE)
  have hs := slip_of_SE k η c (i - c) hT.1
  have e1 : c + (i - c) = i := by abel
  rw [e1] at hs
  unfold slipPermits slipIncrement
  dsimp only
  unfold ChildFrame.slip at hs
  linarith

/-- The price field of the policy at `k >= 2`. -/
theorem price_field_ge2 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (c i : Site)
    (h : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) c i) :
    (reciprocalFrame k).price (reciprocalField k) i ≤ (reciprocalFrame k).price (reciprocalField k) c := by
  have hE := ecover_of_ePolicy k η hη c i h
  obtain ⟨hN, i0, j0, hcr⟩ := nativeRep_spec (stairEven_valid_reciprocal k) c
  have hT := cov_shift k η (nativeRep (2 * (k : ℤ) + 3) c) c (i - c) i0 j0 hcr (cover_ge2 k hk η hη _ hN (i - c) hE)
  have hp := price_of_PE k c (i - c) hT.2.1
  have e1 : c + (i - c) = i := by abel
  rw [e1] at hp
  exact hp

/-- The chain field of the policy at `k >= 2`. -/
theorem chain_field_ge2 (k : ℕ) (hk : 2 ≤ (k : ℤ)) (η : ℤ) (hη : η = 1 ∨ η = -1) (c i : Site)
    (h : ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) c i) :
    (reciprocalFrame k).chainPotential (reciprocalField k) η i ≤
      (reciprocalFrame k).chainPotential (reciprocalField k) η c := by
  have hE := ecover_of_ePolicy k η hη c i h
  obtain ⟨hN, i0, j0, hcr⟩ := nativeRep_spec (stairEven_valid_reciprocal k) c
  have hT := cov_shift k η (nativeRep (2 * (k : ℤ) + 3) c) c (i - c) i0 j0 hcr (cover_ge2 k hk η hη _ hN (i - c) hE)
  have hch := chain_of_CE k η c (i - c) hT.2.2
  have e1 : c + (i - c) = i := by abel
  rw [e1] at hch
  exact hch

/-- The upward vertical increment at the origin is `-1` (stair values at `(0, 1)` and `(0, 0)`). -/
theorem incr_c0_up (k : ℕ) : incr (reciprocalField k) (0, 1) ((0 : ℤ), (0 : ℤ)) = -1 := by
  have hp : ((0 : ℤ), (0 : ℤ)) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites := mem_raw_corner0 k
  have hpe : ((0 : ℤ), (0 : ℤ)) + (0, 1) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites := by
    have e : ((0 : ℤ), (0 : ℤ)) + (0, 1) = ((0 : ℤ), (1 : ℤ)) := by ext <;> simp
    rw [e]
    exact mem_raw_of_box k 0 1 (by omega)
  rw [incr_raw_stair k (0, 1) _ hp hpe]
  have e : ((0 : ℤ), (0 : ℤ)) + (0, 1) = ((0 : ℤ), (1 : ℤ)) := by ext <;> simp
  rw [e]
  unfold BaseMask.stairEvenValue
  rw [if_neg (not_stairCorner _ 0 1 (by omega)), if_pos (corner_yes _ 0 0 (by omega))]
  norm_num

/-- The downward vertical increment at the origin is `0` (through the kernel translation `U`). -/
theorem incr_c0_dn (k : ℕ) : incr (reciprocalField k) (0, -1) ((0 : ℤ), (0 : ℤ)) = 0 := by
  have h := incr_U_inv k (0, -1) ((0 : ℤ), (0 : ℤ))
  have e : ((0 : ℤ), (0 : ℤ)) + (2 * (k : ℤ) + 3, 1) = (2 * (k : ℤ) + 3, 1) := by ext <;> simp
  rw [e] at h
  rw [← h, incr_vert k (-1) (2 * (k : ℤ) + 3) 1 (Or.inr rfl)
    (mem_raw_of_box k (2 * (k : ℤ) + 3) 1 (by omega))
    (mem_raw_of_box k (2 * (k : ℤ) + 3) (1 + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  norm_num

/-- The downward vertical increment at `(0, 1)` into the origin is `1`. -/
theorem incr_c0_fromdown (k : ℕ) : incr (reciprocalField k) (0, -1) ((0 : ℤ), (1 : ℤ)) = 1 := by
  have h := incr_c0_up k
  unfold incr at h ⊢
  have e1 : ((0 : ℤ), (1 : ℤ)) + (0, -1) = ((0 : ℤ), (0 : ℤ)) := by ext <;> simp
  have e2 : ((0 : ℤ), (0 : ℤ)) + (0, 1) = ((0 : ℤ), (1 : ℤ)) := by ext <;> simp
  rw [e2] at h
  rw [e1]
  linarith

theorem tr0_m1_2_p_my (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, -1) ((-1), (2)) ≤ incr (reciprocalField k) (0, -1) ((-3), (2)) ∧
    incr (reciprocalField k) (0, -1) ((-1), (2)) - incr (reciprocalField k) (0, -1) ((-2), (3)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((-1), (2)) - incr (reciprocalField k) (0, -1) ((-4), (3)) ≤ -1 := by
  have hZ1_0 : incr (reciprocalField k) (0, -1) ((-1), (2)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 1), (3)) :=
    incr_eq_U k (0, -1) ((-1), (2)) (((2 * (k : ℤ) + 3) - 1), (3)) (by ext <;> (simp; try ring))
  have hZ2_0 : incr (reciprocalField k) (0, -1) ((-3), (2)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 3), (3)) :=
    incr_eq_U k (0, -1) ((-3), (2)) (((2 * (k : ℤ) + 3) - 3), (3)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (0, -1) ((-2), (3)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (4)) :=
    incr_eq_U k (0, -1) ((-2), (3)) (((2 * (k : ℤ) + 3) - 2), (4)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, -1) ((-4), (3)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 4), (4)) :=
    incr_eq_U k (0, -1) ((-4), (3)) (((2 * (k : ℤ) + 3) - 4), (4)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 1), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 1) (3) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (3) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 3), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 3) (3) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) (3) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 2) (4) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (4) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 4), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 4) (4) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) (4) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_m1_2_m_py (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, 1) ((-1), (2)) ≤ incr (reciprocalField k) (0, 1) ((1), (2)) ∧
    incr (reciprocalField k) (0, 1) ((-1), (2)) - incr (reciprocalField k) (0, 1) ((-2), (3)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((-1), (2)) - incr (reciprocalField k) (0, 1) ((0), (3)) ≤ 1 := by
  have hZ3_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 3), (2 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-2), (3)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 3), (2 - (2 * (k : ℤ) + 3))) ((-2), (3)) (by ext <;> (simp; try ring))
  have hZ3_1 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 3), (2 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((2 * (2 * (k : ℤ) + 3) + -3), (3 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (0, 1) (((2 * (k : ℤ) + 3) - 3), (2 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -3), (3 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, 1) ((-1), (2)) = -((2)) := by
    rw [incr_vert k 1 (-1) (2) (Or.inl rfl) (mem_raw_of_box k (-1) (2) (by omega)) (mem_raw_of_box k (-1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((1), (2)) = -((2)) := by
    rw [incr_vert k 1 (1) (2) (Or.inl rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((2 * (2 * (k : ℤ) + 3) + -3), (3 - (2 * (k : ℤ) + 3))) = -((3 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 (2 * (2 * (k : ℤ) + 3) + -3) (3 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -3) (3 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -3) ((3 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((0), (3)) = -((3)) := by
    rw [incr_vert k 1 (0) (3) (Or.inl rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_m1_3_p_px (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (1, 0) ((-1), (3)) ≤ incr (reciprocalField k) (1, 0) ((-3), (3)) ∧
    incr (reciprocalField k) (1, 0) ((-1), (3)) - incr (reciprocalField k) (1, 0) ((-2), (4)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((-1), (3)) - incr (reciprocalField k) (1, 0) ((-4), (4)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (1, 0) ((-3), (3)) = incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 3), (4)) :=
    incr_eq_U k (1, 0) ((-3), (3)) (((2 * (k : ℤ) + 3) - 3), (4)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 3), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((-2), (4)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) (((2 * (k : ℤ) + 3) - 3), (3 - (2 * (k : ℤ) + 3))) ((-2), (4)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 5), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((-4), (4)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) (((2 * (k : ℤ) + 3) - 5), (3 - (2 * (k : ℤ) + 3))) ((-4), (4)) (by ext <;> (simp; try ring))
  have hZ4_1 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 5), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((2 * (2 * (k : ℤ) + 3) + -5), (4 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (1, 0) (((2 * (k : ℤ) + 3) - 5), (3 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -5), (4 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (1, 0) ((-1), (3)) = min ((-1) + (1) - 1) 0 - min ((-1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (-1) (3) (mem_raw_of_box k ((-1) + (1)) (3) (by omega)) (mem_raw_of_box k (-1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-1) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((-1) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-1) (3) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 3), (4)) = min (((2 * (k : ℤ) + 3) - 3) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 3) (4) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 3) + (1)) (4) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (4) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 3) + (1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (4) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 3), (3 - (2 * (k : ℤ) + 3))) = min (((2 * (k : ℤ) + 3) - 3) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 3) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 3) (3 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 3) + (1)) (3 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (3 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 3) + (1)) (3 - (2 * (k : ℤ) + 3)) (by omega)) (corner_yes (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (3 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((2 * (2 * (k : ℤ) + 3) + -5), (4 - (2 * (k : ℤ) + 3))) = min ((2 * (2 * (k : ℤ) + 3) + -5) + (1) - 1) 0 - min ((2 * (2 * (k : ℤ) + 3) + -5) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2 * (2 * (k : ℤ) + 3) + -5) (4 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k ((2 * (2 * (k : ℤ) + 3) + -5) + (1)) (4 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -5) (4 - (2 * (k : ℤ) + 3)) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2 * (2 * (k : ℤ) + 3) + -5) (4 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (2 * (k : ℤ) + 3) + -5) + (1)) (4 - (2 * (k : ℤ) + 3)) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2 * (2 * (k : ℤ) + 3) + -5) (4 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_m1_3_m_mx (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (-1, 0) ((-1), (3)) ≤ incr (reciprocalField k) (-1, 0) ((1), (3)) ∧
    incr (reciprocalField k) (-1, 0) ((-1), (3)) - incr (reciprocalField k) (-1, 0) ((-2), (4)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((-1), (3)) - incr (reciprocalField k) (-1, 0) ((0), (4)) ≤ 0 := by
  have hZ1_0 : incr (reciprocalField k) (-1, 0) ((-1), (3)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 1), (4)) :=
    incr_eq_U k (-1, 0) ((-1), (3)) (((2 * (k : ℤ) + 3) - 1), (4)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 3), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (-1, 0) ((-2), (4)) + ((2 * (k : ℤ) + 3) * 0 - -1) :=
    incr_eq_T k (-1, 0) (((2 * (k : ℤ) + 3) - 3), (3 - (2 * (k : ℤ) + 3))) ((-2), (4)) (by ext <;> (simp; try ring))
  have hZ3_1 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 3), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (-1, 0) ((2 * (2 * (k : ℤ) + 3) + -3), (4 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (-1, 0) (((2 * (k : ℤ) + 3) - 3), (3 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -3), (4 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 1), (4)) = min (((2 * (k : ℤ) + 3) - 1) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 1) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 1) (4) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 1) + (-1)) (4) (by omega)) (mem_raw_corner2' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 1) + (-1)) (4) (by omega)) (corner_yes (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (4) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) ((1), (3)) = min ((1) + (-1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (1) (3) (mem_raw_of_box k ((1) + (-1)) (3) (by omega)) (mem_raw_of_box k (1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (3) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (-1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (3) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((2 * (2 * (k : ℤ) + 3) + -3), (4 - (2 * (k : ℤ) + 3))) = min ((2 * (2 * (k : ℤ) + 3) + -3) + (-1) - 1) 0 - min ((2 * (2 * (k : ℤ) + 3) + -3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (2 * (2 * (k : ℤ) + 3) + -3) (4 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k ((2 * (2 * (k : ℤ) + 3) + -3) + (-1)) (4 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -3) (4 - (2 * (k : ℤ) + 3)) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2 * (2 * (k : ℤ) + 3) + -3) (4 - (2 * (k : ℤ) + 3)) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (2 * (k : ℤ) + 3) + -3) + (-1)) (4 - (2 * (k : ℤ) + 3)) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2 * (2 * (k : ℤ) + 3) + -3) (4 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) ((0), (4)) = min ((0) + (-1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (0) (4) (mem_raw_of_box k ((0) + (-1)) (4) (by omega)) (mem_raw_of_box k (0) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (4) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_m1_4_p_my (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, -1) ((-1), (4)) ≤ incr (reciprocalField k) (0, -1) ((-3), (4)) ∧
    incr (reciprocalField k) (0, -1) ((-1), (4)) - incr (reciprocalField k) (0, -1) ((-2), (5)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((-1), (4)) - incr (reciprocalField k) (0, -1) ((-4), (5)) ≤ -1 := by
  have hZ2_0 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 4), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, -1) ((-3), (4)) + ((2 * (k : ℤ) + 3) * -1 - 0) :=
    incr_eq_T k (0, -1) (((2 * (k : ℤ) + 3) - 4), (3 - (2 * (k : ℤ) + 3))) ((-3), (4)) (by ext <;> (simp; try ring))
  have hZ2_1 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 4), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, -1) ((2 * (2 * (k : ℤ) + 3) + -4), (4 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (0, -1) (((2 * (k : ℤ) + 3) - 4), (3 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -4), (4 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 3), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, -1) ((-2), (5)) + ((2 * (k : ℤ) + 3) * -1 - 0) :=
    incr_eq_T k (0, -1) (((2 * (k : ℤ) + 3) - 3), (4 - (2 * (k : ℤ) + 3))) ((-2), (5)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 5), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, -1) ((-4), (5)) + ((2 * (k : ℤ) + 3) * -1 - 0) :=
    incr_eq_T k (0, -1) (((2 * (k : ℤ) + 3) - 5), (4 - (2 * (k : ℤ) + 3))) ((-4), (5)) (by ext <;> (simp; try ring))
  have hZ4_1 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 5), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, -1) ((2 * (2 * (k : ℤ) + 3) + -5), (5 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (0, -1) (((2 * (k : ℤ) + 3) - 5), (4 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -5), (5 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, -1) ((-1), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (-1) (4) (Or.inr rfl) (mem_raw_of_box k (-1) (4) (by omega)) (mem_raw_of_box k (-1) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((2 * (2 * (k : ℤ) + 3) + -4), (4 - (2 * (k : ℤ) + 3))) = ((4 - (2 * (k : ℤ) + 3))) + -1 := by
    rw [incr_vert k (-1) (2 * (2 * (k : ℤ) + 3) + -4) (4 - (2 * (k : ℤ) + 3)) (Or.inr rfl) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -4) (4 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -4) ((4 - (2 * (k : ℤ) + 3)) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 3), (4 - (2 * (k : ℤ) + 3))) = 1 := by
    rw [show (((2 * (k : ℤ) + 3) - 3), (4 - (2 * (k : ℤ) + 3))) = ((0 : ℤ), (1 : ℤ)) from by ext <;> omega]
    exact incr_c0_fromdown k
  have vZ4 : incr (reciprocalField k) (0, -1) ((2 * (2 * (k : ℤ) + 3) + -5), (5 - (2 * (k : ℤ) + 3))) = ((5 - (2 * (k : ℤ) + 3))) + -1 := by
    rw [incr_vert k (-1) (2 * (2 * (k : ℤ) + 3) + -5) (5 - (2 * (k : ℤ) + 3)) (Or.inr rfl) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -5) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -5) ((5 - (2 * (k : ℤ) + 3)) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_m1_4_m_py (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, 1) ((-1), (4)) ≤ incr (reciprocalField k) (0, 1) ((1), (4)) ∧
    incr (reciprocalField k) (0, 1) ((-1), (4)) - incr (reciprocalField k) (0, 1) ((-2), (5)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((-1), (4)) - incr (reciprocalField k) (0, 1) ((0), (5)) ≤ 1 := by
  have hZ1_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-1), (4)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 2), (3 - (2 * (k : ℤ) + 3))) ((-1), (4)) (by ext <;> (simp; try ring))
  have hZ2_0 : incr (reciprocalField k) (0, 1) ((2 * (k : ℤ) + 3), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((1), (4)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) ((2 * (k : ℤ) + 3), (3 - (2 * (k : ℤ) + 3))) ((1), (4)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 3), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-2), (5)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 3), (4 - (2 * (k : ℤ) + 3))) ((-2), (5)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 1), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((0), (5)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 1), (4 - (2 * (k : ℤ) + 3))) ((0), (5)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (3 - (2 * (k : ℤ) + 3))) = -((3 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 2) (3 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (3 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((3 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((2 * (k : ℤ) + 3), (3 - (2 * (k : ℤ) + 3))) = -((3 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (k : ℤ) + 3) ((3 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 3), (4 - (2 * (k : ℤ) + 3))) = -((4 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 3) (4 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) (4 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) ((4 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 1), (4 - (2 * (k : ℤ) + 3))) = -((4 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 1) (4 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (4 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) ((4 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_0_0_p_px (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (1, 0) ((0), (0)) ≤ incr (reciprocalField k) (1, 0) ((-2), (0)) ∧
    incr (reciprocalField k) (1, 0) ((0), (0)) - incr (reciprocalField k) (1, 0) ((-1), (1)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((0), (0)) - incr (reciprocalField k) (1, 0) ((-3), (1)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (1, 0) ((-2), (0)) = incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (1)) :=
    incr_eq_U k (1, 0) ((-2), (0)) (((2 * (k : ℤ) + 3) - 2), (1)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (1, 0) ((-1), (1)) = incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 1), (2)) :=
    incr_eq_U k (1, 0) ((-1), (1)) (((2 * (k : ℤ) + 3) - 1), (2)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (1, 0) ((-3), (1)) = incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 3), (2)) :=
    incr_eq_U k (1, 0) ((-3), (1)) (((2 * (k : ℤ) + 3) - 3), (2)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (1, 0) ((0), (0)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) (0) (0) (mem_raw_of_box k ((0) + (1)) (0) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (0) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (0) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (0) (0) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (1)) = min (((2 * (k : ℤ) + 3) - 2) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 2) (1) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 2) + (1)) (1) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 2) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (1) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 1), (2)) = min (((2 * (k : ℤ) + 3) - 1) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 1) (2) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 1) + (1)) (2) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 1) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (2) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 3), (2)) = min (((2 * (k : ℤ) + 3) - 3) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 3) (2) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 3) + (1)) (2) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 3) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (2) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_0_0_m_px (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (1, 0) ((0), (0)) ≤ incr (reciprocalField k) (1, 0) ((2), (0)) ∧
    incr (reciprocalField k) (1, 0) ((0), (0)) - incr (reciprocalField k) (1, 0) ((-1), (1)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((0), (0)) - incr (reciprocalField k) (1, 0) ((1), (1)) ≤ 0 := by
  have hZ3_0 : incr (reciprocalField k) (1, 0) ((-1), (1)) = incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 1), (2)) :=
    incr_eq_U k (1, 0) ((-1), (1)) (((2 * (k : ℤ) + 3) - 1), (2)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (1, 0) ((0), (0)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) (0) (0) (mem_raw_of_box k ((0) + (1)) (0) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (0) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (0) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (0) (0) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((2), (0)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (0) (mem_raw_of_box k ((2) + (1)) (0) (by omega)) (mem_raw_of_box k (2) (0) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (0) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (0) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 1), (2)) = min (((2 * (k : ℤ) + 3) - 1) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 1) (2) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 1) + (1)) (2) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 1) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (2) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((1), (1)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (1) (mem_raw_of_box k ((1) + (1)) (1) (by omega)) (mem_raw_of_box k (1) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (1) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_0_1_p_my (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, -1) ((0), (1)) ≤ incr (reciprocalField k) (0, -1) ((-2), (1)) ∧
    incr (reciprocalField k) (0, -1) ((0), (1)) - incr (reciprocalField k) (0, -1) ((-1), (2)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((0), (1)) - incr (reciprocalField k) (0, -1) ((-3), (2)) ≤ -1 := by
  have hZ2_0 : incr (reciprocalField k) (0, -1) ((-2), (1)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (2)) :=
    incr_eq_U k (0, -1) ((-2), (1)) (((2 * (k : ℤ) + 3) - 2), (2)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (0, -1) ((-1), (2)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 1), (3)) :=
    incr_eq_U k (0, -1) ((-1), (2)) (((2 * (k : ℤ) + 3) - 1), (3)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, -1) ((-3), (2)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 3), (3)) :=
    incr_eq_U k (0, -1) ((-3), (2)) (((2 * (k : ℤ) + 3) - 3), (3)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, -1) ((0), (1)) = 1 := by
    rw [show ((0), (1)) = ((0 : ℤ), (1 : ℤ)) from by ext <;> omega]
    exact incr_c0_fromdown k
  have vZ2 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 2) (2) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (2) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 1), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 1) (3) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (3) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 3), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 3) (3) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) (3) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_0_1_m_py (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, 1) ((0), (1)) ≤ incr (reciprocalField k) (0, 1) ((2), (1)) ∧
    incr (reciprocalField k) (0, 1) ((0), (1)) - incr (reciprocalField k) (0, 1) ((-1), (2)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((0), (1)) - incr (reciprocalField k) (0, 1) ((1), (2)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((0), (1)) = -((1)) := by
    rw [incr_vert k 1 (0) (1) (Or.inl rfl) (mem_raw_of_box k (0) (1) (by omega)) (mem_raw_of_box k (0) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((2), (1)) = -((1)) := by
    rw [incr_vert k 1 (2) (1) (Or.inl rfl) (mem_raw_of_box k (2) (1) (by omega)) (mem_raw_of_box k (2) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((-1), (2)) = -((2)) := by
    rw [incr_vert k 1 (-1) (2) (Or.inl rfl) (mem_raw_of_box k (-1) (2) (by omega)) (mem_raw_of_box k (-1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((1), (2)) = -((2)) := by
    rw [incr_vert k 1 (1) (2) (Or.inl rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_0_2_p_mx (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (-1, 0) ((0), (2)) ≤ incr (reciprocalField k) (-1, 0) ((-2), (2)) ∧
    incr (reciprocalField k) (-1, 0) ((0), (2)) - incr (reciprocalField k) (-1, 0) ((-1), (3)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((0), (2)) - incr (reciprocalField k) (-1, 0) ((-3), (3)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (-1, 0) ((-2), (2)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 2), (3)) :=
    incr_eq_U k (-1, 0) ((-2), (2)) (((2 * (k : ℤ) + 3) - 2), (3)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (-1, 0) ((-1), (3)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 1), (4)) :=
    incr_eq_U k (-1, 0) ((-1), (3)) (((2 * (k : ℤ) + 3) - 1), (4)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (-1, 0) ((-3), (3)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 3), (4)) :=
    incr_eq_U k (-1, 0) ((-3), (3)) (((2 * (k : ℤ) + 3) - 3), (4)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (-1, 0) ((0), (2)) = min ((0) + (-1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (0) (2) (mem_raw_of_box k ((0) + (-1)) (2) (by omega)) (mem_raw_of_box k (0) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (2) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (-1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (2) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 2), (3)) = min (((2 * (k : ℤ) + 3) - 2) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 2) (3) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 2) + (-1)) (3) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (3) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 2) + (-1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (3) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 1), (4)) = min (((2 * (k : ℤ) + 3) - 1) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 1) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 1) (4) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 1) + (-1)) (4) (by omega)) (mem_raw_corner2' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 1) + (-1)) (4) (by omega)) (corner_yes (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (4) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 3), (4)) = min (((2 * (k : ℤ) + 3) - 3) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 3) (4) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 3) + (-1)) (4) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 3) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (4) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_0_2_m_mx (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (-1, 0) ((0), (2)) ≤ incr (reciprocalField k) (-1, 0) ((2), (2)) ∧
    incr (reciprocalField k) (-1, 0) ((0), (2)) - incr (reciprocalField k) (-1, 0) ((-1), (3)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((0), (2)) - incr (reciprocalField k) (-1, 0) ((1), (3)) ≤ 0 := by
  have hZ3_0 : incr (reciprocalField k) (-1, 0) ((-1), (3)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 1), (4)) :=
    incr_eq_U k (-1, 0) ((-1), (3)) (((2 * (k : ℤ) + 3) - 1), (4)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (-1, 0) ((0), (2)) = min ((0) + (-1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (0) (2) (mem_raw_of_box k ((0) + (-1)) (2) (by omega)) (mem_raw_of_box k (0) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (2) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (-1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (2) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) ((2), (2)) = min ((2) + (-1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (2) (2) (mem_raw_of_box k ((2) + (-1)) (2) (by omega)) (mem_raw_of_box k (2) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (2) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (-1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (2) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 1), (4)) = min (((2 * (k : ℤ) + 3) - 1) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 1) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 1) (4) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 1) + (-1)) (4) (by omega)) (mem_raw_corner2' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 1) + (-1)) (4) (by omega)) (corner_yes (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (4) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) ((1), (3)) = min ((1) + (-1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (1) (3) (mem_raw_of_box k ((1) + (-1)) (3) (by omega)) (mem_raw_of_box k (1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (3) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (-1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (3) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_0_3_p_my (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, -1) ((0), (3)) ≤ incr (reciprocalField k) (0, -1) ((-2), (3)) ∧
    incr (reciprocalField k) (0, -1) ((0), (3)) - incr (reciprocalField k) (0, -1) ((-1), (4)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((0), (3)) - incr (reciprocalField k) (0, -1) ((-3), (4)) ≤ -1 := by
  have hZ2_0 : incr (reciprocalField k) (0, -1) ((-2), (3)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (4)) :=
    incr_eq_U k (0, -1) ((-2), (3)) (((2 * (k : ℤ) + 3) - 2), (4)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 4), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, -1) ((-3), (4)) + ((2 * (k : ℤ) + 3) * -1 - 0) :=
    incr_eq_T k (0, -1) (((2 * (k : ℤ) + 3) - 4), (3 - (2 * (k : ℤ) + 3))) ((-3), (4)) (by ext <;> (simp; try ring))
  have hZ4_1 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 4), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, -1) ((2 * (2 * (k : ℤ) + 3) + -4), (4 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (0, -1) (((2 * (k : ℤ) + 3) - 4), (3 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -4), (4 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, -1) ((0), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (0) (3) (Or.inr rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 2) (4) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (4) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((-1), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (-1) (4) (Or.inr rfl) (mem_raw_of_box k (-1) (4) (by omega)) (mem_raw_of_box k (-1) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((2 * (2 * (k : ℤ) + 3) + -4), (4 - (2 * (k : ℤ) + 3))) = ((4 - (2 * (k : ℤ) + 3))) + -1 := by
    rw [incr_vert k (-1) (2 * (2 * (k : ℤ) + 3) + -4) (4 - (2 * (k : ℤ) + 3)) (Or.inr rfl) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -4) (4 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -4) ((4 - (2 * (k : ℤ) + 3)) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_0_3_p_py (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, 1) ((0), (3)) ≤ incr (reciprocalField k) (0, 1) ((-2), (3)) ∧
    incr (reciprocalField k) (0, 1) ((0), (3)) - incr (reciprocalField k) (0, 1) ((-1), (4)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((0), (3)) - incr (reciprocalField k) (0, 1) ((-3), (4)) ≤ 1 := by
  have hZ2_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 3), (2 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-2), (3)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 3), (2 - (2 * (k : ℤ) + 3))) ((-2), (3)) (by ext <;> (simp; try ring))
  have hZ2_1 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 3), (2 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((2 * (2 * (k : ℤ) + 3) + -3), (3 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (0, 1) (((2 * (k : ℤ) + 3) - 3), (2 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -3), (3 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-1), (4)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 2), (3 - (2 * (k : ℤ) + 3))) ((-1), (4)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 4), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-3), (4)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 4), (3 - (2 * (k : ℤ) + 3))) ((-3), (4)) (by ext <;> (simp; try ring))
  have hZ4_1 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 4), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((2 * (2 * (k : ℤ) + 3) + -4), (4 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (0, 1) (((2 * (k : ℤ) + 3) - 4), (3 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -4), (4 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, 1) ((0), (3)) = -((3)) := by
    rw [incr_vert k 1 (0) (3) (Or.inl rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((2 * (2 * (k : ℤ) + 3) + -3), (3 - (2 * (k : ℤ) + 3))) = -((3 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 (2 * (2 * (k : ℤ) + 3) + -3) (3 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -3) (3 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -3) ((3 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (3 - (2 * (k : ℤ) + 3))) = -((3 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 2) (3 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (3 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((3 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((2 * (2 * (k : ℤ) + 3) + -4), (4 - (2 * (k : ℤ) + 3))) = -((4 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 (2 * (2 * (k : ℤ) + 3) + -4) (4 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -4) (4 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -4) ((4 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_0_3_m_my (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, -1) ((0), (3)) ≤ incr (reciprocalField k) (0, -1) ((2), (3)) ∧
    incr (reciprocalField k) (0, -1) ((0), (3)) - incr (reciprocalField k) (0, -1) ((-1), (4)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((0), (3)) - incr (reciprocalField k) (0, -1) ((1), (4)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((0), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (0) (3) (Or.inr rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((2), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (2) (3) (Or.inr rfl) (mem_raw_of_box k (2) (3) (by omega)) (mem_raw_of_box k (2) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((-1), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (-1) (4) (Or.inr rfl) (mem_raw_of_box k (-1) (4) (by omega)) (mem_raw_of_box k (-1) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((1), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (1) (4) (Or.inr rfl) (mem_raw_of_box k (1) (4) (by omega)) (mem_raw_of_box k (1) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_0_3_m_py (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, 1) ((0), (3)) ≤ incr (reciprocalField k) (0, 1) ((2), (3)) ∧
    incr (reciprocalField k) (0, 1) ((0), (3)) - incr (reciprocalField k) (0, 1) ((-1), (4)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((0), (3)) - incr (reciprocalField k) (0, 1) ((1), (4)) ≤ 1 := by
  have hZ3_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-1), (4)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 2), (3 - (2 * (k : ℤ) + 3))) ((-1), (4)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, 1) ((2 * (k : ℤ) + 3), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((1), (4)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) ((2 * (k : ℤ) + 3), (3 - (2 * (k : ℤ) + 3))) ((1), (4)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, 1) ((0), (3)) = -((3)) := by
    rw [incr_vert k 1 (0) (3) (Or.inl rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((2), (3)) = 1 - (2 * (k : ℤ) + 3) := by
    rw [show ((2), (3)) = ((2 : ℤ), 2 * (k : ℤ) + 3) from by ext <;> omega]
    exact incr_c2low_up k
  have vZ3 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (3 - (2 * (k : ℤ) + 3))) = -((3 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 2) (3 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (3 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((3 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((2 * (k : ℤ) + 3), (3 - (2 * (k : ℤ) + 3))) = -((3 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (k : ℤ) + 3) ((3 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_0_4_p_px (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (1, 0) ((0), (4)) ≤ incr (reciprocalField k) (1, 0) ((-2), (4)) ∧
    incr (reciprocalField k) (1, 0) ((0), (4)) - incr (reciprocalField k) (1, 0) ((-1), (5)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((0), (4)) - incr (reciprocalField k) (1, 0) ((-3), (5)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 3), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((-2), (4)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) (((2 * (k : ℤ) + 3) - 3), (3 - (2 * (k : ℤ) + 3))) ((-2), (4)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((-1), (5)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) (((2 * (k : ℤ) + 3) - 2), (4 - (2 * (k : ℤ) + 3))) ((-1), (5)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 4), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((-3), (5)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) (((2 * (k : ℤ) + 3) - 4), (4 - (2 * (k : ℤ) + 3))) ((-3), (5)) (by ext <;> (simp; try ring))
  have hZ4_1 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 4), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((2 * (2 * (k : ℤ) + 3) + -4), (5 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (1, 0) (((2 * (k : ℤ) + 3) - 4), (4 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -4), (5 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (1, 0) ((0), (4)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (4) (mem_raw_of_box k ((0) + (1)) (4) (by omega)) (mem_raw_of_box k (0) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (4) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (4) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 3), (3 - (2 * (k : ℤ) + 3))) = min (((2 * (k : ℤ) + 3) - 3) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 3) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 3) (3 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 3) + (1)) (3 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (3 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 3) + (1)) (3 - (2 * (k : ℤ) + 3)) (by omega)) (corner_yes (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (3 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (4 - (2 * (k : ℤ) + 3))) = min (((2 * (k : ℤ) + 3) - 2) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 2) (4 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 2) + (1)) (4 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (4 - (2 * (k : ℤ) + 3)) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (4 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 2) + (1)) (4 - (2 * (k : ℤ) + 3)) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (4 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((2 * (2 * (k : ℤ) + 3) + -4), (5 - (2 * (k : ℤ) + 3))) = min ((2 * (2 * (k : ℤ) + 3) + -4) + (1) - 1) 0 - min ((2 * (2 * (k : ℤ) + 3) + -4) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2 * (2 * (k : ℤ) + 3) + -4) (5 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k ((2 * (2 * (k : ℤ) + 3) + -4) + (1)) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -4) (5 - (2 * (k : ℤ) + 3)) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2 * (2 * (k : ℤ) + 3) + -4) (5 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (2 * (k : ℤ) + 3) + -4) + (1)) (5 - (2 * (k : ℤ) + 3)) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2 * (2 * (k : ℤ) + 3) + -4) (5 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_0_4_m_px (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (1, 0) ((0), (4)) ≤ incr (reciprocalField k) (1, 0) ((2), (4)) ∧
    incr (reciprocalField k) (1, 0) ((0), (4)) - incr (reciprocalField k) (1, 0) ((-1), (5)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((0), (4)) - incr (reciprocalField k) (1, 0) ((1), (5)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (1, 0) ((2), (4)) = incr (reciprocalField k) (1, 0) ((2 - (2 * (k : ℤ) + 3)), (3)) :=
    (incr_eq_U k (1, 0) ((2 - (2 * (k : ℤ) + 3)), (3)) ((2), (4)) (by ext <;> (simp; try ring))).symm
  have hZ3_0 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((-1), (5)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) (((2 * (k : ℤ) + 3) - 2), (4 - (2 * (k : ℤ) + 3))) ((-1), (5)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (1, 0) ((2 * (k : ℤ) + 3), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((1), (5)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) ((2 * (k : ℤ) + 3), (4 - (2 * (k : ℤ) + 3))) ((1), (5)) (by ext <;> (simp; try ring))
  have hZ4_1 : incr (reciprocalField k) (1, 0) ((2 * (k : ℤ) + 3), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((0), (3 - (2 * (k : ℤ) + 3))) :=
    (incr_eq_U k (1, 0) ((0), (3 - (2 * (k : ℤ) + 3))) ((2 * (k : ℤ) + 3), (4 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (1, 0) ((0), (4)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (4) (mem_raw_of_box k ((0) + (1)) (4) (by omega)) (mem_raw_of_box k (0) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (4) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (4) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((2 - (2 * (k : ℤ) + 3)), (3)) = min ((2 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((2 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2 - (2 * (k : ℤ) + 3)) (3) (mem_raw_of_box k ((2 - (2 * (k : ℤ) + 3)) + (1)) (3) (by omega)) (mem_raw_of_box k (2 - (2 * (k : ℤ) + 3)) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2 - (2 * (k : ℤ) + 3)) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2 - (2 * (k : ℤ) + 3)) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2 - (2 * (k : ℤ) + 3)) (3) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (4 - (2 * (k : ℤ) + 3))) = min (((2 * (k : ℤ) + 3) - 2) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 2) (4 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 2) + (1)) (4 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (4 - (2 * (k : ℤ) + 3)) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (4 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 2) + (1)) (4 - (2 * (k : ℤ) + 3)) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (4 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((0), (3 - (2 * (k : ℤ) + 3))) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) (0) (3 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k ((0) + (1)) (3 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (0) (3 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (3 - (2 * (k : ℤ) + 3)) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (0) (3 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_1_0_p_my (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, -1) ((1), (0)) ≤ incr (reciprocalField k) (0, -1) ((-1), (0)) ∧
    incr (reciprocalField k) (0, -1) ((1), (0)) - incr (reciprocalField k) (0, -1) ((0), (1)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((1), (0)) - incr (reciprocalField k) (0, -1) ((-2), (1)) ≤ -1 := by
  have hZ1_0 : incr (reciprocalField k) (0, -1) ((1), (0)) = incr (reciprocalField k) (0, -1) ((2 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) + ((2 * (k : ℤ) + 3) * -1 - 0) :=
    incr_eq_T k (0, -1) ((1), (0)) ((2 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) (by ext <;> (simp; try ring))
  have hZ2_0 : incr (reciprocalField k) (0, -1) ((-1), (0)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 1), (1)) :=
    incr_eq_U k (0, -1) ((-1), (0)) (((2 * (k : ℤ) + 3) - 1), (1)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, -1) ((-2), (1)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (2)) :=
    incr_eq_U k (0, -1) ((-2), (1)) (((2 * (k : ℤ) + 3) - 2), (2)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, -1) ((2 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) = (((2 * (k : ℤ) + 3) + 1)) + -1 := by
    rw [incr_vert k (-1) (2 - (2 * (k : ℤ) + 3)) ((2 * (k : ℤ) + 3) + 1) (Or.inr rfl) (mem_raw_of_box k (2 - (2 * (k : ℤ) + 3)) ((2 * (k : ℤ) + 3) + 1) (by omega)) (mem_raw_of_box k (2 - (2 * (k : ℤ) + 3)) (((2 * (k : ℤ) + 3) + 1) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 1), (1)) = ((1)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 1) (1) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (1) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) ((1) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((0), (1)) = 1 := by
    rw [show ((0), (1)) = ((0 : ℤ), (1 : ℤ)) from by ext <;> omega]
    exact incr_c0_fromdown k
  have vZ4 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 2) (2) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (2) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_1_0_m_py (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, 1) ((1), (0)) ≤ incr (reciprocalField k) (0, 1) ((3), (0)) ∧
    incr (reciprocalField k) (0, 1) ((1), (0)) - incr (reciprocalField k) (0, 1) ((0), (1)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((1), (0)) - incr (reciprocalField k) (0, 1) ((2), (1)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((1), (0)) = -((0)) := by
    rw [incr_vert k 1 (1) (0) (Or.inl rfl) (mem_raw_of_box k (1) (0) (by omega)) (mem_raw_of_box k (1) ((0) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((3), (0)) = -((0)) := by
    rw [incr_vert k 1 (3) (0) (Or.inl rfl) (mem_raw_of_box k (3) (0) (by omega)) (mem_raw_of_box k (3) ((0) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((0), (1)) = -((1)) := by
    rw [incr_vert k 1 (0) (1) (Or.inl rfl) (mem_raw_of_box k (0) (1) (by omega)) (mem_raw_of_box k (0) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((2), (1)) = -((1)) := by
    rw [incr_vert k 1 (2) (1) (Or.inl rfl) (mem_raw_of_box k (2) (1) (by omega)) (mem_raw_of_box k (2) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_1_1_p_mx (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (-1, 0) ((1), (1)) ≤ incr (reciprocalField k) (-1, 0) ((-1), (1)) ∧
    incr (reciprocalField k) (-1, 0) ((1), (1)) - incr (reciprocalField k) (-1, 0) ((0), (2)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((1), (1)) - incr (reciprocalField k) (-1, 0) ((-2), (2)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (-1, 0) ((-1), (1)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 1), (2)) :=
    incr_eq_U k (-1, 0) ((-1), (1)) (((2 * (k : ℤ) + 3) - 1), (2)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (-1, 0) ((-2), (2)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 2), (3)) :=
    incr_eq_U k (-1, 0) ((-2), (2)) (((2 * (k : ℤ) + 3) - 2), (3)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (-1, 0) ((1), (1)) = min ((1) + (-1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (1) (1) (mem_raw_of_box k ((1) + (-1)) (1) (by omega)) (mem_raw_of_box k (1) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (1) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (-1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (1) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 1), (2)) = min (((2 * (k : ℤ) + 3) - 1) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 1) (2) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 1) + (-1)) (2) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (2) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 1) + (-1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (2) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((0), (2)) = min ((0) + (-1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (0) (2) (mem_raw_of_box k ((0) + (-1)) (2) (by omega)) (mem_raw_of_box k (0) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (2) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (-1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (2) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 2), (3)) = min (((2 * (k : ℤ) + 3) - 2) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 2) (3) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 2) + (-1)) (3) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (3) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 2) + (-1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (3) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_1_1_p_px (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (1, 0) ((1), (1)) ≤ incr (reciprocalField k) (1, 0) ((-1), (1)) ∧
    incr (reciprocalField k) (1, 0) ((1), (1)) - incr (reciprocalField k) (1, 0) ((0), (2)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((1), (1)) - incr (reciprocalField k) (1, 0) ((-2), (2)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (1, 0) ((-1), (1)) = incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 1), (2)) :=
    incr_eq_U k (1, 0) ((-1), (1)) (((2 * (k : ℤ) + 3) - 1), (2)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (1, 0) ((-2), (2)) = incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (3)) :=
    incr_eq_U k (1, 0) ((-2), (2)) (((2 * (k : ℤ) + 3) - 2), (3)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (1, 0) ((1), (1)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (1) (mem_raw_of_box k ((1) + (1)) (1) (by omega)) (mem_raw_of_box k (1) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (1) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 1), (2)) = min (((2 * (k : ℤ) + 3) - 1) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 1) (2) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 1) + (1)) (2) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 1) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (2) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((0), (2)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (2) (mem_raw_of_box k ((0) + (1)) (2) (by omega)) (mem_raw_of_box k (0) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (2) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (3)) = min (((2 * (k : ℤ) + 3) - 2) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 2) (3) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 2) + (1)) (3) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 2) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (3) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_1_1_m_mx (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (-1, 0) ((1), (1)) ≤ incr (reciprocalField k) (-1, 0) ((3), (1)) ∧
    incr (reciprocalField k) (-1, 0) ((1), (1)) - incr (reciprocalField k) (-1, 0) ((0), (2)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((1), (1)) - incr (reciprocalField k) (-1, 0) ((2), (2)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (-1, 0) ((1), (1)) = min ((1) + (-1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (1) (1) (mem_raw_of_box k ((1) + (-1)) (1) (by omega)) (mem_raw_of_box k (1) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (1) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (-1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (1) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) ((3), (1)) = min ((3) + (-1) - 1) 0 - min ((3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (3) (1) (mem_raw_of_box k ((3) + (-1)) (1) (by omega)) (mem_raw_of_box k (3) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3) (1) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((3) + (-1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3) (1) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((0), (2)) = min ((0) + (-1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (0) (2) (mem_raw_of_box k ((0) + (-1)) (2) (by omega)) (mem_raw_of_box k (0) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (2) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (-1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (2) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) ((2), (2)) = min ((2) + (-1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (2) (2) (mem_raw_of_box k ((2) + (-1)) (2) (by omega)) (mem_raw_of_box k (2) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (2) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (-1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (2) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_1_1_m_px (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (1, 0) ((1), (1)) ≤ incr (reciprocalField k) (1, 0) ((3), (1)) ∧
    incr (reciprocalField k) (1, 0) ((1), (1)) - incr (reciprocalField k) (1, 0) ((0), (2)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((1), (1)) - incr (reciprocalField k) (1, 0) ((2), (2)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (1, 0) ((3), (1)) = incr (reciprocalField k) (1, 0) ((3 - (2 * (k : ℤ) + 3)), (0)) :=
    (incr_eq_U k (1, 0) ((3 - (2 * (k : ℤ) + 3)), (0)) ((3), (1)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (1, 0) ((1), (1)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (1) (mem_raw_of_box k ((1) + (1)) (1) (by omega)) (mem_raw_of_box k (1) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (1) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((3 - (2 * (k : ℤ) + 3)), (0)) = min ((3 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((3 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) (3 - (2 * (k : ℤ) + 3)) (0) (mem_raw_of_box k ((3 - (2 * (k : ℤ) + 3)) + (1)) (0) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3 - (2 * (k : ℤ) + 3)) + (1)) (0) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (0) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((0), (2)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (2) (mem_raw_of_box k ((0) + (1)) (2) (by omega)) (mem_raw_of_box k (0) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (2) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((2), (2)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (2) (mem_raw_of_box k ((2) + (1)) (2) (by omega)) (mem_raw_of_box k (2) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (2) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_1_2_p_my (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, -1) ((1), (2)) ≤ incr (reciprocalField k) (0, -1) ((-1), (2)) ∧
    incr (reciprocalField k) (0, -1) ((1), (2)) - incr (reciprocalField k) (0, -1) ((0), (3)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((1), (2)) - incr (reciprocalField k) (0, -1) ((-2), (3)) ≤ -1 := by
  have hZ2_0 : incr (reciprocalField k) (0, -1) ((-1), (2)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 1), (3)) :=
    incr_eq_U k (0, -1) ((-1), (2)) (((2 * (k : ℤ) + 3) - 1), (3)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, -1) ((-2), (3)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (4)) :=
    incr_eq_U k (0, -1) ((-2), (3)) (((2 * (k : ℤ) + 3) - 2), (4)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, -1) ((1), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (1) (2) (Or.inr rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 1), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 1) (3) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (3) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((0), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (0) (3) (Or.inr rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 2) (4) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (4) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_1_2_p_py (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, 1) ((1), (2)) ≤ incr (reciprocalField k) (0, 1) ((-1), (2)) ∧
    incr (reciprocalField k) (0, 1) ((1), (2)) - incr (reciprocalField k) (0, 1) ((0), (3)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((1), (2)) - incr (reciprocalField k) (0, 1) ((-2), (3)) ≤ 1 := by
  have hZ4_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 3), (2 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-2), (3)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 3), (2 - (2 * (k : ℤ) + 3))) ((-2), (3)) (by ext <;> (simp; try ring))
  have hZ4_1 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 3), (2 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((2 * (2 * (k : ℤ) + 3) + -3), (3 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (0, 1) (((2 * (k : ℤ) + 3) - 3), (2 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -3), (3 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, 1) ((1), (2)) = -((2)) := by
    rw [incr_vert k 1 (1) (2) (Or.inl rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((-1), (2)) = -((2)) := by
    rw [incr_vert k 1 (-1) (2) (Or.inl rfl) (mem_raw_of_box k (-1) (2) (by omega)) (mem_raw_of_box k (-1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((0), (3)) = -((3)) := by
    rw [incr_vert k 1 (0) (3) (Or.inl rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((2 * (2 * (k : ℤ) + 3) + -3), (3 - (2 * (k : ℤ) + 3))) = -((3 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 (2 * (2 * (k : ℤ) + 3) + -3) (3 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -3) (3 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -3) ((3 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_1_2_m_my (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, -1) ((1), (2)) ≤ incr (reciprocalField k) (0, -1) ((3), (2)) ∧
    incr (reciprocalField k) (0, -1) ((1), (2)) - incr (reciprocalField k) (0, -1) ((0), (3)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((1), (2)) - incr (reciprocalField k) (0, -1) ((2), (3)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((1), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (1) (2) (Or.inr rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((3), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (3) (2) (Or.inr rfl) (mem_raw_of_box k (3) (2) (by omega)) (mem_raw_of_box k (3) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((0), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (0) (3) (Or.inr rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((2), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (2) (3) (Or.inr rfl) (mem_raw_of_box k (2) (3) (by omega)) (mem_raw_of_box k (2) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_1_2_m_py (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, 1) ((1), (2)) ≤ incr (reciprocalField k) (0, 1) ((3), (2)) ∧
    incr (reciprocalField k) (0, 1) ((1), (2)) - incr (reciprocalField k) (0, 1) ((0), (3)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((1), (2)) - incr (reciprocalField k) (0, 1) ((2), (3)) ≤ 1 := by
  have hZ2_0 : incr (reciprocalField k) (0, 1) ((3), (2)) = incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (1)) :=
    (incr_eq_U k (0, 1) ((3 - (2 * (k : ℤ) + 3)), (1)) ((3), (2)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (0, 1) ((1), (2)) = -((2)) := by
    rw [incr_vert k 1 (1) (2) (Or.inl rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (1)) = -((1)) := by
    rw [incr_vert k 1 (3 - (2 * (k : ℤ) + 3)) (1) (Or.inl rfl) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) (1) (by omega)) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((0), (3)) = -((3)) := by
    rw [incr_vert k 1 (0) (3) (Or.inl rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((2), (3)) = 1 - (2 * (k : ℤ) + 3) := by
    rw [show ((2), (3)) = ((2 : ℤ), 2 * (k : ℤ) + 3) from by ext <;> omega]
    exact incr_c2low_up k
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_1_3_p_mx (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (-1, 0) ((1), (3)) ≤ incr (reciprocalField k) (-1, 0) ((-1), (3)) ∧
    incr (reciprocalField k) (-1, 0) ((1), (3)) - incr (reciprocalField k) (-1, 0) ((0), (4)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((1), (3)) - incr (reciprocalField k) (-1, 0) ((-2), (4)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (-1, 0) ((-1), (3)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 1), (4)) :=
    incr_eq_U k (-1, 0) ((-1), (3)) (((2 * (k : ℤ) + 3) - 1), (4)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 3), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (-1, 0) ((-2), (4)) + ((2 * (k : ℤ) + 3) * 0 - -1) :=
    incr_eq_T k (-1, 0) (((2 * (k : ℤ) + 3) - 3), (3 - (2 * (k : ℤ) + 3))) ((-2), (4)) (by ext <;> (simp; try ring))
  have hZ4_1 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 3), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (-1, 0) ((2 * (2 * (k : ℤ) + 3) + -3), (4 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (-1, 0) (((2 * (k : ℤ) + 3) - 3), (3 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -3), (4 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (-1, 0) ((1), (3)) = min ((1) + (-1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (1) (3) (mem_raw_of_box k ((1) + (-1)) (3) (by omega)) (mem_raw_of_box k (1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (3) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (-1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (3) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 1), (4)) = min (((2 * (k : ℤ) + 3) - 1) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 1) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 1) (4) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 1) + (-1)) (4) (by omega)) (mem_raw_corner2' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 1) + (-1)) (4) (by omega)) (corner_yes (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (4) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((0), (4)) = min ((0) + (-1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (0) (4) (mem_raw_of_box k ((0) + (-1)) (4) (by omega)) (mem_raw_of_box k (0) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (4) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) ((2 * (2 * (k : ℤ) + 3) + -3), (4 - (2 * (k : ℤ) + 3))) = min ((2 * (2 * (k : ℤ) + 3) + -3) + (-1) - 1) 0 - min ((2 * (2 * (k : ℤ) + 3) + -3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (2 * (2 * (k : ℤ) + 3) + -3) (4 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k ((2 * (2 * (k : ℤ) + 3) + -3) + (-1)) (4 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -3) (4 - (2 * (k : ℤ) + 3)) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2 * (2 * (k : ℤ) + 3) + -3) (4 - (2 * (k : ℤ) + 3)) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (2 * (k : ℤ) + 3) + -3) + (-1)) (4 - (2 * (k : ℤ) + 3)) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2 * (2 * (k : ℤ) + 3) + -3) (4 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_1_3_p_px (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (1, 0) ((1), (3)) ≤ incr (reciprocalField k) (1, 0) ((-1), (3)) ∧
    incr (reciprocalField k) (1, 0) ((1), (3)) - incr (reciprocalField k) (1, 0) ((0), (4)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((1), (3)) - incr (reciprocalField k) (1, 0) ((-2), (4)) ≤ 0 := by
  have hZ4_0 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 3), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((-2), (4)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) (((2 * (k : ℤ) + 3) - 3), (3 - (2 * (k : ℤ) + 3))) ((-2), (4)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (1, 0) ((1), (3)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (3) (mem_raw_of_box k ((1) + (1)) (3) (by omega)) (mem_raw_of_box k (1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (3) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((-1), (3)) = min ((-1) + (1) - 1) 0 - min ((-1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (-1) (3) (mem_raw_of_box k ((-1) + (1)) (3) (by omega)) (mem_raw_of_box k (-1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-1) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((-1) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-1) (3) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((0), (4)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (4) (mem_raw_of_box k ((0) + (1)) (4) (by omega)) (mem_raw_of_box k (0) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (4) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (4) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 3), (3 - (2 * (k : ℤ) + 3))) = min (((2 * (k : ℤ) + 3) - 3) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 3) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 3) (3 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 3) + (1)) (3 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (3 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 3) + (1)) (3 - (2 * (k : ℤ) + 3)) (by omega)) (corner_yes (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (3 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_1_3_m_mx (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (-1, 0) ((1), (3)) ≤ incr (reciprocalField k) (-1, 0) ((3), (3)) ∧
    incr (reciprocalField k) (-1, 0) ((1), (3)) - incr (reciprocalField k) (-1, 0) ((0), (4)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((1), (3)) - incr (reciprocalField k) (-1, 0) ((2), (4)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (-1, 0) ((3), (3)) = incr (reciprocalField k) (-1, 0) ((3 - (2 * (k : ℤ) + 3)), (2)) :=
    (incr_eq_U k (-1, 0) ((3 - (2 * (k : ℤ) + 3)), (2)) ((3), (3)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (-1, 0) ((1), (3)) = min ((1) + (-1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (1) (3) (mem_raw_of_box k ((1) + (-1)) (3) (by omega)) (mem_raw_of_box k (1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (3) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (-1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (3) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) ((3 - (2 * (k : ℤ) + 3)), (2)) = min ((3 - (2 * (k : ℤ) + 3)) + (-1) - 1) 0 - min ((3 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (3 - (2 * (k : ℤ) + 3)) (2) (mem_raw_of_box k ((3 - (2 * (k : ℤ) + 3)) + (-1)) (2) (by omega)) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (2) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((3 - (2 * (k : ℤ) + 3)) + (-1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (2) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((0), (4)) = min ((0) + (-1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (0) (4) (mem_raw_of_box k ((0) + (-1)) (4) (by omega)) (mem_raw_of_box k (0) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (4) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) ((2), (4)) = min ((2) + (-1) - 1) 0 - min ((2) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (-1) (2) (4) (mem_raw_of_box k ((2) + (-1)) (4) (by omega)) (mem_raw_corner2' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (2) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (-1)) (4) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (2) (4) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_1_3_m_px (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (1, 0) ((1), (3)) ≤ incr (reciprocalField k) (1, 0) ((3), (3)) ∧
    incr (reciprocalField k) (1, 0) ((1), (3)) - incr (reciprocalField k) (1, 0) ((0), (4)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((1), (3)) - incr (reciprocalField k) (1, 0) ((2), (4)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (1, 0) ((3), (3)) = incr (reciprocalField k) (1, 0) ((3 - (2 * (k : ℤ) + 3)), (2)) :=
    (incr_eq_U k (1, 0) ((3 - (2 * (k : ℤ) + 3)), (2)) ((3), (3)) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (1, 0) ((2), (4)) = incr (reciprocalField k) (1, 0) ((2 - (2 * (k : ℤ) + 3)), (3)) :=
    (incr_eq_U k (1, 0) ((2 - (2 * (k : ℤ) + 3)), (3)) ((2), (4)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (1, 0) ((1), (3)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (3) (mem_raw_of_box k ((1) + (1)) (3) (by omega)) (mem_raw_of_box k (1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (3) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((3 - (2 * (k : ℤ) + 3)), (2)) = min ((3 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((3 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (3 - (2 * (k : ℤ) + 3)) (2) (mem_raw_of_box k ((3 - (2 * (k : ℤ) + 3)) + (1)) (2) (by omega)) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3 - (2 * (k : ℤ) + 3)) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (2) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((0), (4)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (4) (mem_raw_of_box k ((0) + (1)) (4) (by omega)) (mem_raw_of_box k (0) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (4) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (4) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((2 - (2 * (k : ℤ) + 3)), (3)) = min ((2 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((2 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2 - (2 * (k : ℤ) + 3)) (3) (mem_raw_of_box k ((2 - (2 * (k : ℤ) + 3)) + (1)) (3) (by omega)) (mem_raw_of_box k (2 - (2 * (k : ℤ) + 3)) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2 - (2 * (k : ℤ) + 3)) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2 - (2 * (k : ℤ) + 3)) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2 - (2 * (k : ℤ) + 3)) (3) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_1_4_p_py (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, 1) ((1), (4)) ≤ incr (reciprocalField k) (0, 1) ((-1), (4)) ∧
    incr (reciprocalField k) (0, 1) ((1), (4)) - incr (reciprocalField k) (0, 1) ((0), (5)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((1), (4)) - incr (reciprocalField k) (0, 1) ((-2), (5)) ≤ 1 := by
  have hZ1_0 : incr (reciprocalField k) (0, 1) ((2 * (k : ℤ) + 3), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((1), (4)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) ((2 * (k : ℤ) + 3), (3 - (2 * (k : ℤ) + 3))) ((1), (4)) (by ext <;> (simp; try ring))
  have hZ2_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-1), (4)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 2), (3 - (2 * (k : ℤ) + 3))) ((-1), (4)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 1), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((0), (5)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 1), (4 - (2 * (k : ℤ) + 3))) ((0), (5)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 3), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-2), (5)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 3), (4 - (2 * (k : ℤ) + 3))) ((-2), (5)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, 1) ((2 * (k : ℤ) + 3), (3 - (2 * (k : ℤ) + 3))) = -((3 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (k : ℤ) + 3) ((3 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (3 - (2 * (k : ℤ) + 3))) = -((3 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 2) (3 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (3 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((3 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 1), (4 - (2 * (k : ℤ) + 3))) = -((4 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 1) (4 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (4 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) ((4 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 3), (4 - (2 * (k : ℤ) + 3))) = -((4 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 3) (4 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) (4 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) ((4 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_1_4_m_py (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, 1) ((1), (4)) ≤ incr (reciprocalField k) (0, 1) ((3), (4)) ∧
    incr (reciprocalField k) (0, 1) ((1), (4)) - incr (reciprocalField k) (0, 1) ((0), (5)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((1), (4)) - incr (reciprocalField k) (0, 1) ((2), (5)) ≤ 1 := by
  have hZ1_0 : incr (reciprocalField k) (0, 1) ((2 * (k : ℤ) + 3), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((1), (4)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) ((2 * (k : ℤ) + 3), (3 - (2 * (k : ℤ) + 3))) ((1), (4)) (by ext <;> (simp; try ring))
  have hZ2_0 : incr (reciprocalField k) (0, 1) ((3), (4)) = incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (3)) :=
    (incr_eq_U k (0, 1) ((3 - (2 * (k : ℤ) + 3)), (3)) ((3), (4)) (by ext <;> (simp; try ring))).symm
  have hZ3_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 1), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((0), (5)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 1), (4 - (2 * (k : ℤ) + 3))) ((0), (5)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) + 1), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((2), (5)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) + 1), (4 - (2 * (k : ℤ) + 3))) ((2), (5)) (by ext <;> (simp; try ring))
  have hZ4_1 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) + 1), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((1), (3 - (2 * (k : ℤ) + 3))) :=
    (incr_eq_U k (0, 1) ((1), (3 - (2 * (k : ℤ) + 3))) (((2 * (k : ℤ) + 3) + 1), (4 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (0, 1) ((2 * (k : ℤ) + 3), (3 - (2 * (k : ℤ) + 3))) = -((3 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (k : ℤ) + 3) ((3 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (3)) = -((3)) := by
    rw [incr_vert k 1 (3 - (2 * (k : ℤ) + 3)) (3) (Or.inl rfl) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) (3) (by omega)) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 1), (4 - (2 * (k : ℤ) + 3))) = -((4 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 1) (4 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (4 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) ((4 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((1), (3 - (2 * (k : ℤ) + 3))) = -((3 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 (1) (3 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k (1) (3 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (1) ((3 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_2_0_p_px (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (1, 0) ((2), (0)) ≤ incr (reciprocalField k) (1, 0) ((0), (0)) ∧
    incr (reciprocalField k) (1, 0) ((2), (0)) - incr (reciprocalField k) (1, 0) ((1), (1)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((2), (0)) - incr (reciprocalField k) (1, 0) ((-1), (1)) ≤ 0 := by
  have hZ4_0 : incr (reciprocalField k) (1, 0) ((-1), (1)) = incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 1), (2)) :=
    incr_eq_U k (1, 0) ((-1), (1)) (((2 * (k : ℤ) + 3) - 1), (2)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (1, 0) ((2), (0)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (0) (mem_raw_of_box k ((2) + (1)) (0) (by omega)) (mem_raw_of_box k (2) (0) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (0) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (0) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((0), (0)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) (0) (0) (mem_raw_of_box k ((0) + (1)) (0) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (0) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (0) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (0) (0) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((1), (1)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (1) (mem_raw_of_box k ((1) + (1)) (1) (by omega)) (mem_raw_of_box k (1) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (1) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 1), (2)) = min (((2 * (k : ℤ) + 3) - 1) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 1) (2) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 1) + (1)) (2) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 1) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (2) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_2_0_m_px (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (1, 0) ((2), (0)) ≤ incr (reciprocalField k) (1, 0) ((4), (0)) ∧
    incr (reciprocalField k) (1, 0) ((2), (0)) - incr (reciprocalField k) (1, 0) ((1), (1)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((2), (0)) - incr (reciprocalField k) (1, 0) ((3), (1)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (1, 0) ((4), (0)) = incr (reciprocalField k) (1, 0) ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) ((4), (0)) ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) (by ext <;> (simp; try ring))
  have hZ2_1 : incr (reciprocalField k) (1, 0) ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) = incr (reciprocalField k) (1, 0) ((-2 * (2 * (k : ℤ) + 3) + 5), (2 * (k : ℤ) + 3)) :=
    (incr_eq_U k (1, 0) ((-2 * (2 * (k : ℤ) + 3) + 5), (2 * (k : ℤ) + 3)) ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (1, 0) ((3), (1)) = incr (reciprocalField k) (1, 0) ((3 - (2 * (k : ℤ) + 3)), (0)) :=
    (incr_eq_U k (1, 0) ((3 - (2 * (k : ℤ) + 3)), (0)) ((3), (1)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (1, 0) ((2), (0)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (0) (mem_raw_of_box k ((2) + (1)) (0) (by omega)) (mem_raw_of_box k (2) (0) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (0) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (0) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((-2 * (2 * (k : ℤ) + 3) + 5), (2 * (k : ℤ) + 3)) = min ((-2 * (2 * (k : ℤ) + 3) + 5) + (1) - 1) 0 - min ((-2 * (2 * (k : ℤ) + 3) + 5) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (-2 * (2 * (k : ℤ) + 3) + 5) (2 * (k : ℤ) + 3) (mem_raw_of_box k ((-2 * (2 * (k : ℤ) + 3) + 5) + (1)) (2 * (k : ℤ) + 3) (by omega)) (mem_raw_of_box k (-2 * (2 * (k : ℤ) + 3) + 5) (2 * (k : ℤ) + 3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-2 * (2 * (k : ℤ) + 3) + 5) (2 * (k : ℤ) + 3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((-2 * (2 * (k : ℤ) + 3) + 5) + (1)) (2 * (k : ℤ) + 3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-2 * (2 * (k : ℤ) + 3) + 5) (2 * (k : ℤ) + 3) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((1), (1)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (1) (mem_raw_of_box k ((1) + (1)) (1) (by omega)) (mem_raw_of_box k (1) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (1) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((3 - (2 * (k : ℤ) + 3)), (0)) = min ((3 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((3 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) (3 - (2 * (k : ℤ) + 3)) (0) (mem_raw_of_box k ((3 - (2 * (k : ℤ) + 3)) + (1)) (0) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3 - (2 * (k : ℤ) + 3)) + (1)) (0) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (0) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_2_1_p_my (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, -1) ((2), (1)) ≤ incr (reciprocalField k) (0, -1) ((0), (1)) ∧
    incr (reciprocalField k) (0, -1) ((2), (1)) - incr (reciprocalField k) (0, -1) ((1), (2)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((2), (1)) - incr (reciprocalField k) (0, -1) ((-1), (2)) ≤ -1 := by
  have hZ4_0 : incr (reciprocalField k) (0, -1) ((-1), (2)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 1), (3)) :=
    incr_eq_U k (0, -1) ((-1), (2)) (((2 * (k : ℤ) + 3) - 1), (3)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, -1) ((2), (1)) = ((1)) + -1 := by
    rw [incr_vert k (-1) (2) (1) (Or.inr rfl) (mem_raw_of_box k (2) (1) (by omega)) (mem_raw_of_box k (2) ((1) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((0), (1)) = 1 := by
    rw [show ((0), (1)) = ((0 : ℤ), (1 : ℤ)) from by ext <;> omega]
    exact incr_c0_fromdown k
  have vZ3 : incr (reciprocalField k) (0, -1) ((1), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (1) (2) (Or.inr rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 1), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 1) (3) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (3) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_2_1_p_py (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, 1) ((2), (1)) ≤ incr (reciprocalField k) (0, 1) ((0), (1)) ∧
    incr (reciprocalField k) (0, 1) ((2), (1)) - incr (reciprocalField k) (0, 1) ((1), (2)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((2), (1)) - incr (reciprocalField k) (0, 1) ((-1), (2)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((2), (1)) = -((1)) := by
    rw [incr_vert k 1 (2) (1) (Or.inl rfl) (mem_raw_of_box k (2) (1) (by omega)) (mem_raw_of_box k (2) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((0), (1)) = -((1)) := by
    rw [incr_vert k 1 (0) (1) (Or.inl rfl) (mem_raw_of_box k (0) (1) (by omega)) (mem_raw_of_box k (0) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((1), (2)) = -((2)) := by
    rw [incr_vert k 1 (1) (2) (Or.inl rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((-1), (2)) = -((2)) := by
    rw [incr_vert k 1 (-1) (2) (Or.inl rfl) (mem_raw_of_box k (-1) (2) (by omega)) (mem_raw_of_box k (-1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_2_1_m_my (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, -1) ((2), (1)) ≤ incr (reciprocalField k) (0, -1) ((4), (1)) ∧
    incr (reciprocalField k) (0, -1) ((2), (1)) - incr (reciprocalField k) (0, -1) ((1), (2)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((2), (1)) - incr (reciprocalField k) (0, -1) ((3), (2)) ≤ -1 := by
  have hZ2_0 : incr (reciprocalField k) (0, -1) ((4), (1)) = incr (reciprocalField k) (0, -1) ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 2)) + ((2 * (k : ℤ) + 3) * -1 - 0) :=
    incr_eq_T k (0, -1) ((4), (1)) ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 2)) (by ext <;> (simp; try ring))
  have hZ2_1 : incr (reciprocalField k) (0, -1) ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 2)) = incr (reciprocalField k) (0, -1) ((-2 * (2 * (k : ℤ) + 3) + 5), ((2 * (k : ℤ) + 3) + 1)) :=
    (incr_eq_U k (0, -1) ((-2 * (2 * (k : ℤ) + 3) + 5), ((2 * (k : ℤ) + 3) + 1)) ((5 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 2)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (0, -1) ((2), (1)) = ((1)) + -1 := by
    rw [incr_vert k (-1) (2) (1) (Or.inr rfl) (mem_raw_of_box k (2) (1) (by omega)) (mem_raw_of_box k (2) ((1) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((-2 * (2 * (k : ℤ) + 3) + 5), ((2 * (k : ℤ) + 3) + 1)) = (((2 * (k : ℤ) + 3) + 1)) + -1 := by
    rw [incr_vert k (-1) (-2 * (2 * (k : ℤ) + 3) + 5) ((2 * (k : ℤ) + 3) + 1) (Or.inr rfl) (mem_raw_of_box k (-2 * (2 * (k : ℤ) + 3) + 5) ((2 * (k : ℤ) + 3) + 1) (by omega)) (mem_raw_of_box k (-2 * (2 * (k : ℤ) + 3) + 5) (((2 * (k : ℤ) + 3) + 1) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((1), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (1) (2) (Or.inr rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((3), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (3) (2) (Or.inr rfl) (mem_raw_of_box k (3) (2) (by omega)) (mem_raw_of_box k (3) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_2_1_m_py (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, 1) ((2), (1)) ≤ incr (reciprocalField k) (0, 1) ((4), (1)) ∧
    incr (reciprocalField k) (0, 1) ((2), (1)) - incr (reciprocalField k) (0, 1) ((1), (2)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((2), (1)) - incr (reciprocalField k) (0, 1) ((3), (2)) ≤ 1 := by
  have hZ2_0 : incr (reciprocalField k) (0, 1) ((4), (1)) = incr (reciprocalField k) (0, 1) ((4 - (2 * (k : ℤ) + 3)), (0)) :=
    (incr_eq_U k (0, 1) ((4 - (2 * (k : ℤ) + 3)), (0)) ((4), (1)) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (0, 1) ((3), (2)) = incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (1)) :=
    (incr_eq_U k (0, 1) ((3 - (2 * (k : ℤ) + 3)), (1)) ((3), (2)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (0, 1) ((2), (1)) = -((1)) := by
    rw [incr_vert k 1 (2) (1) (Or.inl rfl) (mem_raw_of_box k (2) (1) (by omega)) (mem_raw_of_box k (2) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((4 - (2 * (k : ℤ) + 3)), (0)) = -((0)) := by
    rw [incr_vert k 1 (4 - (2 * (k : ℤ) + 3)) (0) (Or.inl rfl) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) (0) (by omega)) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) ((0) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((1), (2)) = -((2)) := by
    rw [incr_vert k 1 (1) (2) (Or.inl rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (1)) = -((1)) := by
    rw [incr_vert k 1 (3 - (2 * (k : ℤ) + 3)) (1) (Or.inl rfl) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) (1) (by omega)) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_2_2_p_px (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (1, 0) ((2), (2)) ≤ incr (reciprocalField k) (1, 0) ((0), (2)) ∧
    incr (reciprocalField k) (1, 0) ((2), (2)) - incr (reciprocalField k) (1, 0) ((1), (3)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((2), (2)) - incr (reciprocalField k) (1, 0) ((-1), (3)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (1, 0) ((2), (2)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (2) (mem_raw_of_box k ((2) + (1)) (2) (by omega)) (mem_raw_of_box k (2) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (2) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((0), (2)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (2) (mem_raw_of_box k ((0) + (1)) (2) (by omega)) (mem_raw_of_box k (0) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (2) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((1), (3)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (3) (mem_raw_of_box k ((1) + (1)) (3) (by omega)) (mem_raw_of_box k (1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (3) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((-1), (3)) = min ((-1) + (1) - 1) 0 - min ((-1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (-1) (3) (mem_raw_of_box k ((-1) + (1)) (3) (by omega)) (mem_raw_of_box k (-1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-1) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((-1) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-1) (3) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_2_2_m_px (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (1, 0) ((2), (2)) ≤ incr (reciprocalField k) (1, 0) ((4), (2)) ∧
    incr (reciprocalField k) (1, 0) ((2), (2)) - incr (reciprocalField k) (1, 0) ((1), (3)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((2), (2)) - incr (reciprocalField k) (1, 0) ((3), (3)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (1, 0) ((4), (2)) = incr (reciprocalField k) (1, 0) ((4 - (2 * (k : ℤ) + 3)), (1)) :=
    (incr_eq_U k (1, 0) ((4 - (2 * (k : ℤ) + 3)), (1)) ((4), (2)) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (1, 0) ((3), (3)) = incr (reciprocalField k) (1, 0) ((3 - (2 * (k : ℤ) + 3)), (2)) :=
    (incr_eq_U k (1, 0) ((3 - (2 * (k : ℤ) + 3)), (2)) ((3), (3)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (1, 0) ((2), (2)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (2) (mem_raw_of_box k ((2) + (1)) (2) (by omega)) (mem_raw_of_box k (2) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (2) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((4 - (2 * (k : ℤ) + 3)), (1)) = min ((4 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((4 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (4 - (2 * (k : ℤ) + 3)) (1) (mem_raw_of_box k ((4 - (2 * (k : ℤ) + 3)) + (1)) (1) (by omega)) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (4 - (2 * (k : ℤ) + 3)) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((4 - (2 * (k : ℤ) + 3)) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (4 - (2 * (k : ℤ) + 3)) (1) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((1), (3)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (3) (mem_raw_of_box k ((1) + (1)) (3) (by omega)) (mem_raw_of_box k (1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (3) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((3 - (2 * (k : ℤ) + 3)), (2)) = min ((3 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((3 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (3 - (2 * (k : ℤ) + 3)) (2) (mem_raw_of_box k ((3 - (2 * (k : ℤ) + 3)) + (1)) (2) (by omega)) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3 - (2 * (k : ℤ) + 3)) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (2) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_2_3_p_my (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, -1) ((2), (3)) ≤ incr (reciprocalField k) (0, -1) ((0), (3)) ∧
    incr (reciprocalField k) (0, -1) ((2), (3)) - incr (reciprocalField k) (0, -1) ((1), (4)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((2), (3)) - incr (reciprocalField k) (0, -1) ((-1), (4)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((2), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (2) (3) (Or.inr rfl) (mem_raw_of_box k (2) (3) (by omega)) (mem_raw_of_box k (2) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((0), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (0) (3) (Or.inr rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((1), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (1) (4) (Or.inr rfl) (mem_raw_of_box k (1) (4) (by omega)) (mem_raw_of_box k (1) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((-1), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (-1) (4) (Or.inr rfl) (mem_raw_of_box k (-1) (4) (by omega)) (mem_raw_of_box k (-1) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_2_3_m_py (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, 1) ((2), (3)) ≤ incr (reciprocalField k) (0, 1) ((4), (3)) ∧
    incr (reciprocalField k) (0, 1) ((2), (3)) - incr (reciprocalField k) (0, 1) ((1), (4)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((2), (3)) - incr (reciprocalField k) (0, 1) ((3), (4)) ≤ 1 := by
  have hZ2_0 : incr (reciprocalField k) (0, 1) ((4), (3)) = incr (reciprocalField k) (0, 1) ((4 - (2 * (k : ℤ) + 3)), (2)) :=
    (incr_eq_U k (0, 1) ((4 - (2 * (k : ℤ) + 3)), (2)) ((4), (3)) (by ext <;> (simp; try ring))).symm
  have hZ3_0 : incr (reciprocalField k) (0, 1) ((2 * (k : ℤ) + 3), (3 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((1), (4)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) ((2 * (k : ℤ) + 3), (3 - (2 * (k : ℤ) + 3))) ((1), (4)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, 1) ((3), (4)) = incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (3)) :=
    (incr_eq_U k (0, 1) ((3 - (2 * (k : ℤ) + 3)), (3)) ((3), (4)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (0, 1) ((2), (3)) = 1 - (2 * (k : ℤ) + 3) := by
    rw [show ((2), (3)) = ((2 : ℤ), 2 * (k : ℤ) + 3) from by ext <;> omega]
    exact incr_c2low_up k
  have vZ2 : incr (reciprocalField k) (0, 1) ((4 - (2 * (k : ℤ) + 3)), (2)) = -((2)) := by
    rw [incr_vert k 1 (4 - (2 * (k : ℤ) + 3)) (2) (Or.inl rfl) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) (2) (by omega)) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((2 * (k : ℤ) + 3), (3 - (2 * (k : ℤ) + 3))) = -((3 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (k : ℤ) + 3) ((3 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (3)) = -((3)) := by
    rw [incr_vert k 1 (3 - (2 * (k : ℤ) + 3)) (3) (Or.inl rfl) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) (3) (by omega)) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_2_4_p_px (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (1, 0) ((2), (4)) ≤ incr (reciprocalField k) (1, 0) ((0), (4)) ∧
    incr (reciprocalField k) (1, 0) ((2), (4)) - incr (reciprocalField k) (1, 0) ((1), (5)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((2), (4)) - incr (reciprocalField k) (1, 0) ((-1), (5)) ≤ 0 := by
  have hZ1_0 : incr (reciprocalField k) (1, 0) ((2), (4)) = incr (reciprocalField k) (1, 0) ((2 - (2 * (k : ℤ) + 3)), (3)) :=
    (incr_eq_U k (1, 0) ((2 - (2 * (k : ℤ) + 3)), (3)) ((2), (4)) (by ext <;> (simp; try ring))).symm
  have hZ3_0 : incr (reciprocalField k) (1, 0) ((2 * (k : ℤ) + 3), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((1), (5)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) ((2 * (k : ℤ) + 3), (4 - (2 * (k : ℤ) + 3))) ((1), (5)) (by ext <;> (simp; try ring))
  have hZ3_1 : incr (reciprocalField k) (1, 0) ((2 * (k : ℤ) + 3), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((0), (3 - (2 * (k : ℤ) + 3))) :=
    (incr_eq_U k (1, 0) ((0), (3 - (2 * (k : ℤ) + 3))) ((2 * (k : ℤ) + 3), (4 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((-1), (5)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) (((2 * (k : ℤ) + 3) - 2), (4 - (2 * (k : ℤ) + 3))) ((-1), (5)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (1, 0) ((2 - (2 * (k : ℤ) + 3)), (3)) = min ((2 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((2 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2 - (2 * (k : ℤ) + 3)) (3) (mem_raw_of_box k ((2 - (2 * (k : ℤ) + 3)) + (1)) (3) (by omega)) (mem_raw_of_box k (2 - (2 * (k : ℤ) + 3)) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2 - (2 * (k : ℤ) + 3)) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2 - (2 * (k : ℤ) + 3)) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2 - (2 * (k : ℤ) + 3)) (3) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((0), (4)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (4) (mem_raw_of_box k ((0) + (1)) (4) (by omega)) (mem_raw_of_box k (0) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (4) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (4) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((0), (3 - (2 * (k : ℤ) + 3))) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) (0) (3 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k ((0) + (1)) (3 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (0) (3 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (3 - (2 * (k : ℤ) + 3)) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (0) (3 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (4 - (2 * (k : ℤ) + 3))) = min (((2 * (k : ℤ) + 3) - 2) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 2) (4 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 2) + (1)) (4 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (4 - (2 * (k : ℤ) + 3)) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (4 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 2) + (1)) (4 - (2 * (k : ℤ) + 3)) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (4 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_2_4_m_mx (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (-1, 0) ((2), (4)) ≤ incr (reciprocalField k) (-1, 0) ((4), (4)) ∧
    incr (reciprocalField k) (-1, 0) ((2), (4)) - incr (reciprocalField k) (-1, 0) ((1), (5)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((2), (4)) - incr (reciprocalField k) (-1, 0) ((3), (5)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (-1, 0) ((4), (4)) = incr (reciprocalField k) (-1, 0) ((4 - (2 * (k : ℤ) + 3)), (3)) :=
    (incr_eq_U k (-1, 0) ((4 - (2 * (k : ℤ) + 3)), (3)) ((4), (4)) (by ext <;> (simp; try ring))).symm
  have hZ3_0 : incr (reciprocalField k) (-1, 0) ((2 * (k : ℤ) + 3), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (-1, 0) ((1), (5)) + ((2 * (k : ℤ) + 3) * 0 - -1) :=
    incr_eq_T k (-1, 0) ((2 * (k : ℤ) + 3), (4 - (2 * (k : ℤ) + 3))) ((1), (5)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (-1, 0) ((3), (5)) = incr (reciprocalField k) (-1, 0) ((3 - (2 * (k : ℤ) + 3)), (4)) :=
    (incr_eq_U k (-1, 0) ((3 - (2 * (k : ℤ) + 3)), (4)) ((3), (5)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (-1, 0) ((2), (4)) = min ((2) + (-1) - 1) 0 - min ((2) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (-1) (2) (4) (mem_raw_of_box k ((2) + (-1)) (4) (by omega)) (mem_raw_corner2' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (2) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (-1)) (4) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (2) (4) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) ((4 - (2 * (k : ℤ) + 3)), (3)) = min ((4 - (2 * (k : ℤ) + 3)) + (-1) - 1) 0 - min ((4 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (4 - (2 * (k : ℤ) + 3)) (3) (mem_raw_of_box k ((4 - (2 * (k : ℤ) + 3)) + (-1)) (3) (by omega)) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (4 - (2 * (k : ℤ) + 3)) (3) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((4 - (2 * (k : ℤ) + 3)) + (-1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (4 - (2 * (k : ℤ) + 3)) (3) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((2 * (k : ℤ) + 3), (4 - (2 * (k : ℤ) + 3))) = min ((2 * (k : ℤ) + 3) + (-1) - 1) 0 - min ((2 * (k : ℤ) + 3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (2 * (k : ℤ) + 3) (4 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) + (-1)) (4 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (k : ℤ) + 3) (4 - (2 * (k : ℤ) + 3)) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 3) (4 - (2 * (k : ℤ) + 3)) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) + (-1)) (4 - (2 * (k : ℤ) + 3)) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 3) (4 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) ((3 - (2 * (k : ℤ) + 3)), (4)) = min ((3 - (2 * (k : ℤ) + 3)) + (-1) - 1) 0 - min ((3 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (3 - (2 * (k : ℤ) + 3)) (4) (mem_raw_of_box k ((3 - (2 * (k : ℤ) + 3)) + (-1)) (4) (by omega)) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((3 - (2 * (k : ℤ) + 3)) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (4) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_3_0_p_py (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, 1) ((3), (0)) ≤ incr (reciprocalField k) (0, 1) ((1), (0)) ∧
    incr (reciprocalField k) (0, 1) ((3), (0)) - incr (reciprocalField k) (0, 1) ((2), (1)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((3), (0)) - incr (reciprocalField k) (0, 1) ((0), (1)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((3), (0)) = -((0)) := by
    rw [incr_vert k 1 (3) (0) (Or.inl rfl) (mem_raw_of_box k (3) (0) (by omega)) (mem_raw_of_box k (3) ((0) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((1), (0)) = -((0)) := by
    rw [incr_vert k 1 (1) (0) (Or.inl rfl) (mem_raw_of_box k (1) (0) (by omega)) (mem_raw_of_box k (1) ((0) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((2), (1)) = -((1)) := by
    rw [incr_vert k 1 (2) (1) (Or.inl rfl) (mem_raw_of_box k (2) (1) (by omega)) (mem_raw_of_box k (2) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((0), (1)) = -((1)) := by
    rw [incr_vert k 1 (0) (1) (Or.inl rfl) (mem_raw_of_box k (0) (1) (by omega)) (mem_raw_of_box k (0) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_3_0_m_py (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, 1) ((3), (0)) ≤ incr (reciprocalField k) (0, 1) ((5), (0)) ∧
    incr (reciprocalField k) (0, 1) ((3), (0)) - incr (reciprocalField k) (0, 1) ((2), (1)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((3), (0)) - incr (reciprocalField k) (0, 1) ((4), (1)) ≤ 1 := by
  have hZ2_0 : incr (reciprocalField k) (0, 1) ((5), (0)) = incr (reciprocalField k) (0, 1) ((6 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) ((5), (0)) ((6 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) (by ext <;> (simp; try ring))
  have hZ2_1 : incr (reciprocalField k) (0, 1) ((6 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) = incr (reciprocalField k) (0, 1) ((-2 * (2 * (k : ℤ) + 3) + 6), (2 * (k : ℤ) + 3)) :=
    (incr_eq_U k (0, 1) ((-2 * (2 * (k : ℤ) + 3) + 6), (2 * (k : ℤ) + 3)) ((6 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (0, 1) ((4), (1)) = incr (reciprocalField k) (0, 1) ((4 - (2 * (k : ℤ) + 3)), (0)) :=
    (incr_eq_U k (0, 1) ((4 - (2 * (k : ℤ) + 3)), (0)) ((4), (1)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (0, 1) ((3), (0)) = -((0)) := by
    rw [incr_vert k 1 (3) (0) (Or.inl rfl) (mem_raw_of_box k (3) (0) (by omega)) (mem_raw_of_box k (3) ((0) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((-2 * (2 * (k : ℤ) + 3) + 6), (2 * (k : ℤ) + 3)) = -((2 * (k : ℤ) + 3)) := by
    rw [incr_vert k 1 (-2 * (2 * (k : ℤ) + 3) + 6) (2 * (k : ℤ) + 3) (Or.inl rfl) (mem_raw_of_box k (-2 * (2 * (k : ℤ) + 3) + 6) (2 * (k : ℤ) + 3) (by omega)) (mem_raw_of_box k (-2 * (2 * (k : ℤ) + 3) + 6) ((2 * (k : ℤ) + 3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((2), (1)) = -((1)) := by
    rw [incr_vert k 1 (2) (1) (Or.inl rfl) (mem_raw_of_box k (2) (1) (by omega)) (mem_raw_of_box k (2) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((4 - (2 * (k : ℤ) + 3)), (0)) = -((0)) := by
    rw [incr_vert k 1 (4 - (2 * (k : ℤ) + 3)) (0) (Or.inl rfl) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) (0) (by omega)) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) ((0) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_3_1_p_px (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (1, 0) ((3), (1)) ≤ incr (reciprocalField k) (1, 0) ((1), (1)) ∧
    incr (reciprocalField k) (1, 0) ((3), (1)) - incr (reciprocalField k) (1, 0) ((2), (2)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((3), (1)) - incr (reciprocalField k) (1, 0) ((0), (2)) ≤ 0 := by
  have hZ1_0 : incr (reciprocalField k) (1, 0) ((3), (1)) = incr (reciprocalField k) (1, 0) ((3 - (2 * (k : ℤ) + 3)), (0)) :=
    (incr_eq_U k (1, 0) ((3 - (2 * (k : ℤ) + 3)), (0)) ((3), (1)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (1, 0) ((3 - (2 * (k : ℤ) + 3)), (0)) = min ((3 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((3 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) (3 - (2 * (k : ℤ) + 3)) (0) (mem_raw_of_box k ((3 - (2 * (k : ℤ) + 3)) + (1)) (0) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3 - (2 * (k : ℤ) + 3)) + (1)) (0) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (0) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((1), (1)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (1) (mem_raw_of_box k ((1) + (1)) (1) (by omega)) (mem_raw_of_box k (1) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (1) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((2), (2)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (2) (mem_raw_of_box k ((2) + (1)) (2) (by omega)) (mem_raw_of_box k (2) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (2) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((0), (2)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (2) (mem_raw_of_box k ((0) + (1)) (2) (by omega)) (mem_raw_of_box k (0) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (2) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_3_1_m_px (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (1, 0) ((3), (1)) ≤ incr (reciprocalField k) (1, 0) ((5), (1)) ∧
    incr (reciprocalField k) (1, 0) ((3), (1)) - incr (reciprocalField k) (1, 0) ((2), (2)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((3), (1)) - incr (reciprocalField k) (1, 0) ((4), (2)) ≤ 0 := by
  have hZ1_0 : incr (reciprocalField k) (1, 0) ((3), (1)) = incr (reciprocalField k) (1, 0) ((3 - (2 * (k : ℤ) + 3)), (0)) :=
    (incr_eq_U k (1, 0) ((3 - (2 * (k : ℤ) + 3)), (0)) ((3), (1)) (by ext <;> (simp; try ring))).symm
  have hZ2_0 : incr (reciprocalField k) (1, 0) ((5), (1)) = incr (reciprocalField k) (1, 0) ((5 - (2 * (k : ℤ) + 3)), (0)) :=
    (incr_eq_U k (1, 0) ((5 - (2 * (k : ℤ) + 3)), (0)) ((5), (1)) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (1, 0) ((4), (2)) = incr (reciprocalField k) (1, 0) ((4 - (2 * (k : ℤ) + 3)), (1)) :=
    (incr_eq_U k (1, 0) ((4 - (2 * (k : ℤ) + 3)), (1)) ((4), (2)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (1, 0) ((3 - (2 * (k : ℤ) + 3)), (0)) = min ((3 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((3 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) (3 - (2 * (k : ℤ) + 3)) (0) (mem_raw_of_box k ((3 - (2 * (k : ℤ) + 3)) + (1)) (0) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3 - (2 * (k : ℤ) + 3)) + (1)) (0) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (0) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((5 - (2 * (k : ℤ) + 3)), (0)) = min ((5 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((5 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (5 - (2 * (k : ℤ) + 3)) (0) (mem_raw_of_box k ((5 - (2 * (k : ℤ) + 3)) + (1)) (0) (by omega)) (mem_raw_of_box k (5 - (2 * (k : ℤ) + 3)) (0) (by omega)), hG_nc (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((5 - (2 * (k : ℤ) + 3)) + (1)) (0) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (0) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((2), (2)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (2) (mem_raw_of_box k ((2) + (1)) (2) (by omega)) (mem_raw_of_box k (2) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (2) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((4 - (2 * (k : ℤ) + 3)), (1)) = min ((4 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((4 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (4 - (2 * (k : ℤ) + 3)) (1) (mem_raw_of_box k ((4 - (2 * (k : ℤ) + 3)) + (1)) (1) (by omega)) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (4 - (2 * (k : ℤ) + 3)) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((4 - (2 * (k : ℤ) + 3)) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (4 - (2 * (k : ℤ) + 3)) (1) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_3_2_p_my (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, -1) ((3), (2)) ≤ incr (reciprocalField k) (0, -1) ((1), (2)) ∧
    incr (reciprocalField k) (0, -1) ((3), (2)) - incr (reciprocalField k) (0, -1) ((2), (3)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((3), (2)) - incr (reciprocalField k) (0, -1) ((0), (3)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((3), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (3) (2) (Or.inr rfl) (mem_raw_of_box k (3) (2) (by omega)) (mem_raw_of_box k (3) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((1), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (1) (2) (Or.inr rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((2), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (2) (3) (Or.inr rfl) (mem_raw_of_box k (2) (3) (by omega)) (mem_raw_of_box k (2) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((0), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (0) (3) (Or.inr rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr0_3_2_m_py (k : ℕ) (hk : (k : ℤ) = 0) :
    incr (reciprocalField k) (0, 1) ((3), (2)) ≤ incr (reciprocalField k) (0, 1) ((5), (2)) ∧
    incr (reciprocalField k) (0, 1) ((3), (2)) - incr (reciprocalField k) (0, 1) ((2), (3)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((3), (2)) - incr (reciprocalField k) (0, 1) ((4), (3)) ≤ 1 := by
  have hZ1_0 : incr (reciprocalField k) (0, 1) ((3), (2)) = incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (1)) :=
    (incr_eq_U k (0, 1) ((3 - (2 * (k : ℤ) + 3)), (1)) ((3), (2)) (by ext <;> (simp; try ring))).symm
  have hZ2_0 : incr (reciprocalField k) (0, 1) ((5), (2)) = incr (reciprocalField k) (0, 1) ((5 - (2 * (k : ℤ) + 3)), (1)) :=
    (incr_eq_U k (0, 1) ((5 - (2 * (k : ℤ) + 3)), (1)) ((5), (2)) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (0, 1) ((4), (3)) = incr (reciprocalField k) (0, 1) ((4 - (2 * (k : ℤ) + 3)), (2)) :=
    (incr_eq_U k (0, 1) ((4 - (2 * (k : ℤ) + 3)), (2)) ((4), (3)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (1)) = -((1)) := by
    rw [incr_vert k 1 (3 - (2 * (k : ℤ) + 3)) (1) (Or.inl rfl) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) (1) (by omega)) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((5 - (2 * (k : ℤ) + 3)), (1)) = -((1)) := by
    rw [incr_vert k 1 (5 - (2 * (k : ℤ) + 3)) (1) (Or.inl rfl) (mem_raw_of_box k (5 - (2 * (k : ℤ) + 3)) (1) (by omega)) (mem_raw_of_box k (5 - (2 * (k : ℤ) + 3)) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((2), (3)) = 1 - (2 * (k : ℤ) + 3) := by
    rw [show ((2), (3)) = ((2 : ℤ), 2 * (k : ℤ) + 3) from by ext <;> omega]
    exact incr_c2low_up k
  have vZ4 : incr (reciprocalField k) (0, 1) ((4 - (2 * (k : ℤ) + 3)), (2)) = -((2)) := by
    rw [incr_vert k 1 (4 - (2 * (k : ℤ) + 3)) (2) (Or.inl rfl) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) (2) (by omega)) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩


theorem cov0_m1_2_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-1 : ℤ), (2 : ℤ))) (hc : ECover k (1 : ℤ) ((-1 : ℤ), (2 : ℤ)) e) :
    SE k (1 : ℤ) ((-1 : ℤ), (2 : ℤ)) e ∧ PE k ((-1 : ℤ), (2 : ℤ)) e ∧ CE k (1 : ℤ) ((-1 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((-1 : ℤ), (2 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (1 : ℤ) ((-1 : ℤ), (2 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr0_m1_2_p_my 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_m1_2_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-1 : ℤ), (2 : ℤ))) (hc : ECover k (-1 : ℤ) ((-1 : ℤ), (2 : ℤ)) e) :
    SE k (-1 : ℤ) ((-1 : ℤ), (2 : ℤ)) e ∧ PE k ((-1 : ℤ), (2 : ℤ)) e ∧ CE k (-1 : ℤ) ((-1 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((-1 : ℤ), (2 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (-1 : ℤ) ((-1 : ℤ), (2 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr0_m1_2_m_py 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_m1_3_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-1 : ℤ), (3 : ℤ))) (hc : ECover k (1 : ℤ) ((-1 : ℤ), (3 : ℤ)) e) :
    SE k (1 : ℤ) ((-1 : ℤ), (3 : ℤ)) e ∧ PE k ((-1 : ℤ), (3 : ℤ)) e ∧ CE k (1 : ℤ) ((-1 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((-1 : ℤ), (3 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (1 : ℤ) ((-1 : ℤ), (3 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_m1_3_p_px 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_m1_3_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-1 : ℤ), (3 : ℤ))) (hc : ECover k (-1 : ℤ) ((-1 : ℤ), (3 : ℤ)) e) :
    SE k (-1 : ℤ) ((-1 : ℤ), (3 : ℤ)) e ∧ PE k ((-1 : ℤ), (3 : ℤ)) e ∧ CE k (-1 : ℤ) ((-1 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((-1 : ℤ), (3 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (-1 : ℤ) ((-1 : ℤ), (3 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_m1_3_m_mx 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_m1_4_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-1 : ℤ), (4 : ℤ))) (hc : ECover k (1 : ℤ) ((-1 : ℤ), (4 : ℤ)) e) :
    SE k (1 : ℤ) ((-1 : ℤ), (4 : ℤ)) e ∧ PE k ((-1 : ℤ), (4 : ℤ)) e ∧ CE k (1 : ℤ) ((-1 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((-1 : ℤ), (4 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (1 : ℤ) ((-1 : ℤ), (4 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr0_m1_4_p_my 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_m1_4_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-1 : ℤ), (4 : ℤ))) (hc : ECover k (-1 : ℤ) ((-1 : ℤ), (4 : ℤ)) e) :
    SE k (-1 : ℤ) ((-1 : ℤ), (4 : ℤ)) e ∧ PE k ((-1 : ℤ), (4 : ℤ)) e ∧ CE k (-1 : ℤ) ((-1 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((-1 : ℤ), (4 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (-1 : ℤ) ((-1 : ℤ), (4 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr0_m1_4_m_py 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_0_0_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (0 : ℤ))) (hc : ECover k (1 : ℤ) ((0 : ℤ), (0 : ℤ)) e) :
    SE k (1 : ℤ) ((0 : ℤ), (0 : ℤ)) e ∧ PE k ((0 : ℤ), (0 : ℤ)) e ∧ CE k (1 : ℤ) ((0 : ℤ), (0 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((0 : ℤ), (0 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (1 : ℤ) ((0 : ℤ), (0 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_0_0_p_px 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_0_0_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (0 : ℤ))) (hc : ECover k (-1 : ℤ) ((0 : ℤ), (0 : ℤ)) e) :
    SE k (-1 : ℤ) ((0 : ℤ), (0 : ℤ)) e ∧ PE k ((0 : ℤ), (0 : ℤ)) e ∧ CE k (-1 : ℤ) ((0 : ℤ), (0 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((0 : ℤ), (0 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (-1 : ℤ) ((0 : ℤ), (0 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_0_0_m_px 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_0_1_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (1 : ℤ))) (hc : ECover k (1 : ℤ) ((0 : ℤ), (1 : ℤ)) e) :
    SE k (1 : ℤ) ((0 : ℤ), (1 : ℤ)) e ∧ PE k ((0 : ℤ), (1 : ℤ)) e ∧ CE k (1 : ℤ) ((0 : ℤ), (1 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((0 : ℤ), (1 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (1 : ℤ) ((0 : ℤ), (1 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr0_0_1_p_my 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_0_1_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (1 : ℤ))) (hc : ECover k (-1 : ℤ) ((0 : ℤ), (1 : ℤ)) e) :
    SE k (-1 : ℤ) ((0 : ℤ), (1 : ℤ)) e ∧ PE k ((0 : ℤ), (1 : ℤ)) e ∧ CE k (-1 : ℤ) ((0 : ℤ), (1 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((0 : ℤ), (1 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (-1 : ℤ) ((0 : ℤ), (1 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr0_0_1_m_py 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_0_2_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (2 : ℤ))) (hc : ECover k (1 : ℤ) ((0 : ℤ), (2 : ℤ)) e) :
    SE k (1 : ℤ) ((0 : ℤ), (2 : ℤ)) e ∧ PE k ((0 : ℤ), (2 : ℤ)) e ∧ CE k (1 : ℤ) ((0 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((0 : ℤ), (2 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (1 : ℤ) ((0 : ℤ), (2 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_0_2_p_mx 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_0_2_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (2 : ℤ))) (hc : ECover k (-1 : ℤ) ((0 : ℤ), (2 : ℤ)) e) :
    SE k (-1 : ℤ) ((0 : ℤ), (2 : ℤ)) e ∧ PE k ((0 : ℤ), (2 : ℤ)) e ∧ CE k (-1 : ℤ) ((0 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((0 : ℤ), (2 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (-1 : ℤ) ((0 : ℤ), (2 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_0_2_m_mx 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_0_3_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (3 : ℤ))) (hc : ECover k (1 : ℤ) ((0 : ℤ), (3 : ℤ)) e) :
    SE k (1 : ℤ) ((0 : ℤ), (3 : ℤ)) e ∧ PE k ((0 : ℤ), (3 : ℤ)) e ∧ CE k (1 : ℤ) ((0 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((0 : ℤ), (3 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((0 : ℤ), (3 : ℤ)) - ((0 : ℤ), (3 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr0_0_3_p_my 0 (by norm_num)
  · have hs : incomingPos ((0 : ℤ), (3 : ℤ)) - ((0 : ℤ), (3 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr0_0_3_p_py 0 (by norm_num)

theorem cov0_0_3_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (3 : ℤ))) (hc : ECover k (-1 : ℤ) ((0 : ℤ), (3 : ℤ)) e) :
    SE k (-1 : ℤ) ((0 : ℤ), (3 : ℤ)) e ∧ PE k ((0 : ℤ), (3 : ℤ)) e ∧ CE k (-1 : ℤ) ((0 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((0 : ℤ), (3 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((0 : ℤ), (3 : ℤ)) - ((0 : ℤ), (3 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr0_0_3_m_my 0 (by norm_num)
  · have hs : incomingPos ((0 : ℤ), (3 : ℤ)) - ((0 : ℤ), (3 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr0_0_3_m_py 0 (by norm_num)

theorem cov0_0_4_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (4 : ℤ))) (hc : ECover k (1 : ℤ) ((0 : ℤ), (4 : ℤ)) e) :
    SE k (1 : ℤ) ((0 : ℤ), (4 : ℤ)) e ∧ PE k ((0 : ℤ), (4 : ℤ)) e ∧ CE k (1 : ℤ) ((0 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((0 : ℤ), (4 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (1 : ℤ) ((0 : ℤ), (4 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_0_4_p_px 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_0_4_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (4 : ℤ))) (hc : ECover k (-1 : ℤ) ((0 : ℤ), (4 : ℤ)) e) :
    SE k (-1 : ℤ) ((0 : ℤ), (4 : ℤ)) e ∧ PE k ((0 : ℤ), (4 : ℤ)) e ∧ CE k (-1 : ℤ) ((0 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((0 : ℤ), (4 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (-1 : ℤ) ((0 : ℤ), (4 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_0_4_m_px 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_1_0_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (0 : ℤ))) (hc : ECover k (1 : ℤ) ((1 : ℤ), (0 : ℤ)) e) :
    SE k (1 : ℤ) ((1 : ℤ), (0 : ℤ)) e ∧ PE k ((1 : ℤ), (0 : ℤ)) e ∧ CE k (1 : ℤ) ((1 : ℤ), (0 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((1 : ℤ), (0 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (1 : ℤ) ((1 : ℤ), (0 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr0_1_0_p_my 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_1_0_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (0 : ℤ))) (hc : ECover k (-1 : ℤ) ((1 : ℤ), (0 : ℤ)) e) :
    SE k (-1 : ℤ) ((1 : ℤ), (0 : ℤ)) e ∧ PE k ((1 : ℤ), (0 : ℤ)) e ∧ CE k (-1 : ℤ) ((1 : ℤ), (0 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((1 : ℤ), (0 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (-1 : ℤ) ((1 : ℤ), (0 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr0_1_0_m_py 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_1_1_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (1 : ℤ))) (hc : ECover k (1 : ℤ) ((1 : ℤ), (1 : ℤ)) e) :
    SE k (1 : ℤ) ((1 : ℤ), (1 : ℤ)) e ∧ PE k ((1 : ℤ), (1 : ℤ)) e ∧ CE k (1 : ℤ) ((1 : ℤ), (1 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((1 : ℤ), (1 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((1 : ℤ), (1 : ℤ)) - ((1 : ℤ), (1 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_1_1_p_mx 0 (by norm_num)
  · have hs : incomingPos ((1 : ℤ), (1 : ℤ)) - ((1 : ℤ), (1 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_1_1_p_px 0 (by norm_num)

theorem cov0_1_1_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (1 : ℤ))) (hc : ECover k (-1 : ℤ) ((1 : ℤ), (1 : ℤ)) e) :
    SE k (-1 : ℤ) ((1 : ℤ), (1 : ℤ)) e ∧ PE k ((1 : ℤ), (1 : ℤ)) e ∧ CE k (-1 : ℤ) ((1 : ℤ), (1 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((1 : ℤ), (1 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((1 : ℤ), (1 : ℤ)) - ((1 : ℤ), (1 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_1_1_m_mx 0 (by norm_num)
  · have hs : incomingPos ((1 : ℤ), (1 : ℤ)) - ((1 : ℤ), (1 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_1_1_m_px 0 (by norm_num)

theorem cov0_1_2_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (2 : ℤ))) (hc : ECover k (1 : ℤ) ((1 : ℤ), (2 : ℤ)) e) :
    SE k (1 : ℤ) ((1 : ℤ), (2 : ℤ)) e ∧ PE k ((1 : ℤ), (2 : ℤ)) e ∧ CE k (1 : ℤ) ((1 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((1 : ℤ), (2 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((1 : ℤ), (2 : ℤ)) - ((1 : ℤ), (2 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr0_1_2_p_my 0 (by norm_num)
  · have hs : incomingPos ((1 : ℤ), (2 : ℤ)) - ((1 : ℤ), (2 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr0_1_2_p_py 0 (by norm_num)

theorem cov0_1_2_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (2 : ℤ))) (hc : ECover k (-1 : ℤ) ((1 : ℤ), (2 : ℤ)) e) :
    SE k (-1 : ℤ) ((1 : ℤ), (2 : ℤ)) e ∧ PE k ((1 : ℤ), (2 : ℤ)) e ∧ CE k (-1 : ℤ) ((1 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((1 : ℤ), (2 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((1 : ℤ), (2 : ℤ)) - ((1 : ℤ), (2 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr0_1_2_m_my 0 (by norm_num)
  · have hs : incomingPos ((1 : ℤ), (2 : ℤ)) - ((1 : ℤ), (2 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr0_1_2_m_py 0 (by norm_num)

theorem cov0_1_3_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (3 : ℤ))) (hc : ECover k (1 : ℤ) ((1 : ℤ), (3 : ℤ)) e) :
    SE k (1 : ℤ) ((1 : ℤ), (3 : ℤ)) e ∧ PE k ((1 : ℤ), (3 : ℤ)) e ∧ CE k (1 : ℤ) ((1 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((1 : ℤ), (3 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((1 : ℤ), (3 : ℤ)) - ((1 : ℤ), (3 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_1_3_p_mx 0 (by norm_num)
  · have hs : incomingPos ((1 : ℤ), (3 : ℤ)) - ((1 : ℤ), (3 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_1_3_p_px 0 (by norm_num)

theorem cov0_1_3_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (3 : ℤ))) (hc : ECover k (-1 : ℤ) ((1 : ℤ), (3 : ℤ)) e) :
    SE k (-1 : ℤ) ((1 : ℤ), (3 : ℤ)) e ∧ PE k ((1 : ℤ), (3 : ℤ)) e ∧ CE k (-1 : ℤ) ((1 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((1 : ℤ), (3 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((1 : ℤ), (3 : ℤ)) - ((1 : ℤ), (3 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_1_3_m_mx 0 (by norm_num)
  · have hs : incomingPos ((1 : ℤ), (3 : ℤ)) - ((1 : ℤ), (3 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_1_3_m_px 0 (by norm_num)

theorem cov0_1_4_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (4 : ℤ))) (hc : ECover k (1 : ℤ) ((1 : ℤ), (4 : ℤ)) e) :
    SE k (1 : ℤ) ((1 : ℤ), (4 : ℤ)) e ∧ PE k ((1 : ℤ), (4 : ℤ)) e ∧ CE k (1 : ℤ) ((1 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((1 : ℤ), (4 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (1 : ℤ) ((1 : ℤ), (4 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr0_1_4_p_py 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_1_4_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (4 : ℤ))) (hc : ECover k (-1 : ℤ) ((1 : ℤ), (4 : ℤ)) e) :
    SE k (-1 : ℤ) ((1 : ℤ), (4 : ℤ)) e ∧ PE k ((1 : ℤ), (4 : ℤ)) e ∧ CE k (-1 : ℤ) ((1 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((1 : ℤ), (4 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (-1 : ℤ) ((1 : ℤ), (4 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr0_1_4_m_py 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_2_0_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (0 : ℤ))) (hc : ECover k (1 : ℤ) ((2 : ℤ), (0 : ℤ)) e) :
    SE k (1 : ℤ) ((2 : ℤ), (0 : ℤ)) e ∧ PE k ((2 : ℤ), (0 : ℤ)) e ∧ CE k (1 : ℤ) ((2 : ℤ), (0 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((2 : ℤ), (0 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (1 : ℤ) ((2 : ℤ), (0 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_2_0_p_px 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_2_0_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (0 : ℤ))) (hc : ECover k (-1 : ℤ) ((2 : ℤ), (0 : ℤ)) e) :
    SE k (-1 : ℤ) ((2 : ℤ), (0 : ℤ)) e ∧ PE k ((2 : ℤ), (0 : ℤ)) e ∧ CE k (-1 : ℤ) ((2 : ℤ), (0 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((2 : ℤ), (0 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (-1 : ℤ) ((2 : ℤ), (0 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_2_0_m_px 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_2_1_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (1 : ℤ))) (hc : ECover k (1 : ℤ) ((2 : ℤ), (1 : ℤ)) e) :
    SE k (1 : ℤ) ((2 : ℤ), (1 : ℤ)) e ∧ PE k ((2 : ℤ), (1 : ℤ)) e ∧ CE k (1 : ℤ) ((2 : ℤ), (1 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((2 : ℤ), (1 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((2 : ℤ), (1 : ℤ)) - ((2 : ℤ), (1 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr0_2_1_p_my 0 (by norm_num)
  · have hs : incomingPos ((2 : ℤ), (1 : ℤ)) - ((2 : ℤ), (1 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr0_2_1_p_py 0 (by norm_num)

theorem cov0_2_1_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (1 : ℤ))) (hc : ECover k (-1 : ℤ) ((2 : ℤ), (1 : ℤ)) e) :
    SE k (-1 : ℤ) ((2 : ℤ), (1 : ℤ)) e ∧ PE k ((2 : ℤ), (1 : ℤ)) e ∧ CE k (-1 : ℤ) ((2 : ℤ), (1 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((2 : ℤ), (1 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((2 : ℤ), (1 : ℤ)) - ((2 : ℤ), (1 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr0_2_1_m_my 0 (by norm_num)
  · have hs : incomingPos ((2 : ℤ), (1 : ℤ)) - ((2 : ℤ), (1 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr0_2_1_m_py 0 (by norm_num)

theorem cov0_2_2_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (2 : ℤ))) (hc : ECover k (1 : ℤ) ((2 : ℤ), (2 : ℤ)) e) :
    SE k (1 : ℤ) ((2 : ℤ), (2 : ℤ)) e ∧ PE k ((2 : ℤ), (2 : ℤ)) e ∧ CE k (1 : ℤ) ((2 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((2 : ℤ), (2 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (1 : ℤ) ((2 : ℤ), (2 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_2_2_p_px 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_2_2_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (2 : ℤ))) (hc : ECover k (-1 : ℤ) ((2 : ℤ), (2 : ℤ)) e) :
    SE k (-1 : ℤ) ((2 : ℤ), (2 : ℤ)) e ∧ PE k ((2 : ℤ), (2 : ℤ)) e ∧ CE k (-1 : ℤ) ((2 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((2 : ℤ), (2 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (-1 : ℤ) ((2 : ℤ), (2 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_2_2_m_px 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_2_3_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (3 : ℤ))) (hc : ECover k (1 : ℤ) ((2 : ℤ), (3 : ℤ)) e) :
    SE k (1 : ℤ) ((2 : ℤ), (3 : ℤ)) e ∧ PE k ((2 : ℤ), (3 : ℤ)) e ∧ CE k (1 : ℤ) ((2 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((2 : ℤ), (3 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (1 : ℤ) ((2 : ℤ), (3 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr0_2_3_p_my 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_2_3_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (3 : ℤ))) (hc : ECover k (-1 : ℤ) ((2 : ℤ), (3 : ℤ)) e) :
    SE k (-1 : ℤ) ((2 : ℤ), (3 : ℤ)) e ∧ PE k ((2 : ℤ), (3 : ℤ)) e ∧ CE k (-1 : ℤ) ((2 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((2 : ℤ), (3 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (-1 : ℤ) ((2 : ℤ), (3 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr0_2_3_m_py 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_2_4_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (4 : ℤ))) (hc : ECover k (1 : ℤ) ((2 : ℤ), (4 : ℤ)) e) :
    SE k (1 : ℤ) ((2 : ℤ), (4 : ℤ)) e ∧ PE k ((2 : ℤ), (4 : ℤ)) e ∧ CE k (1 : ℤ) ((2 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((2 : ℤ), (4 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (1 : ℤ) ((2 : ℤ), (4 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_2_4_p_px 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_2_4_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (4 : ℤ))) (hc : ECover k (-1 : ℤ) ((2 : ℤ), (4 : ℤ)) e) :
    SE k (-1 : ℤ) ((2 : ℤ), (4 : ℤ)) e ∧ PE k ((2 : ℤ), (4 : ℤ)) e ∧ CE k (-1 : ℤ) ((2 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((2 : ℤ), (4 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (-1 : ℤ) ((2 : ℤ), (4 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_2_4_m_mx 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_3_0_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((3 : ℤ), (0 : ℤ))) (hc : ECover k (1 : ℤ) ((3 : ℤ), (0 : ℤ)) e) :
    SE k (1 : ℤ) ((3 : ℤ), (0 : ℤ)) e ∧ PE k ((3 : ℤ), (0 : ℤ)) e ∧ CE k (1 : ℤ) ((3 : ℤ), (0 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((3 : ℤ), (0 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (1 : ℤ) ((3 : ℤ), (0 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr0_3_0_p_py 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_3_0_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((3 : ℤ), (0 : ℤ))) (hc : ECover k (-1 : ℤ) ((3 : ℤ), (0 : ℤ)) e) :
    SE k (-1 : ℤ) ((3 : ℤ), (0 : ℤ)) e ∧ PE k ((3 : ℤ), (0 : ℤ)) e ∧ CE k (-1 : ℤ) ((3 : ℤ), (0 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((3 : ℤ), (0 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (-1 : ℤ) ((3 : ℤ), (0 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr0_3_0_m_py 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_3_1_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((3 : ℤ), (1 : ℤ))) (hc : ECover k (1 : ℤ) ((3 : ℤ), (1 : ℤ)) e) :
    SE k (1 : ℤ) ((3 : ℤ), (1 : ℤ)) e ∧ PE k ((3 : ℤ), (1 : ℤ)) e ∧ CE k (1 : ℤ) ((3 : ℤ), (1 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((3 : ℤ), (1 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (1 : ℤ) ((3 : ℤ), (1 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_3_1_p_px 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_3_1_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((3 : ℤ), (1 : ℤ))) (hc : ECover k (-1 : ℤ) ((3 : ℤ), (1 : ℤ)) e) :
    SE k (-1 : ℤ) ((3 : ℤ), (1 : ℤ)) e ∧ PE k ((3 : ℤ), (1 : ℤ)) e ∧ CE k (-1 : ℤ) ((3 : ℤ), (1 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((3 : ℤ), (1 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (-1 : ℤ) ((3 : ℤ), (1 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr0_3_1_m_px 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_3_2_p (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((3 : ℤ), (2 : ℤ))) (hc : ECover k (1 : ℤ) ((3 : ℤ), (2 : ℤ)) e) :
    SE k (1 : ℤ) ((3 : ℤ), (2 : ℤ)) e ∧ PE k ((3 : ℤ), (2 : ℤ)) e ∧ CE k (1 : ℤ) ((3 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((3 : ℤ), (2 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (1 : ℤ) ((3 : ℤ), (2 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr0_3_2_p_my 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov0_3_2_m (k : ℕ) (hk : (k : ℤ) = 0) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((3 : ℤ), (2 : ℤ))) (hc : ECover k (-1 : ℤ) ((3 : ℤ), (2 : ℤ)) e) :
    SE k (-1 : ℤ) ((3 : ℤ), (2 : ℤ)) e ∧ PE k ((3 : ℤ), (2 : ℤ)) e ∧ CE k (-1 : ℤ) ((3 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 0 := by omega
  have hl : laplacian (reciprocalField 0) ((3 : ℤ), (2 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 0 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((0 : ℕ) : ℤ) + 3) (-1 : ℤ) ((3 : ℤ), (2 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr0_3_2_m_py 0 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cover_small0 (k : ℕ) (hk : (k : ℤ) = 0) (r : Site)
    (hr : NativeP (2 * (k : ℤ) + 3) r) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site) (hc : ECover k η r e) :
    SE k η r e ∧ PE k r e ∧ CE k η r e := by
  obtain ⟨a, b⟩ := r
  have hN := hr
  unfold NativeP at hN
  simp only [Prod.mk.injEq] at hN
  have ha1 : -1 ≤ a := by omega
  have ha2 : a ≤ 3 := by omega
  have hb1 : 0 ≤ b := by omega
  have hb2 : b ≤ 4 := by omega
  rcases hη with rfl | rfl
  · interval_cases a <;> interval_cases b
    · exfalso
      omega
    · exfalso
      omega
    · exact cov0_m1_2_p k hk e hr hc
    · exact cov0_m1_3_p k hk e hr hc
    · exact cov0_m1_4_p k hk e hr hc
    · exact cov0_0_0_p k hk e hr hc
    · exact cov0_0_1_p k hk e hr hc
    · exact cov0_0_2_p k hk e hr hc
    · exact cov0_0_3_p k hk e hr hc
    · exact cov0_0_4_p k hk e hr hc
    · exact cov0_1_0_p k hk e hr hc
    · exact cov0_1_1_p k hk e hr hc
    · exact cov0_1_2_p k hk e hr hc
    · exact cov0_1_3_p k hk e hr hc
    · exact cov0_1_4_p k hk e hr hc
    · exact cov0_2_0_p k hk e hr hc
    · exact cov0_2_1_p k hk e hr hc
    · exact cov0_2_2_p k hk e hr hc
    · exact cov0_2_3_p k hk e hr hc
    · exact cov0_2_4_p k hk e hr hc
    · exact cov0_3_0_p k hk e hr hc
    · exact cov0_3_1_p k hk e hr hc
    · exact cov0_3_2_p k hk e hr hc
    · exfalso
      omega
    · exfalso
      omega
  · interval_cases a <;> interval_cases b
    · exfalso
      omega
    · exfalso
      omega
    · exact cov0_m1_2_m k hk e hr hc
    · exact cov0_m1_3_m k hk e hr hc
    · exact cov0_m1_4_m k hk e hr hc
    · exact cov0_0_0_m k hk e hr hc
    · exact cov0_0_1_m k hk e hr hc
    · exact cov0_0_2_m k hk e hr hc
    · exact cov0_0_3_m k hk e hr hc
    · exact cov0_0_4_m k hk e hr hc
    · exact cov0_1_0_m k hk e hr hc
    · exact cov0_1_1_m k hk e hr hc
    · exact cov0_1_2_m k hk e hr hc
    · exact cov0_1_3_m k hk e hr hc
    · exact cov0_1_4_m k hk e hr hc
    · exact cov0_2_0_m k hk e hr hc
    · exact cov0_2_1_m k hk e hr hc
    · exact cov0_2_2_m k hk e hr hc
    · exact cov0_2_3_m k hk e hr hc
    · exact cov0_2_4_m k hk e hr hc
    · exact cov0_3_0_m k hk e hr hc
    · exact cov0_3_1_m k hk e hr hc
    · exact cov0_3_2_m k hk e hr hc
    · exfalso
      omega
    · exfalso
      omega


theorem tr1_m3_4_p_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((-3), (4)) ≤ incr (reciprocalField k) (0, -1) ((-5), (4)) ∧
    incr (reciprocalField k) (0, -1) ((-3), (4)) - incr (reciprocalField k) (0, -1) ((-4), (5)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((-3), (4)) - incr (reciprocalField k) (0, -1) ((-6), (5)) ≤ -1 := by
  have hZ1_0 : incr (reciprocalField k) (0, -1) ((-3), (4)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 3), (5)) :=
    incr_eq_U k (0, -1) ((-3), (4)) (((2 * (k : ℤ) + 3) - 3), (5)) (by ext <;> (simp; try ring))
  have hZ2_0 : incr (reciprocalField k) (0, -1) ((-5), (4)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 5), (5)) :=
    incr_eq_U k (0, -1) ((-5), (4)) (((2 * (k : ℤ) + 3) - 5), (5)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (0, -1) ((-4), (5)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 4), (6)) :=
    incr_eq_U k (0, -1) ((-4), (5)) (((2 * (k : ℤ) + 3) - 4), (6)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, -1) ((-6), (5)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 6), (6)) :=
    incr_eq_U k (0, -1) ((-6), (5)) (((2 * (k : ℤ) + 3) - 6), (6)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 3), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 3) (5) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) (5) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 5), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 5) (5) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 5) (5) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 5) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 4), (6)) = ((6)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 4) (6) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) (6) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) ((6) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 6), (6)) = ((6)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 6) (6) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 6) (6) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 6) ((6) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m3_4_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((-3), (4)) ≤ incr (reciprocalField k) (0, 1) ((-1), (4)) ∧
    incr (reciprocalField k) (0, 1) ((-3), (4)) - incr (reciprocalField k) (0, 1) ((-4), (5)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((-3), (4)) - incr (reciprocalField k) (0, 1) ((-2), (5)) ≤ 1 := by
  have hZ3_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 5), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-4), (5)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 5), (4 - (2 * (k : ℤ) + 3))) ((-4), (5)) (by ext <;> (simp; try ring))
  have hZ3_1 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 5), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((2 * (2 * (k : ℤ) + 3) + -5), (5 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (0, 1) (((2 * (k : ℤ) + 3) - 5), (4 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -5), (5 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, 1) ((-3), (4)) = -((4)) := by
    rw [incr_vert k 1 (-3) (4) (Or.inl rfl) (mem_raw_of_box k (-3) (4) (by omega)) (mem_raw_of_box k (-3) ((4) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((-1), (4)) = -((4)) := by
    rw [incr_vert k 1 (-1) (4) (Or.inl rfl) (mem_raw_of_box k (-1) (4) (by omega)) (mem_raw_of_box k (-1) ((4) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((2 * (2 * (k : ℤ) + 3) + -5), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 (2 * (2 * (k : ℤ) + 3) + -5) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -5) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -5) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((-2), (5)) = -((5)) := by
    rw [incr_vert k 1 (-2) (5) (Or.inl rfl) (mem_raw_of_box k (-2) (5) (by omega)) (mem_raw_of_box k (-2) ((5) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m3_5_p_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((-3), (5)) ≤ incr (reciprocalField k) (1, 0) ((-5), (5)) ∧
    incr (reciprocalField k) (1, 0) ((-3), (5)) - incr (reciprocalField k) (1, 0) ((-4), (6)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((-3), (5)) - incr (reciprocalField k) (1, 0) ((-6), (6)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (1, 0) ((-5), (5)) = incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 5), (6)) :=
    incr_eq_U k (1, 0) ((-5), (5)) (((2 * (k : ℤ) + 3) - 5), (6)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 5), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((-4), (6)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) (((2 * (k : ℤ) + 3) - 5), (5 - (2 * (k : ℤ) + 3))) ((-4), (6)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 7), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((-6), (6)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) (((2 * (k : ℤ) + 3) - 7), (5 - (2 * (k : ℤ) + 3))) ((-6), (6)) (by ext <;> (simp; try ring))
  have hZ4_1 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 7), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((2 * (2 * (k : ℤ) + 3) + -7), (6 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (1, 0) (((2 * (k : ℤ) + 3) - 7), (5 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -7), (6 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (1, 0) ((-3), (5)) = min ((-3) + (1) - 1) 0 - min ((-3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (-3) (5) (mem_raw_of_box k ((-3) + (1)) (5) (by omega)) (mem_raw_of_box k (-3) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-3) (5) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((-3) + (1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-3) (5) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 5), (6)) = min (((2 * (k : ℤ) + 3) - 5) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 5) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 5) (6) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 5) + (1)) (6) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 5) (6) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 5) (6) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 5) + (1)) (6) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 5) (6) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 5), (5 - (2 * (k : ℤ) + 3))) = min (((2 * (k : ℤ) + 3) - 5) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 5) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 5) (5 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 5) + (1)) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 5) (5 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 5) + (1)) (5 - (2 * (k : ℤ) + 3)) (by omega)) (corner_yes (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 5) (5 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((2 * (2 * (k : ℤ) + 3) + -7), (6 - (2 * (k : ℤ) + 3))) = min ((2 * (2 * (k : ℤ) + 3) + -7) + (1) - 1) 0 - min ((2 * (2 * (k : ℤ) + 3) + -7) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2 * (2 * (k : ℤ) + 3) + -7) (6 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k ((2 * (2 * (k : ℤ) + 3) + -7) + (1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -7) (6 - (2 * (k : ℤ) + 3)) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2 * (2 * (k : ℤ) + 3) + -7) (6 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (2 * (k : ℤ) + 3) + -7) + (1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2 * (2 * (k : ℤ) + 3) + -7) (6 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m3_5_m_mx (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (-1, 0) ((-3), (5)) ≤ incr (reciprocalField k) (-1, 0) ((-1), (5)) ∧
    incr (reciprocalField k) (-1, 0) ((-3), (5)) - incr (reciprocalField k) (-1, 0) ((-4), (6)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((-3), (5)) - incr (reciprocalField k) (-1, 0) ((-2), (6)) ≤ 0 := by
  have hZ1_0 : incr (reciprocalField k) (-1, 0) ((-3), (5)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 3), (6)) :=
    incr_eq_U k (-1, 0) ((-3), (5)) (((2 * (k : ℤ) + 3) - 3), (6)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 5), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (-1, 0) ((-4), (6)) + ((2 * (k : ℤ) + 3) * 0 - -1) :=
    incr_eq_T k (-1, 0) (((2 * (k : ℤ) + 3) - 5), (5 - (2 * (k : ℤ) + 3))) ((-4), (6)) (by ext <;> (simp; try ring))
  have hZ3_1 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 5), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (-1, 0) ((2 * (2 * (k : ℤ) + 3) + -5), (6 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (-1, 0) (((2 * (k : ℤ) + 3) - 5), (5 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -5), (6 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 3), (6)) = min (((2 * (k : ℤ) + 3) - 3) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 3) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 3) (6) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 3) + (-1)) (6) (by omega)) (mem_raw_corner2' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (6) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 3) + (-1)) (6) (by omega)) (corner_yes (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (6) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) ((-1), (5)) = min ((-1) + (-1) - 1) 0 - min ((-1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-1) (5) (mem_raw_of_box k ((-1) + (-1)) (5) (by omega)) (mem_raw_of_box k (-1) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-1) (5) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-1) + (-1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-1) (5) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((2 * (2 * (k : ℤ) + 3) + -5), (6 - (2 * (k : ℤ) + 3))) = min ((2 * (2 * (k : ℤ) + 3) + -5) + (-1) - 1) 0 - min ((2 * (2 * (k : ℤ) + 3) + -5) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (2 * (2 * (k : ℤ) + 3) + -5) (6 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k ((2 * (2 * (k : ℤ) + 3) + -5) + (-1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -5) (6 - (2 * (k : ℤ) + 3)) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2 * (2 * (k : ℤ) + 3) + -5) (6 - (2 * (k : ℤ) + 3)) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (2 * (k : ℤ) + 3) + -5) + (-1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2 * (2 * (k : ℤ) + 3) + -5) (6 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) ((-2), (6)) = min ((-2) + (-1) - 1) 0 - min ((-2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-2) (6) (mem_raw_of_box k ((-2) + (-1)) (6) (by omega)) (mem_raw_of_box k (-2) (6) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-2) (6) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-2) + (-1)) (6) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-2) (6) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m3_6_p_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((-3), (6)) ≤ incr (reciprocalField k) (0, -1) ((-5), (6)) ∧
    incr (reciprocalField k) (0, -1) ((-3), (6)) - incr (reciprocalField k) (0, -1) ((-4), (7)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((-3), (6)) - incr (reciprocalField k) (0, -1) ((-6), (7)) ≤ -1 := by
  have hZ2_0 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 6), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, -1) ((-5), (6)) + ((2 * (k : ℤ) + 3) * -1 - 0) :=
    incr_eq_T k (0, -1) (((2 * (k : ℤ) + 3) - 6), (5 - (2 * (k : ℤ) + 3))) ((-5), (6)) (by ext <;> (simp; try ring))
  have hZ2_1 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 6), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, -1) ((2 * (2 * (k : ℤ) + 3) + -6), (6 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (0, -1) (((2 * (k : ℤ) + 3) - 6), (5 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -6), (6 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 5), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, -1) ((-4), (7)) + ((2 * (k : ℤ) + 3) * -1 - 0) :=
    incr_eq_T k (0, -1) (((2 * (k : ℤ) + 3) - 5), (6 - (2 * (k : ℤ) + 3))) ((-4), (7)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 7), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, -1) ((-6), (7)) + ((2 * (k : ℤ) + 3) * -1 - 0) :=
    incr_eq_T k (0, -1) (((2 * (k : ℤ) + 3) - 7), (6 - (2 * (k : ℤ) + 3))) ((-6), (7)) (by ext <;> (simp; try ring))
  have hZ4_1 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 7), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, -1) ((2 * (2 * (k : ℤ) + 3) + -7), (7 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (0, -1) (((2 * (k : ℤ) + 3) - 7), (6 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -7), (7 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, -1) ((-3), (6)) = ((6)) + -1 := by
    rw [incr_vert k (-1) (-3) (6) (Or.inr rfl) (mem_raw_of_box k (-3) (6) (by omega)) (mem_raw_of_box k (-3) ((6) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((2 * (2 * (k : ℤ) + 3) + -6), (6 - (2 * (k : ℤ) + 3))) = ((6 - (2 * (k : ℤ) + 3))) + -1 := by
    rw [incr_vert k (-1) (2 * (2 * (k : ℤ) + 3) + -6) (6 - (2 * (k : ℤ) + 3)) (Or.inr rfl) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -6) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -6) ((6 - (2 * (k : ℤ) + 3)) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 5), (6 - (2 * (k : ℤ) + 3))) = 1 := by
    rw [show (((2 * (k : ℤ) + 3) - 5), (6 - (2 * (k : ℤ) + 3))) = ((0 : ℤ), (1 : ℤ)) from by ext <;> omega]
    exact incr_c0_fromdown k
  have vZ4 : incr (reciprocalField k) (0, -1) ((2 * (2 * (k : ℤ) + 3) + -7), (7 - (2 * (k : ℤ) + 3))) = ((7 - (2 * (k : ℤ) + 3))) + -1 := by
    rw [incr_vert k (-1) (2 * (2 * (k : ℤ) + 3) + -7) (7 - (2 * (k : ℤ) + 3)) (Or.inr rfl) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -7) (7 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -7) ((7 - (2 * (k : ℤ) + 3)) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m3_6_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((-3), (6)) ≤ incr (reciprocalField k) (0, 1) ((-1), (6)) ∧
    incr (reciprocalField k) (0, 1) ((-3), (6)) - incr (reciprocalField k) (0, 1) ((-4), (7)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((-3), (6)) - incr (reciprocalField k) (0, 1) ((-2), (7)) ≤ 1 := by
  have hZ1_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 4), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-3), (6)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 4), (5 - (2 * (k : ℤ) + 3))) ((-3), (6)) (by ext <;> (simp; try ring))
  have hZ2_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-1), (6)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) ((-1), (6)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 5), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-4), (7)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 5), (6 - (2 * (k : ℤ) + 3))) ((-4), (7)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 3), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-2), (7)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 3), (6 - (2 * (k : ℤ) + 3))) ((-2), (7)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 4), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 4) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 2) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 5), (6 - (2 * (k : ℤ) + 3))) = -((6 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 5) (6 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 5) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 5) ((6 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 3), (6 - (2 * (k : ℤ) + 3))) = -((6 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 3) (6 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) ((6 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m2_3_p_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((-2), (3)) ≤ incr (reciprocalField k) (0, -1) ((-4), (3)) ∧
    incr (reciprocalField k) (0, -1) ((-2), (3)) - incr (reciprocalField k) (0, -1) ((-3), (4)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((-2), (3)) - incr (reciprocalField k) (0, -1) ((-5), (4)) ≤ -1 := by
  have hZ1_0 : incr (reciprocalField k) (0, -1) ((-2), (3)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (4)) :=
    incr_eq_U k (0, -1) ((-2), (3)) (((2 * (k : ℤ) + 3) - 2), (4)) (by ext <;> (simp; try ring))
  have hZ2_0 : incr (reciprocalField k) (0, -1) ((-4), (3)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 4), (4)) :=
    incr_eq_U k (0, -1) ((-4), (3)) (((2 * (k : ℤ) + 3) - 4), (4)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (0, -1) ((-3), (4)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 3), (5)) :=
    incr_eq_U k (0, -1) ((-3), (4)) (((2 * (k : ℤ) + 3) - 3), (5)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, -1) ((-5), (4)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 5), (5)) :=
    incr_eq_U k (0, -1) ((-5), (4)) (((2 * (k : ℤ) + 3) - 5), (5)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 2) (4) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (4) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 4), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 4) (4) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) (4) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 3), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 3) (5) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) (5) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 5), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 5) (5) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 5) (5) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 5) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m2_3_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((-2), (3)) ≤ incr (reciprocalField k) (0, 1) ((0), (3)) ∧
    incr (reciprocalField k) (0, 1) ((-2), (3)) - incr (reciprocalField k) (0, 1) ((-3), (4)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((-2), (3)) - incr (reciprocalField k) (0, 1) ((-1), (4)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((-2), (3)) = -((3)) := by
    rw [incr_vert k 1 (-2) (3) (Or.inl rfl) (mem_raw_of_box k (-2) (3) (by omega)) (mem_raw_of_box k (-2) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((0), (3)) = -((3)) := by
    rw [incr_vert k 1 (0) (3) (Or.inl rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((-3), (4)) = -((4)) := by
    rw [incr_vert k 1 (-3) (4) (Or.inl rfl) (mem_raw_of_box k (-3) (4) (by omega)) (mem_raw_of_box k (-3) ((4) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((-1), (4)) = -((4)) := by
    rw [incr_vert k 1 (-1) (4) (Or.inl rfl) (mem_raw_of_box k (-1) (4) (by omega)) (mem_raw_of_box k (-1) ((4) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m2_4_p_mx (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (-1, 0) ((-2), (4)) ≤ incr (reciprocalField k) (-1, 0) ((-4), (4)) ∧
    incr (reciprocalField k) (-1, 0) ((-2), (4)) - incr (reciprocalField k) (-1, 0) ((-3), (5)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((-2), (4)) - incr (reciprocalField k) (-1, 0) ((-5), (5)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (-1, 0) ((-4), (4)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 4), (5)) :=
    incr_eq_U k (-1, 0) ((-4), (4)) (((2 * (k : ℤ) + 3) - 4), (5)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (-1, 0) ((-3), (5)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 3), (6)) :=
    incr_eq_U k (-1, 0) ((-3), (5)) (((2 * (k : ℤ) + 3) - 3), (6)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (-1, 0) ((-5), (5)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 5), (6)) :=
    incr_eq_U k (-1, 0) ((-5), (5)) (((2 * (k : ℤ) + 3) - 5), (6)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (-1, 0) ((-2), (4)) = min ((-2) + (-1) - 1) 0 - min ((-2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-2) (4) (mem_raw_of_box k ((-2) + (-1)) (4) (by omega)) (mem_raw_of_box k (-2) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-2) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-2) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-2) (4) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 4), (5)) = min (((2 * (k : ℤ) + 3) - 4) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 4) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 4) (5) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 4) + (-1)) (5) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 4) (5) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 4) + (-1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 4) (5) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 3), (6)) = min (((2 * (k : ℤ) + 3) - 3) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 3) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 3) (6) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 3) + (-1)) (6) (by omega)) (mem_raw_corner2' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (6) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 3) + (-1)) (6) (by omega)) (corner_yes (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (6) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 5), (6)) = min (((2 * (k : ℤ) + 3) - 5) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 5) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 5) (6) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 5) + (-1)) (6) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 5) (6) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 5) (6) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 5) + (-1)) (6) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 5) (6) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m2_4_m_mx (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (-1, 0) ((-2), (4)) ≤ incr (reciprocalField k) (-1, 0) ((0), (4)) ∧
    incr (reciprocalField k) (-1, 0) ((-2), (4)) - incr (reciprocalField k) (-1, 0) ((-3), (5)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((-2), (4)) - incr (reciprocalField k) (-1, 0) ((-1), (5)) ≤ 0 := by
  have hZ3_0 : incr (reciprocalField k) (-1, 0) ((-3), (5)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 3), (6)) :=
    incr_eq_U k (-1, 0) ((-3), (5)) (((2 * (k : ℤ) + 3) - 3), (6)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (-1, 0) ((-2), (4)) = min ((-2) + (-1) - 1) 0 - min ((-2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-2) (4) (mem_raw_of_box k ((-2) + (-1)) (4) (by omega)) (mem_raw_of_box k (-2) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-2) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-2) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-2) (4) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) ((0), (4)) = min ((0) + (-1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (0) (4) (mem_raw_of_box k ((0) + (-1)) (4) (by omega)) (mem_raw_of_box k (0) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (4) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 3), (6)) = min (((2 * (k : ℤ) + 3) - 3) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 3) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 3) (6) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 3) + (-1)) (6) (by omega)) (mem_raw_corner2' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (6) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 3) + (-1)) (6) (by omega)) (corner_yes (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (6) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) ((-1), (5)) = min ((-1) + (-1) - 1) 0 - min ((-1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-1) (5) (mem_raw_of_box k ((-1) + (-1)) (5) (by omega)) (mem_raw_of_box k (-1) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-1) (5) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-1) + (-1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-1) (5) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m2_5_p_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((-2), (5)) ≤ incr (reciprocalField k) (0, -1) ((-4), (5)) ∧
    incr (reciprocalField k) (0, -1) ((-2), (5)) - incr (reciprocalField k) (0, -1) ((-3), (6)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((-2), (5)) - incr (reciprocalField k) (0, -1) ((-5), (6)) ≤ -1 := by
  have hZ2_0 : incr (reciprocalField k) (0, -1) ((-4), (5)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 4), (6)) :=
    incr_eq_U k (0, -1) ((-4), (5)) (((2 * (k : ℤ) + 3) - 4), (6)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 6), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, -1) ((-5), (6)) + ((2 * (k : ℤ) + 3) * -1 - 0) :=
    incr_eq_T k (0, -1) (((2 * (k : ℤ) + 3) - 6), (5 - (2 * (k : ℤ) + 3))) ((-5), (6)) (by ext <;> (simp; try ring))
  have hZ4_1 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 6), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, -1) ((2 * (2 * (k : ℤ) + 3) + -6), (6 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (0, -1) (((2 * (k : ℤ) + 3) - 6), (5 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -6), (6 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, -1) ((-2), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) (-2) (5) (Or.inr rfl) (mem_raw_of_box k (-2) (5) (by omega)) (mem_raw_of_box k (-2) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 4), (6)) = ((6)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 4) (6) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) (6) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) ((6) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((-3), (6)) = ((6)) + -1 := by
    rw [incr_vert k (-1) (-3) (6) (Or.inr rfl) (mem_raw_of_box k (-3) (6) (by omega)) (mem_raw_of_box k (-3) ((6) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((2 * (2 * (k : ℤ) + 3) + -6), (6 - (2 * (k : ℤ) + 3))) = ((6 - (2 * (k : ℤ) + 3))) + -1 := by
    rw [incr_vert k (-1) (2 * (2 * (k : ℤ) + 3) + -6) (6 - (2 * (k : ℤ) + 3)) (Or.inr rfl) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -6) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -6) ((6 - (2 * (k : ℤ) + 3)) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m2_5_p_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((-2), (5)) ≤ incr (reciprocalField k) (0, 1) ((-4), (5)) ∧
    incr (reciprocalField k) (0, 1) ((-2), (5)) - incr (reciprocalField k) (0, 1) ((-3), (6)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((-2), (5)) - incr (reciprocalField k) (0, 1) ((-5), (6)) ≤ 1 := by
  have hZ2_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 5), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-4), (5)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 5), (4 - (2 * (k : ℤ) + 3))) ((-4), (5)) (by ext <;> (simp; try ring))
  have hZ2_1 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 5), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((2 * (2 * (k : ℤ) + 3) + -5), (5 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (0, 1) (((2 * (k : ℤ) + 3) - 5), (4 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -5), (5 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 4), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-3), (6)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 4), (5 - (2 * (k : ℤ) + 3))) ((-3), (6)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 6), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-5), (6)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 6), (5 - (2 * (k : ℤ) + 3))) ((-5), (6)) (by ext <;> (simp; try ring))
  have hZ4_1 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 6), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((2 * (2 * (k : ℤ) + 3) + -6), (6 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (0, 1) (((2 * (k : ℤ) + 3) - 6), (5 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -6), (6 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, 1) ((-2), (5)) = -((5)) := by
    rw [incr_vert k 1 (-2) (5) (Or.inl rfl) (mem_raw_of_box k (-2) (5) (by omega)) (mem_raw_of_box k (-2) ((5) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((2 * (2 * (k : ℤ) + 3) + -5), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 (2 * (2 * (k : ℤ) + 3) + -5) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -5) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -5) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 4), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 4) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((2 * (2 * (k : ℤ) + 3) + -6), (6 - (2 * (k : ℤ) + 3))) = -((6 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 (2 * (2 * (k : ℤ) + 3) + -6) (6 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -6) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -6) ((6 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m2_5_m_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((-2), (5)) ≤ incr (reciprocalField k) (0, -1) ((0), (5)) ∧
    incr (reciprocalField k) (0, -1) ((-2), (5)) - incr (reciprocalField k) (0, -1) ((-3), (6)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((-2), (5)) - incr (reciprocalField k) (0, -1) ((-1), (6)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((-2), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) (-2) (5) (Or.inr rfl) (mem_raw_of_box k (-2) (5) (by omega)) (mem_raw_of_box k (-2) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((0), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) (0) (5) (Or.inr rfl) (mem_raw_of_box k (0) (5) (by omega)) (mem_raw_of_box k (0) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((-3), (6)) = ((6)) + -1 := by
    rw [incr_vert k (-1) (-3) (6) (Or.inr rfl) (mem_raw_of_box k (-3) (6) (by omega)) (mem_raw_of_box k (-3) ((6) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((-1), (6)) = ((6)) + -1 := by
    rw [incr_vert k (-1) (-1) (6) (Or.inr rfl) (mem_raw_of_box k (-1) (6) (by omega)) (mem_raw_of_box k (-1) ((6) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m2_5_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((-2), (5)) ≤ incr (reciprocalField k) (0, 1) ((0), (5)) ∧
    incr (reciprocalField k) (0, 1) ((-2), (5)) - incr (reciprocalField k) (0, 1) ((-3), (6)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((-2), (5)) - incr (reciprocalField k) (0, 1) ((-1), (6)) ≤ 1 := by
  have hZ3_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 4), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-3), (6)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 4), (5 - (2 * (k : ℤ) + 3))) ((-3), (6)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-1), (6)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) ((-1), (6)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, 1) ((-2), (5)) = -((5)) := by
    rw [incr_vert k 1 (-2) (5) (Or.inl rfl) (mem_raw_of_box k (-2) (5) (by omega)) (mem_raw_of_box k (-2) ((5) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((0), (5)) = -((5)) := by
    rw [incr_vert k 1 (0) (5) (Or.inl rfl) (mem_raw_of_box k (0) (5) (by omega)) (mem_raw_of_box k (0) ((5) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 4), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 4) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 2) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m2_6_p_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((-2), (6)) ≤ incr (reciprocalField k) (1, 0) ((-4), (6)) ∧
    incr (reciprocalField k) (1, 0) ((-2), (6)) - incr (reciprocalField k) (1, 0) ((-3), (7)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((-2), (6)) - incr (reciprocalField k) (1, 0) ((-5), (7)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 5), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((-4), (6)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) (((2 * (k : ℤ) + 3) - 5), (5 - (2 * (k : ℤ) + 3))) ((-4), (6)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 4), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((-3), (7)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) (((2 * (k : ℤ) + 3) - 4), (6 - (2 * (k : ℤ) + 3))) ((-3), (7)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 6), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((-5), (7)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) (((2 * (k : ℤ) + 3) - 6), (6 - (2 * (k : ℤ) + 3))) ((-5), (7)) (by ext <;> (simp; try ring))
  have hZ4_1 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 6), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((2 * (2 * (k : ℤ) + 3) + -6), (7 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (1, 0) (((2 * (k : ℤ) + 3) - 6), (6 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -6), (7 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (1, 0) ((-2), (6)) = min ((-2) + (1) - 1) 0 - min ((-2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (-2) (6) (mem_raw_of_box k ((-2) + (1)) (6) (by omega)) (mem_raw_of_box k (-2) (6) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-2) (6) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((-2) + (1)) (6) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-2) (6) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 5), (5 - (2 * (k : ℤ) + 3))) = min (((2 * (k : ℤ) + 3) - 5) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 5) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 5) (5 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 5) + (1)) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 5) (5 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 5) + (1)) (5 - (2 * (k : ℤ) + 3)) (by omega)) (corner_yes (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 5) (5 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 4), (6 - (2 * (k : ℤ) + 3))) = min (((2 * (k : ℤ) + 3) - 4) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 4) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 4) (6 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 4) + (1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) (6 - (2 * (k : ℤ) + 3)) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 4) (6 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 4) + (1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 4) (6 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((2 * (2 * (k : ℤ) + 3) + -6), (7 - (2 * (k : ℤ) + 3))) = min ((2 * (2 * (k : ℤ) + 3) + -6) + (1) - 1) 0 - min ((2 * (2 * (k : ℤ) + 3) + -6) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2 * (2 * (k : ℤ) + 3) + -6) (7 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k ((2 * (2 * (k : ℤ) + 3) + -6) + (1)) (7 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -6) (7 - (2 * (k : ℤ) + 3)) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2 * (2 * (k : ℤ) + 3) + -6) (7 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (2 * (k : ℤ) + 3) + -6) + (1)) (7 - (2 * (k : ℤ) + 3)) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2 * (2 * (k : ℤ) + 3) + -6) (7 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m2_6_m_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((-2), (6)) ≤ incr (reciprocalField k) (1, 0) ((0), (6)) ∧
    incr (reciprocalField k) (1, 0) ((-2), (6)) - incr (reciprocalField k) (1, 0) ((-3), (7)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((-2), (6)) - incr (reciprocalField k) (1, 0) ((-1), (7)) ≤ 0 := by
  have hZ3_0 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 4), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((-3), (7)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) (((2 * (k : ℤ) + 3) - 4), (6 - (2 * (k : ℤ) + 3))) ((-3), (7)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((-1), (7)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) (((2 * (k : ℤ) + 3) - 2), (6 - (2 * (k : ℤ) + 3))) ((-1), (7)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (1, 0) ((-2), (6)) = min ((-2) + (1) - 1) 0 - min ((-2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (-2) (6) (mem_raw_of_box k ((-2) + (1)) (6) (by omega)) (mem_raw_of_box k (-2) (6) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-2) (6) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((-2) + (1)) (6) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-2) (6) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((0), (6)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (6) (mem_raw_of_box k ((0) + (1)) (6) (by omega)) (mem_raw_of_box k (0) (6) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (6) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (6) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (6) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 4), (6 - (2 * (k : ℤ) + 3))) = min (((2 * (k : ℤ) + 3) - 4) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 4) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 4) (6 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 4) + (1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) (6 - (2 * (k : ℤ) + 3)) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 4) (6 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 4) + (1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 4) (6 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (6 - (2 * (k : ℤ) + 3))) = min (((2 * (k : ℤ) + 3) - 2) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 2) (6 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 2) + (1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (6 - (2 * (k : ℤ) + 3)) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (6 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 2) + (1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (6 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m1_2_p_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((-1), (2)) ≤ incr (reciprocalField k) (0, -1) ((-3), (2)) ∧
    incr (reciprocalField k) (0, -1) ((-1), (2)) - incr (reciprocalField k) (0, -1) ((-2), (3)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((-1), (2)) - incr (reciprocalField k) (0, -1) ((-4), (3)) ≤ -1 := by
  have hZ1_0 : incr (reciprocalField k) (0, -1) ((-1), (2)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 1), (3)) :=
    incr_eq_U k (0, -1) ((-1), (2)) (((2 * (k : ℤ) + 3) - 1), (3)) (by ext <;> (simp; try ring))
  have hZ2_0 : incr (reciprocalField k) (0, -1) ((-3), (2)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 3), (3)) :=
    incr_eq_U k (0, -1) ((-3), (2)) (((2 * (k : ℤ) + 3) - 3), (3)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (0, -1) ((-2), (3)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (4)) :=
    incr_eq_U k (0, -1) ((-2), (3)) (((2 * (k : ℤ) + 3) - 2), (4)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, -1) ((-4), (3)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 4), (4)) :=
    incr_eq_U k (0, -1) ((-4), (3)) (((2 * (k : ℤ) + 3) - 4), (4)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 1), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 1) (3) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (3) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 3), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 3) (3) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) (3) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 2) (4) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (4) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 4), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 4) (4) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) (4) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m1_2_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((-1), (2)) ≤ incr (reciprocalField k) (0, 1) ((1), (2)) ∧
    incr (reciprocalField k) (0, 1) ((-1), (2)) - incr (reciprocalField k) (0, 1) ((-2), (3)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((-1), (2)) - incr (reciprocalField k) (0, 1) ((0), (3)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((-1), (2)) = -((2)) := by
    rw [incr_vert k 1 (-1) (2) (Or.inl rfl) (mem_raw_of_box k (-1) (2) (by omega)) (mem_raw_of_box k (-1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((1), (2)) = -((2)) := by
    rw [incr_vert k 1 (1) (2) (Or.inl rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((-2), (3)) = -((3)) := by
    rw [incr_vert k 1 (-2) (3) (Or.inl rfl) (mem_raw_of_box k (-2) (3) (by omega)) (mem_raw_of_box k (-2) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((0), (3)) = -((3)) := by
    rw [incr_vert k 1 (0) (3) (Or.inl rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m1_3_p_mx (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (-1, 0) ((-1), (3)) ≤ incr (reciprocalField k) (-1, 0) ((-3), (3)) ∧
    incr (reciprocalField k) (-1, 0) ((-1), (3)) - incr (reciprocalField k) (-1, 0) ((-2), (4)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((-1), (3)) - incr (reciprocalField k) (-1, 0) ((-4), (4)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (-1, 0) ((-3), (3)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 3), (4)) :=
    incr_eq_U k (-1, 0) ((-3), (3)) (((2 * (k : ℤ) + 3) - 3), (4)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (-1, 0) ((-4), (4)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 4), (5)) :=
    incr_eq_U k (-1, 0) ((-4), (4)) (((2 * (k : ℤ) + 3) - 4), (5)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (-1, 0) ((-1), (3)) = min ((-1) + (-1) - 1) 0 - min ((-1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-1) (3) (mem_raw_of_box k ((-1) + (-1)) (3) (by omega)) (mem_raw_of_box k (-1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-1) (3) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-1) + (-1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-1) (3) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 3), (4)) = min (((2 * (k : ℤ) + 3) - 3) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 3) (4) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 3) + (-1)) (4) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 3) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (4) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((-2), (4)) = min ((-2) + (-1) - 1) 0 - min ((-2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-2) (4) (mem_raw_of_box k ((-2) + (-1)) (4) (by omega)) (mem_raw_of_box k (-2) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-2) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-2) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-2) (4) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 4), (5)) = min (((2 * (k : ℤ) + 3) - 4) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 4) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 4) (5) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 4) + (-1)) (5) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 4) (5) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 4) + (-1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 4) (5) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m1_3_m_mx (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (-1, 0) ((-1), (3)) ≤ incr (reciprocalField k) (-1, 0) ((1), (3)) ∧
    incr (reciprocalField k) (-1, 0) ((-1), (3)) - incr (reciprocalField k) (-1, 0) ((-2), (4)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((-1), (3)) - incr (reciprocalField k) (-1, 0) ((0), (4)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (-1, 0) ((-1), (3)) = min ((-1) + (-1) - 1) 0 - min ((-1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-1) (3) (mem_raw_of_box k ((-1) + (-1)) (3) (by omega)) (mem_raw_of_box k (-1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-1) (3) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-1) + (-1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-1) (3) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) ((1), (3)) = min ((1) + (-1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (1) (3) (mem_raw_of_box k ((1) + (-1)) (3) (by omega)) (mem_raw_of_box k (1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (3) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (-1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (3) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((-2), (4)) = min ((-2) + (-1) - 1) 0 - min ((-2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-2) (4) (mem_raw_of_box k ((-2) + (-1)) (4) (by omega)) (mem_raw_of_box k (-2) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-2) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-2) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-2) (4) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) ((0), (4)) = min ((0) + (-1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (0) (4) (mem_raw_of_box k ((0) + (-1)) (4) (by omega)) (mem_raw_of_box k (0) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (4) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m1_4_p_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((-1), (4)) ≤ incr (reciprocalField k) (0, -1) ((-3), (4)) ∧
    incr (reciprocalField k) (0, -1) ((-1), (4)) - incr (reciprocalField k) (0, -1) ((-2), (5)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((-1), (4)) - incr (reciprocalField k) (0, -1) ((-4), (5)) ≤ -1 := by
  have hZ2_0 : incr (reciprocalField k) (0, -1) ((-3), (4)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 3), (5)) :=
    incr_eq_U k (0, -1) ((-3), (4)) (((2 * (k : ℤ) + 3) - 3), (5)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, -1) ((-4), (5)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 4), (6)) :=
    incr_eq_U k (0, -1) ((-4), (5)) (((2 * (k : ℤ) + 3) - 4), (6)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, -1) ((-1), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (-1) (4) (Or.inr rfl) (mem_raw_of_box k (-1) (4) (by omega)) (mem_raw_of_box k (-1) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 3), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 3) (5) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) (5) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((-2), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) (-2) (5) (Or.inr rfl) (mem_raw_of_box k (-2) (5) (by omega)) (mem_raw_of_box k (-2) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 4), (6)) = ((6)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 4) (6) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) (6) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) ((6) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m1_4_p_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((-1), (4)) ≤ incr (reciprocalField k) (0, 1) ((-3), (4)) ∧
    incr (reciprocalField k) (0, 1) ((-1), (4)) - incr (reciprocalField k) (0, 1) ((-2), (5)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((-1), (4)) - incr (reciprocalField k) (0, 1) ((-4), (5)) ≤ 1 := by
  have hZ4_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 5), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-4), (5)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 5), (4 - (2 * (k : ℤ) + 3))) ((-4), (5)) (by ext <;> (simp; try ring))
  have hZ4_1 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 5), (4 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((2 * (2 * (k : ℤ) + 3) + -5), (5 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (0, 1) (((2 * (k : ℤ) + 3) - 5), (4 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -5), (5 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, 1) ((-1), (4)) = -((4)) := by
    rw [incr_vert k 1 (-1) (4) (Or.inl rfl) (mem_raw_of_box k (-1) (4) (by omega)) (mem_raw_of_box k (-1) ((4) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((-3), (4)) = -((4)) := by
    rw [incr_vert k 1 (-3) (4) (Or.inl rfl) (mem_raw_of_box k (-3) (4) (by omega)) (mem_raw_of_box k (-3) ((4) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((-2), (5)) = -((5)) := by
    rw [incr_vert k 1 (-2) (5) (Or.inl rfl) (mem_raw_of_box k (-2) (5) (by omega)) (mem_raw_of_box k (-2) ((5) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((2 * (2 * (k : ℤ) + 3) + -5), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 (2 * (2 * (k : ℤ) + 3) + -5) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -5) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -5) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m1_4_m_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((-1), (4)) ≤ incr (reciprocalField k) (0, -1) ((1), (4)) ∧
    incr (reciprocalField k) (0, -1) ((-1), (4)) - incr (reciprocalField k) (0, -1) ((-2), (5)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((-1), (4)) - incr (reciprocalField k) (0, -1) ((0), (5)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((-1), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (-1) (4) (Or.inr rfl) (mem_raw_of_box k (-1) (4) (by omega)) (mem_raw_of_box k (-1) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((1), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (1) (4) (Or.inr rfl) (mem_raw_of_box k (1) (4) (by omega)) (mem_raw_of_box k (1) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((-2), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) (-2) (5) (Or.inr rfl) (mem_raw_of_box k (-2) (5) (by omega)) (mem_raw_of_box k (-2) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((0), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) (0) (5) (Or.inr rfl) (mem_raw_of_box k (0) (5) (by omega)) (mem_raw_of_box k (0) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m1_4_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((-1), (4)) ≤ incr (reciprocalField k) (0, 1) ((1), (4)) ∧
    incr (reciprocalField k) (0, 1) ((-1), (4)) - incr (reciprocalField k) (0, 1) ((-2), (5)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((-1), (4)) - incr (reciprocalField k) (0, 1) ((0), (5)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((-1), (4)) = -((4)) := by
    rw [incr_vert k 1 (-1) (4) (Or.inl rfl) (mem_raw_of_box k (-1) (4) (by omega)) (mem_raw_of_box k (-1) ((4) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((1), (4)) = -((4)) := by
    rw [incr_vert k 1 (1) (4) (Or.inl rfl) (mem_raw_of_box k (1) (4) (by omega)) (mem_raw_of_box k (1) ((4) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((-2), (5)) = -((5)) := by
    rw [incr_vert k 1 (-2) (5) (Or.inl rfl) (mem_raw_of_box k (-2) (5) (by omega)) (mem_raw_of_box k (-2) ((5) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((0), (5)) = -((5)) := by
    rw [incr_vert k 1 (0) (5) (Or.inl rfl) (mem_raw_of_box k (0) (5) (by omega)) (mem_raw_of_box k (0) ((5) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m1_5_p_mx (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (-1, 0) ((-1), (5)) ≤ incr (reciprocalField k) (-1, 0) ((-3), (5)) ∧
    incr (reciprocalField k) (-1, 0) ((-1), (5)) - incr (reciprocalField k) (-1, 0) ((-2), (6)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((-1), (5)) - incr (reciprocalField k) (-1, 0) ((-4), (6)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (-1, 0) ((-3), (5)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 3), (6)) :=
    incr_eq_U k (-1, 0) ((-3), (5)) (((2 * (k : ℤ) + 3) - 3), (6)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 5), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (-1, 0) ((-4), (6)) + ((2 * (k : ℤ) + 3) * 0 - -1) :=
    incr_eq_T k (-1, 0) (((2 * (k : ℤ) + 3) - 5), (5 - (2 * (k : ℤ) + 3))) ((-4), (6)) (by ext <;> (simp; try ring))
  have hZ4_1 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 5), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (-1, 0) ((2 * (2 * (k : ℤ) + 3) + -5), (6 - (2 * (k : ℤ) + 3))) :=
    incr_eq_U k (-1, 0) (((2 * (k : ℤ) + 3) - 5), (5 - (2 * (k : ℤ) + 3))) ((2 * (2 * (k : ℤ) + 3) + -5), (6 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (-1, 0) ((-1), (5)) = min ((-1) + (-1) - 1) 0 - min ((-1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-1) (5) (mem_raw_of_box k ((-1) + (-1)) (5) (by omega)) (mem_raw_of_box k (-1) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-1) (5) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-1) + (-1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-1) (5) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 3), (6)) = min (((2 * (k : ℤ) + 3) - 3) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 3) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 3) (6) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 3) + (-1)) (6) (by omega)) (mem_raw_corner2' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (6) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 3) + (-1)) (6) (by omega)) (corner_yes (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (6) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((-2), (6)) = min ((-2) + (-1) - 1) 0 - min ((-2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-2) (6) (mem_raw_of_box k ((-2) + (-1)) (6) (by omega)) (mem_raw_of_box k (-2) (6) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-2) (6) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-2) + (-1)) (6) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-2) (6) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) ((2 * (2 * (k : ℤ) + 3) + -5), (6 - (2 * (k : ℤ) + 3))) = min ((2 * (2 * (k : ℤ) + 3) + -5) + (-1) - 1) 0 - min ((2 * (2 * (k : ℤ) + 3) + -5) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (2 * (2 * (k : ℤ) + 3) + -5) (6 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k ((2 * (2 * (k : ℤ) + 3) + -5) + (-1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (2 * (k : ℤ) + 3) + -5) (6 - (2 * (k : ℤ) + 3)) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2 * (2 * (k : ℤ) + 3) + -5) (6 - (2 * (k : ℤ) + 3)) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (2 * (k : ℤ) + 3) + -5) + (-1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2 * (2 * (k : ℤ) + 3) + -5) (6 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m1_5_m_mx (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (-1, 0) ((-1), (5)) ≤ incr (reciprocalField k) (-1, 0) ((1), (5)) ∧
    incr (reciprocalField k) (-1, 0) ((-1), (5)) - incr (reciprocalField k) (-1, 0) ((-2), (6)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((-1), (5)) - incr (reciprocalField k) (-1, 0) ((0), (6)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (-1, 0) ((-1), (5)) = min ((-1) + (-1) - 1) 0 - min ((-1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-1) (5) (mem_raw_of_box k ((-1) + (-1)) (5) (by omega)) (mem_raw_of_box k (-1) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-1) (5) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-1) + (-1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-1) (5) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) ((1), (5)) = min ((1) + (-1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (1) (5) (mem_raw_of_box k ((1) + (-1)) (5) (by omega)) (mem_raw_of_box k (1) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (5) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (-1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (5) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((-2), (6)) = min ((-2) + (-1) - 1) 0 - min ((-2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-2) (6) (mem_raw_of_box k ((-2) + (-1)) (6) (by omega)) (mem_raw_of_box k (-2) (6) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-2) (6) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-2) + (-1)) (6) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-2) (6) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) ((0), (6)) = min ((0) + (-1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (0) (6) (mem_raw_of_box k ((0) + (-1)) (6) (by omega)) (mem_raw_of_box k (0) (6) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (6) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (-1)) (6) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (6) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m1_6_p_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((-1), (6)) ≤ incr (reciprocalField k) (0, 1) ((-3), (6)) ∧
    incr (reciprocalField k) (0, 1) ((-1), (6)) - incr (reciprocalField k) (0, 1) ((-2), (7)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((-1), (6)) - incr (reciprocalField k) (0, 1) ((-4), (7)) ≤ 1 := by
  have hZ1_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-1), (6)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) ((-1), (6)) (by ext <;> (simp; try ring))
  have hZ2_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 4), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-3), (6)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 4), (5 - (2 * (k : ℤ) + 3))) ((-3), (6)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 3), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-2), (7)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 3), (6 - (2 * (k : ℤ) + 3))) ((-2), (7)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 5), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-4), (7)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 5), (6 - (2 * (k : ℤ) + 3))) ((-4), (7)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 2) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 4), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 4) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 3), (6 - (2 * (k : ℤ) + 3))) = -((6 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 3) (6 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) ((6 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 5), (6 - (2 * (k : ℤ) + 3))) = -((6 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 5) (6 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 5) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 5) ((6 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_m1_6_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((-1), (6)) ≤ incr (reciprocalField k) (0, 1) ((1), (6)) ∧
    incr (reciprocalField k) (0, 1) ((-1), (6)) - incr (reciprocalField k) (0, 1) ((-2), (7)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((-1), (6)) - incr (reciprocalField k) (0, 1) ((0), (7)) ≤ 1 := by
  have hZ1_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-1), (6)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) ((-1), (6)) (by ext <;> (simp; try ring))
  have hZ2_0 : incr (reciprocalField k) (0, 1) ((2 * (k : ℤ) + 3), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((1), (6)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) ((2 * (k : ℤ) + 3), (5 - (2 * (k : ℤ) + 3))) ((1), (6)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 3), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-2), (7)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 3), (6 - (2 * (k : ℤ) + 3))) ((-2), (7)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 1), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((0), (7)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 1), (6 - (2 * (k : ℤ) + 3))) ((0), (7)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 2) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((2 * (k : ℤ) + 3), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (k : ℤ) + 3) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 3), (6 - (2 * (k : ℤ) + 3))) = -((6 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 3) (6 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) ((6 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 1), (6 - (2 * (k : ℤ) + 3))) = -((6 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 1) (6 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) ((6 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_0_0_p_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((0), (0)) ≤ incr (reciprocalField k) (1, 0) ((-2), (0)) ∧
    incr (reciprocalField k) (1, 0) ((0), (0)) - incr (reciprocalField k) (1, 0) ((-1), (1)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((0), (0)) - incr (reciprocalField k) (1, 0) ((-3), (1)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (1, 0) ((-2), (0)) = incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (1)) :=
    incr_eq_U k (1, 0) ((-2), (0)) (((2 * (k : ℤ) + 3) - 2), (1)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (1, 0) ((-1), (1)) = incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 1), (2)) :=
    incr_eq_U k (1, 0) ((-1), (1)) (((2 * (k : ℤ) + 3) - 1), (2)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (1, 0) ((-3), (1)) = incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 3), (2)) :=
    incr_eq_U k (1, 0) ((-3), (1)) (((2 * (k : ℤ) + 3) - 3), (2)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (1, 0) ((0), (0)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) (0) (0) (mem_raw_of_box k ((0) + (1)) (0) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (0) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (0) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (0) (0) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (1)) = min (((2 * (k : ℤ) + 3) - 2) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 2) (1) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 2) + (1)) (1) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 2) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (1) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 1), (2)) = min (((2 * (k : ℤ) + 3) - 1) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 1) (2) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 1) + (1)) (2) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 1) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (2) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 3), (2)) = min (((2 * (k : ℤ) + 3) - 3) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 3) (2) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 3) + (1)) (2) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 3) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (2) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_0_0_m_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((0), (0)) ≤ incr (reciprocalField k) (1, 0) ((2), (0)) ∧
    incr (reciprocalField k) (1, 0) ((0), (0)) - incr (reciprocalField k) (1, 0) ((-1), (1)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((0), (0)) - incr (reciprocalField k) (1, 0) ((1), (1)) ≤ 0 := by
  have hZ3_0 : incr (reciprocalField k) (1, 0) ((-1), (1)) = incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 1), (2)) :=
    incr_eq_U k (1, 0) ((-1), (1)) (((2 * (k : ℤ) + 3) - 1), (2)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (1, 0) ((0), (0)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) (0) (0) (mem_raw_of_box k ((0) + (1)) (0) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (0) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (0) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (0) (0) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((2), (0)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (0) (mem_raw_of_box k ((2) + (1)) (0) (by omega)) (mem_raw_of_box k (2) (0) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (0) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (0) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 1), (2)) = min (((2 * (k : ℤ) + 3) - 1) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 1) (2) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 1) + (1)) (2) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 1) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (2) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((1), (1)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (1) (mem_raw_of_box k ((1) + (1)) (1) (by omega)) (mem_raw_of_box k (1) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (1) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_0_1_p_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((0), (1)) ≤ incr (reciprocalField k) (0, -1) ((-2), (1)) ∧
    incr (reciprocalField k) (0, -1) ((0), (1)) - incr (reciprocalField k) (0, -1) ((-1), (2)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((0), (1)) - incr (reciprocalField k) (0, -1) ((-3), (2)) ≤ -1 := by
  have hZ2_0 : incr (reciprocalField k) (0, -1) ((-2), (1)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (2)) :=
    incr_eq_U k (0, -1) ((-2), (1)) (((2 * (k : ℤ) + 3) - 2), (2)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (0, -1) ((-1), (2)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 1), (3)) :=
    incr_eq_U k (0, -1) ((-1), (2)) (((2 * (k : ℤ) + 3) - 1), (3)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, -1) ((-3), (2)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 3), (3)) :=
    incr_eq_U k (0, -1) ((-3), (2)) (((2 * (k : ℤ) + 3) - 3), (3)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, -1) ((0), (1)) = 1 := by
    rw [show ((0), (1)) = ((0 : ℤ), (1 : ℤ)) from by ext <;> omega]
    exact incr_c0_fromdown k
  have vZ2 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 2) (2) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (2) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 1), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 1) (3) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (3) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 3), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 3) (3) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) (3) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_0_1_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((0), (1)) ≤ incr (reciprocalField k) (0, 1) ((2), (1)) ∧
    incr (reciprocalField k) (0, 1) ((0), (1)) - incr (reciprocalField k) (0, 1) ((-1), (2)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((0), (1)) - incr (reciprocalField k) (0, 1) ((1), (2)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((0), (1)) = -((1)) := by
    rw [incr_vert k 1 (0) (1) (Or.inl rfl) (mem_raw_of_box k (0) (1) (by omega)) (mem_raw_of_box k (0) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((2), (1)) = -((1)) := by
    rw [incr_vert k 1 (2) (1) (Or.inl rfl) (mem_raw_of_box k (2) (1) (by omega)) (mem_raw_of_box k (2) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((-1), (2)) = -((2)) := by
    rw [incr_vert k 1 (-1) (2) (Or.inl rfl) (mem_raw_of_box k (-1) (2) (by omega)) (mem_raw_of_box k (-1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((1), (2)) = -((2)) := by
    rw [incr_vert k 1 (1) (2) (Or.inl rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_0_2_p_mx (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (-1, 0) ((0), (2)) ≤ incr (reciprocalField k) (-1, 0) ((-2), (2)) ∧
    incr (reciprocalField k) (-1, 0) ((0), (2)) - incr (reciprocalField k) (-1, 0) ((-1), (3)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((0), (2)) - incr (reciprocalField k) (-1, 0) ((-3), (3)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (-1, 0) ((-2), (2)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 2), (3)) :=
    incr_eq_U k (-1, 0) ((-2), (2)) (((2 * (k : ℤ) + 3) - 2), (3)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (-1, 0) ((-3), (3)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 3), (4)) :=
    incr_eq_U k (-1, 0) ((-3), (3)) (((2 * (k : ℤ) + 3) - 3), (4)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (-1, 0) ((0), (2)) = min ((0) + (-1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (0) (2) (mem_raw_of_box k ((0) + (-1)) (2) (by omega)) (mem_raw_of_box k (0) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (2) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (-1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (2) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 2), (3)) = min (((2 * (k : ℤ) + 3) - 2) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 2) (3) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 2) + (-1)) (3) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (3) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 2) + (-1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (3) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((-1), (3)) = min ((-1) + (-1) - 1) 0 - min ((-1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-1) (3) (mem_raw_of_box k ((-1) + (-1)) (3) (by omega)) (mem_raw_of_box k (-1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-1) (3) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-1) + (-1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-1) (3) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 3), (4)) = min (((2 * (k : ℤ) + 3) - 3) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 3) (4) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 3) + (-1)) (4) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 3) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (4) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_0_2_m_mx (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (-1, 0) ((0), (2)) ≤ incr (reciprocalField k) (-1, 0) ((2), (2)) ∧
    incr (reciprocalField k) (-1, 0) ((0), (2)) - incr (reciprocalField k) (-1, 0) ((-1), (3)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((0), (2)) - incr (reciprocalField k) (-1, 0) ((1), (3)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (-1, 0) ((0), (2)) = min ((0) + (-1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (0) (2) (mem_raw_of_box k ((0) + (-1)) (2) (by omega)) (mem_raw_of_box k (0) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (2) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (-1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (2) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) ((2), (2)) = min ((2) + (-1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (2) (2) (mem_raw_of_box k ((2) + (-1)) (2) (by omega)) (mem_raw_of_box k (2) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (2) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (-1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (2) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((-1), (3)) = min ((-1) + (-1) - 1) 0 - min ((-1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-1) (3) (mem_raw_of_box k ((-1) + (-1)) (3) (by omega)) (mem_raw_of_box k (-1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-1) (3) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-1) + (-1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-1) (3) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) ((1), (3)) = min ((1) + (-1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (1) (3) (mem_raw_of_box k ((1) + (-1)) (3) (by omega)) (mem_raw_of_box k (1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (3) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (-1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (3) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_0_3_p_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((0), (3)) ≤ incr (reciprocalField k) (0, -1) ((-2), (3)) ∧
    incr (reciprocalField k) (0, -1) ((0), (3)) - incr (reciprocalField k) (0, -1) ((-1), (4)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((0), (3)) - incr (reciprocalField k) (0, -1) ((-3), (4)) ≤ -1 := by
  have hZ2_0 : incr (reciprocalField k) (0, -1) ((-2), (3)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (4)) :=
    incr_eq_U k (0, -1) ((-2), (3)) (((2 * (k : ℤ) + 3) - 2), (4)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, -1) ((-3), (4)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 3), (5)) :=
    incr_eq_U k (0, -1) ((-3), (4)) (((2 * (k : ℤ) + 3) - 3), (5)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, -1) ((0), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (0) (3) (Or.inr rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 2) (4) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (4) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((-1), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (-1) (4) (Or.inr rfl) (mem_raw_of_box k (-1) (4) (by omega)) (mem_raw_of_box k (-1) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 3), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 3) (5) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) (5) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_0_3_p_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((0), (3)) ≤ incr (reciprocalField k) (0, 1) ((-2), (3)) ∧
    incr (reciprocalField k) (0, 1) ((0), (3)) - incr (reciprocalField k) (0, 1) ((-1), (4)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((0), (3)) - incr (reciprocalField k) (0, 1) ((-3), (4)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((0), (3)) = -((3)) := by
    rw [incr_vert k 1 (0) (3) (Or.inl rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((-2), (3)) = -((3)) := by
    rw [incr_vert k 1 (-2) (3) (Or.inl rfl) (mem_raw_of_box k (-2) (3) (by omega)) (mem_raw_of_box k (-2) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((-1), (4)) = -((4)) := by
    rw [incr_vert k 1 (-1) (4) (Or.inl rfl) (mem_raw_of_box k (-1) (4) (by omega)) (mem_raw_of_box k (-1) ((4) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((-3), (4)) = -((4)) := by
    rw [incr_vert k 1 (-3) (4) (Or.inl rfl) (mem_raw_of_box k (-3) (4) (by omega)) (mem_raw_of_box k (-3) ((4) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_0_3_m_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((0), (3)) ≤ incr (reciprocalField k) (0, -1) ((2), (3)) ∧
    incr (reciprocalField k) (0, -1) ((0), (3)) - incr (reciprocalField k) (0, -1) ((-1), (4)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((0), (3)) - incr (reciprocalField k) (0, -1) ((1), (4)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((0), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (0) (3) (Or.inr rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((2), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (2) (3) (Or.inr rfl) (mem_raw_of_box k (2) (3) (by omega)) (mem_raw_of_box k (2) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((-1), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (-1) (4) (Or.inr rfl) (mem_raw_of_box k (-1) (4) (by omega)) (mem_raw_of_box k (-1) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((1), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (1) (4) (Or.inr rfl) (mem_raw_of_box k (1) (4) (by omega)) (mem_raw_of_box k (1) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_0_3_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((0), (3)) ≤ incr (reciprocalField k) (0, 1) ((2), (3)) ∧
    incr (reciprocalField k) (0, 1) ((0), (3)) - incr (reciprocalField k) (0, 1) ((-1), (4)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((0), (3)) - incr (reciprocalField k) (0, 1) ((1), (4)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((0), (3)) = -((3)) := by
    rw [incr_vert k 1 (0) (3) (Or.inl rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((2), (3)) = -((3)) := by
    rw [incr_vert k 1 (2) (3) (Or.inl rfl) (mem_raw_of_box k (2) (3) (by omega)) (mem_raw_of_box k (2) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((-1), (4)) = -((4)) := by
    rw [incr_vert k 1 (-1) (4) (Or.inl rfl) (mem_raw_of_box k (-1) (4) (by omega)) (mem_raw_of_box k (-1) ((4) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((1), (4)) = -((4)) := by
    rw [incr_vert k 1 (1) (4) (Or.inl rfl) (mem_raw_of_box k (1) (4) (by omega)) (mem_raw_of_box k (1) ((4) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_0_4_p_mx (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (-1, 0) ((0), (4)) ≤ incr (reciprocalField k) (-1, 0) ((-2), (4)) ∧
    incr (reciprocalField k) (-1, 0) ((0), (4)) - incr (reciprocalField k) (-1, 0) ((-1), (5)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((0), (4)) - incr (reciprocalField k) (-1, 0) ((-3), (5)) ≤ 0 := by
  have hZ4_0 : incr (reciprocalField k) (-1, 0) ((-3), (5)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 3), (6)) :=
    incr_eq_U k (-1, 0) ((-3), (5)) (((2 * (k : ℤ) + 3) - 3), (6)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (-1, 0) ((0), (4)) = min ((0) + (-1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (0) (4) (mem_raw_of_box k ((0) + (-1)) (4) (by omega)) (mem_raw_of_box k (0) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (4) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) ((-2), (4)) = min ((-2) + (-1) - 1) 0 - min ((-2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-2) (4) (mem_raw_of_box k ((-2) + (-1)) (4) (by omega)) (mem_raw_of_box k (-2) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-2) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-2) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-2) (4) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((-1), (5)) = min ((-1) + (-1) - 1) 0 - min ((-1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-1) (5) (mem_raw_of_box k ((-1) + (-1)) (5) (by omega)) (mem_raw_of_box k (-1) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-1) (5) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-1) + (-1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-1) (5) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 3), (6)) = min (((2 * (k : ℤ) + 3) - 3) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 3) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 3) (6) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 3) + (-1)) (6) (by omega)) (mem_raw_corner2' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (6) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 3) + (-1)) (6) (by omega)) (corner_yes (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 3) (6) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_0_4_m_mx (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (-1, 0) ((0), (4)) ≤ incr (reciprocalField k) (-1, 0) ((2), (4)) ∧
    incr (reciprocalField k) (-1, 0) ((0), (4)) - incr (reciprocalField k) (-1, 0) ((-1), (5)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((0), (4)) - incr (reciprocalField k) (-1, 0) ((1), (5)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (-1, 0) ((0), (4)) = min ((0) + (-1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (0) (4) (mem_raw_of_box k ((0) + (-1)) (4) (by omega)) (mem_raw_of_box k (0) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (4) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) ((2), (4)) = min ((2) + (-1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (2) (4) (mem_raw_of_box k ((2) + (-1)) (4) (by omega)) (mem_raw_of_box k (2) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (4) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((-1), (5)) = min ((-1) + (-1) - 1) 0 - min ((-1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-1) (5) (mem_raw_of_box k ((-1) + (-1)) (5) (by omega)) (mem_raw_of_box k (-1) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-1) (5) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-1) + (-1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-1) (5) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) ((1), (5)) = min ((1) + (-1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (1) (5) (mem_raw_of_box k ((1) + (-1)) (5) (by omega)) (mem_raw_of_box k (1) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (5) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (-1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (5) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_0_5_p_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((0), (5)) ≤ incr (reciprocalField k) (0, -1) ((-2), (5)) ∧
    incr (reciprocalField k) (0, -1) ((0), (5)) - incr (reciprocalField k) (0, -1) ((-1), (6)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((0), (5)) - incr (reciprocalField k) (0, -1) ((-3), (6)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((0), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) (0) (5) (Or.inr rfl) (mem_raw_of_box k (0) (5) (by omega)) (mem_raw_of_box k (0) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((-2), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) (-2) (5) (Or.inr rfl) (mem_raw_of_box k (-2) (5) (by omega)) (mem_raw_of_box k (-2) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((-1), (6)) = ((6)) + -1 := by
    rw [incr_vert k (-1) (-1) (6) (Or.inr rfl) (mem_raw_of_box k (-1) (6) (by omega)) (mem_raw_of_box k (-1) ((6) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((-3), (6)) = ((6)) + -1 := by
    rw [incr_vert k (-1) (-3) (6) (Or.inr rfl) (mem_raw_of_box k (-3) (6) (by omega)) (mem_raw_of_box k (-3) ((6) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_0_5_p_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((0), (5)) ≤ incr (reciprocalField k) (0, 1) ((-2), (5)) ∧
    incr (reciprocalField k) (0, 1) ((0), (5)) - incr (reciprocalField k) (0, 1) ((-1), (6)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((0), (5)) - incr (reciprocalField k) (0, 1) ((-3), (6)) ≤ 1 := by
  have hZ3_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-1), (6)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) ((-1), (6)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 4), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-3), (6)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 4), (5 - (2 * (k : ℤ) + 3))) ((-3), (6)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, 1) ((0), (5)) = -((5)) := by
    rw [incr_vert k 1 (0) (5) (Or.inl rfl) (mem_raw_of_box k (0) (5) (by omega)) (mem_raw_of_box k (0) ((5) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((-2), (5)) = -((5)) := by
    rw [incr_vert k 1 (-2) (5) (Or.inl rfl) (mem_raw_of_box k (-2) (5) (by omega)) (mem_raw_of_box k (-2) ((5) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 2) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 4), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 4) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_0_5_m_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((0), (5)) ≤ incr (reciprocalField k) (0, -1) ((2), (5)) ∧
    incr (reciprocalField k) (0, -1) ((0), (5)) - incr (reciprocalField k) (0, -1) ((-1), (6)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((0), (5)) - incr (reciprocalField k) (0, -1) ((1), (6)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((0), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) (0) (5) (Or.inr rfl) (mem_raw_of_box k (0) (5) (by omega)) (mem_raw_of_box k (0) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((2), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) (2) (5) (Or.inr rfl) (mem_raw_of_box k (2) (5) (by omega)) (mem_raw_of_box k (2) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((-1), (6)) = ((6)) + -1 := by
    rw [incr_vert k (-1) (-1) (6) (Or.inr rfl) (mem_raw_of_box k (-1) (6) (by omega)) (mem_raw_of_box k (-1) ((6) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((1), (6)) = ((6)) + -1 := by
    rw [incr_vert k (-1) (1) (6) (Or.inr rfl) (mem_raw_of_box k (1) (6) (by omega)) (mem_raw_of_box k (1) ((6) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_0_5_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((0), (5)) ≤ incr (reciprocalField k) (0, 1) ((2), (5)) ∧
    incr (reciprocalField k) (0, 1) ((0), (5)) - incr (reciprocalField k) (0, 1) ((-1), (6)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((0), (5)) - incr (reciprocalField k) (0, 1) ((1), (6)) ≤ 1 := by
  have hZ3_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-1), (6)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) ((-1), (6)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, 1) ((2 * (k : ℤ) + 3), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((1), (6)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) ((2 * (k : ℤ) + 3), (5 - (2 * (k : ℤ) + 3))) ((1), (6)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, 1) ((0), (5)) = -((5)) := by
    rw [incr_vert k 1 (0) (5) (Or.inl rfl) (mem_raw_of_box k (0) (5) (by omega)) (mem_raw_of_box k (0) ((5) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((2), (5)) = 1 - (2 * (k : ℤ) + 3) := by
    rw [show ((2), (5)) = ((2 : ℤ), 2 * (k : ℤ) + 3) from by ext <;> omega]
    exact incr_c2low_up k
  have vZ3 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 2) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((2 * (k : ℤ) + 3), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (k : ℤ) + 3) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_0_6_p_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((0), (6)) ≤ incr (reciprocalField k) (1, 0) ((-2), (6)) ∧
    incr (reciprocalField k) (1, 0) ((0), (6)) - incr (reciprocalField k) (1, 0) ((-1), (7)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((0), (6)) - incr (reciprocalField k) (1, 0) ((-3), (7)) ≤ 0 := by
  have hZ3_0 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((-1), (7)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) (((2 * (k : ℤ) + 3) - 2), (6 - (2 * (k : ℤ) + 3))) ((-1), (7)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 4), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((-3), (7)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) (((2 * (k : ℤ) + 3) - 4), (6 - (2 * (k : ℤ) + 3))) ((-3), (7)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (1, 0) ((0), (6)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (6) (mem_raw_of_box k ((0) + (1)) (6) (by omega)) (mem_raw_of_box k (0) (6) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (6) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (6) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (6) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((-2), (6)) = min ((-2) + (1) - 1) 0 - min ((-2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (-2) (6) (mem_raw_of_box k ((-2) + (1)) (6) (by omega)) (mem_raw_of_box k (-2) (6) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-2) (6) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((-2) + (1)) (6) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-2) (6) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (6 - (2 * (k : ℤ) + 3))) = min (((2 * (k : ℤ) + 3) - 2) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 2) (6 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 2) + (1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (6 - (2 * (k : ℤ) + 3)) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (6 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 2) + (1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (6 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 4), (6 - (2 * (k : ℤ) + 3))) = min (((2 * (k : ℤ) + 3) - 4) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 4) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 4) (6 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 4) + (1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 4) (6 - (2 * (k : ℤ) + 3)) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 4) (6 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 4) + (1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 4) (6 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_0_6_m_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((0), (6)) ≤ incr (reciprocalField k) (1, 0) ((2), (6)) ∧
    incr (reciprocalField k) (1, 0) ((0), (6)) - incr (reciprocalField k) (1, 0) ((-1), (7)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((0), (6)) - incr (reciprocalField k) (1, 0) ((1), (7)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (1, 0) ((2), (6)) = incr (reciprocalField k) (1, 0) ((2 - (2 * (k : ℤ) + 3)), (5)) :=
    (incr_eq_U k (1, 0) ((2 - (2 * (k : ℤ) + 3)), (5)) ((2), (6)) (by ext <;> (simp; try ring))).symm
  have hZ3_0 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((-1), (7)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) (((2 * (k : ℤ) + 3) - 2), (6 - (2 * (k : ℤ) + 3))) ((-1), (7)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (1, 0) ((2 * (k : ℤ) + 3), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((1), (7)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) ((2 * (k : ℤ) + 3), (6 - (2 * (k : ℤ) + 3))) ((1), (7)) (by ext <;> (simp; try ring))
  have hZ4_1 : incr (reciprocalField k) (1, 0) ((2 * (k : ℤ) + 3), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((0), (5 - (2 * (k : ℤ) + 3))) :=
    (incr_eq_U k (1, 0) ((0), (5 - (2 * (k : ℤ) + 3))) ((2 * (k : ℤ) + 3), (6 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (1, 0) ((0), (6)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (6) (mem_raw_of_box k ((0) + (1)) (6) (by omega)) (mem_raw_of_box k (0) (6) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (6) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (6) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (6) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((2 - (2 * (k : ℤ) + 3)), (5)) = min ((2 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((2 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2 - (2 * (k : ℤ) + 3)) (5) (mem_raw_of_box k ((2 - (2 * (k : ℤ) + 3)) + (1)) (5) (by omega)) (mem_raw_of_box k (2 - (2 * (k : ℤ) + 3)) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2 - (2 * (k : ℤ) + 3)) (5) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2 - (2 * (k : ℤ) + 3)) + (1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2 - (2 * (k : ℤ) + 3)) (5) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (6 - (2 * (k : ℤ) + 3))) = min (((2 * (k : ℤ) + 3) - 2) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 2) (6 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 2) + (1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (6 - (2 * (k : ℤ) + 3)) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (6 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 2) + (1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (6 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((0), (5 - (2 * (k : ℤ) + 3))) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) (0) (5 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k ((0) + (1)) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (0) (5 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (5 - (2 * (k : ℤ) + 3)) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (0) (5 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_0_p_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((1), (0)) ≤ incr (reciprocalField k) (0, -1) ((-1), (0)) ∧
    incr (reciprocalField k) (0, -1) ((1), (0)) - incr (reciprocalField k) (0, -1) ((0), (1)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((1), (0)) - incr (reciprocalField k) (0, -1) ((-2), (1)) ≤ -1 := by
  have hZ1_0 : incr (reciprocalField k) (0, -1) ((1), (0)) = incr (reciprocalField k) (0, -1) ((2 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) + ((2 * (k : ℤ) + 3) * -1 - 0) :=
    incr_eq_T k (0, -1) ((1), (0)) ((2 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) (by ext <;> (simp; try ring))
  have hZ2_0 : incr (reciprocalField k) (0, -1) ((-1), (0)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 1), (1)) :=
    incr_eq_U k (0, -1) ((-1), (0)) (((2 * (k : ℤ) + 3) - 1), (1)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, -1) ((-2), (1)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (2)) :=
    incr_eq_U k (0, -1) ((-2), (1)) (((2 * (k : ℤ) + 3) - 2), (2)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, -1) ((2 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) = (((2 * (k : ℤ) + 3) + 1)) + -1 := by
    rw [incr_vert k (-1) (2 - (2 * (k : ℤ) + 3)) ((2 * (k : ℤ) + 3) + 1) (Or.inr rfl) (mem_raw_of_box k (2 - (2 * (k : ℤ) + 3)) ((2 * (k : ℤ) + 3) + 1) (by omega)) (mem_raw_of_box k (2 - (2 * (k : ℤ) + 3)) (((2 * (k : ℤ) + 3) + 1) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 1), (1)) = ((1)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 1) (1) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (1) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) ((1) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((0), (1)) = 1 := by
    rw [show ((0), (1)) = ((0 : ℤ), (1 : ℤ)) from by ext <;> omega]
    exact incr_c0_fromdown k
  have vZ4 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 2) (2) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (2) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_0_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((1), (0)) ≤ incr (reciprocalField k) (0, 1) ((3), (0)) ∧
    incr (reciprocalField k) (0, 1) ((1), (0)) - incr (reciprocalField k) (0, 1) ((0), (1)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((1), (0)) - incr (reciprocalField k) (0, 1) ((2), (1)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((1), (0)) = -((0)) := by
    rw [incr_vert k 1 (1) (0) (Or.inl rfl) (mem_raw_of_box k (1) (0) (by omega)) (mem_raw_of_box k (1) ((0) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((3), (0)) = -((0)) := by
    rw [incr_vert k 1 (3) (0) (Or.inl rfl) (mem_raw_of_box k (3) (0) (by omega)) (mem_raw_of_box k (3) ((0) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((0), (1)) = -((1)) := by
    rw [incr_vert k 1 (0) (1) (Or.inl rfl) (mem_raw_of_box k (0) (1) (by omega)) (mem_raw_of_box k (0) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((2), (1)) = -((1)) := by
    rw [incr_vert k 1 (2) (1) (Or.inl rfl) (mem_raw_of_box k (2) (1) (by omega)) (mem_raw_of_box k (2) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_1_p_mx (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (-1, 0) ((1), (1)) ≤ incr (reciprocalField k) (-1, 0) ((-1), (1)) ∧
    incr (reciprocalField k) (-1, 0) ((1), (1)) - incr (reciprocalField k) (-1, 0) ((0), (2)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((1), (1)) - incr (reciprocalField k) (-1, 0) ((-2), (2)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (-1, 0) ((-1), (1)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 1), (2)) :=
    incr_eq_U k (-1, 0) ((-1), (1)) (((2 * (k : ℤ) + 3) - 1), (2)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (-1, 0) ((-2), (2)) = incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 2), (3)) :=
    incr_eq_U k (-1, 0) ((-2), (2)) (((2 * (k : ℤ) + 3) - 2), (3)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (-1, 0) ((1), (1)) = min ((1) + (-1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (1) (1) (mem_raw_of_box k ((1) + (-1)) (1) (by omega)) (mem_raw_of_box k (1) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (1) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (-1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (1) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 1), (2)) = min (((2 * (k : ℤ) + 3) - 1) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 1) (2) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 1) + (-1)) (2) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (2) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 1) + (-1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (2) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((0), (2)) = min ((0) + (-1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (0) (2) (mem_raw_of_box k ((0) + (-1)) (2) (by omega)) (mem_raw_of_box k (0) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (2) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (-1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (2) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) (((2 * (k : ℤ) + 3) - 2), (3)) = min (((2 * (k : ℤ) + 3) - 2) + (-1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) ((2 * (k : ℤ) + 3) - 2) (3) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 2) + (-1)) (3) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (3) (-1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 2) + (-1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (3) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_1_p_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((1), (1)) ≤ incr (reciprocalField k) (1, 0) ((-1), (1)) ∧
    incr (reciprocalField k) (1, 0) ((1), (1)) - incr (reciprocalField k) (1, 0) ((0), (2)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((1), (1)) - incr (reciprocalField k) (1, 0) ((-2), (2)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (1, 0) ((-1), (1)) = incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 1), (2)) :=
    incr_eq_U k (1, 0) ((-1), (1)) (((2 * (k : ℤ) + 3) - 1), (2)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (1, 0) ((-2), (2)) = incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (3)) :=
    incr_eq_U k (1, 0) ((-2), (2)) (((2 * (k : ℤ) + 3) - 2), (3)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (1, 0) ((1), (1)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (1) (mem_raw_of_box k ((1) + (1)) (1) (by omega)) (mem_raw_of_box k (1) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (1) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 1), (2)) = min (((2 * (k : ℤ) + 3) - 1) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 1) (2) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 1) + (1)) (2) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 1) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (2) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((0), (2)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (2) (mem_raw_of_box k ((0) + (1)) (2) (by omega)) (mem_raw_of_box k (0) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (2) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (3)) = min (((2 * (k : ℤ) + 3) - 2) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 2) (3) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 2) + (1)) (3) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 2) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (3) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_1_m_mx (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (-1, 0) ((1), (1)) ≤ incr (reciprocalField k) (-1, 0) ((3), (1)) ∧
    incr (reciprocalField k) (-1, 0) ((1), (1)) - incr (reciprocalField k) (-1, 0) ((0), (2)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((1), (1)) - incr (reciprocalField k) (-1, 0) ((2), (2)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (-1, 0) ((1), (1)) = min ((1) + (-1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (1) (1) (mem_raw_of_box k ((1) + (-1)) (1) (by omega)) (mem_raw_of_box k (1) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (1) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (-1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (1) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) ((3), (1)) = min ((3) + (-1) - 1) 0 - min ((3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (3) (1) (mem_raw_of_box k ((3) + (-1)) (1) (by omega)) (mem_raw_of_box k (3) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3) (1) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((3) + (-1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3) (1) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((0), (2)) = min ((0) + (-1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (0) (2) (mem_raw_of_box k ((0) + (-1)) (2) (by omega)) (mem_raw_of_box k (0) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (2) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (-1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (2) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) ((2), (2)) = min ((2) + (-1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (2) (2) (mem_raw_of_box k ((2) + (-1)) (2) (by omega)) (mem_raw_of_box k (2) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (2) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (-1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (2) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_1_m_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((1), (1)) ≤ incr (reciprocalField k) (1, 0) ((3), (1)) ∧
    incr (reciprocalField k) (1, 0) ((1), (1)) - incr (reciprocalField k) (1, 0) ((0), (2)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((1), (1)) - incr (reciprocalField k) (1, 0) ((2), (2)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (1, 0) ((1), (1)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (1) (mem_raw_of_box k ((1) + (1)) (1) (by omega)) (mem_raw_of_box k (1) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (1) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((3), (1)) = min ((3) + (1) - 1) 0 - min ((3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (3) (1) (mem_raw_of_box k ((3) + (1)) (1) (by omega)) (mem_raw_of_box k (3) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3) (1) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((0), (2)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (2) (mem_raw_of_box k ((0) + (1)) (2) (by omega)) (mem_raw_of_box k (0) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (2) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((2), (2)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (2) (mem_raw_of_box k ((2) + (1)) (2) (by omega)) (mem_raw_of_box k (2) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (2) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_2_p_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((1), (2)) ≤ incr (reciprocalField k) (0, -1) ((-1), (2)) ∧
    incr (reciprocalField k) (0, -1) ((1), (2)) - incr (reciprocalField k) (0, -1) ((0), (3)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((1), (2)) - incr (reciprocalField k) (0, -1) ((-2), (3)) ≤ -1 := by
  have hZ2_0 : incr (reciprocalField k) (0, -1) ((-1), (2)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 1), (3)) :=
    incr_eq_U k (0, -1) ((-1), (2)) (((2 * (k : ℤ) + 3) - 1), (3)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, -1) ((-2), (3)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (4)) :=
    incr_eq_U k (0, -1) ((-2), (3)) (((2 * (k : ℤ) + 3) - 2), (4)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, -1) ((1), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (1) (2) (Or.inr rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 1), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 1) (3) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (3) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((0), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (0) (3) (Or.inr rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 2), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 2) (4) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (4) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_2_p_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((1), (2)) ≤ incr (reciprocalField k) (0, 1) ((-1), (2)) ∧
    incr (reciprocalField k) (0, 1) ((1), (2)) - incr (reciprocalField k) (0, 1) ((0), (3)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((1), (2)) - incr (reciprocalField k) (0, 1) ((-2), (3)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((1), (2)) = -((2)) := by
    rw [incr_vert k 1 (1) (2) (Or.inl rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((-1), (2)) = -((2)) := by
    rw [incr_vert k 1 (-1) (2) (Or.inl rfl) (mem_raw_of_box k (-1) (2) (by omega)) (mem_raw_of_box k (-1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((0), (3)) = -((3)) := by
    rw [incr_vert k 1 (0) (3) (Or.inl rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((-2), (3)) = -((3)) := by
    rw [incr_vert k 1 (-2) (3) (Or.inl rfl) (mem_raw_of_box k (-2) (3) (by omega)) (mem_raw_of_box k (-2) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_2_m_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((1), (2)) ≤ incr (reciprocalField k) (0, -1) ((3), (2)) ∧
    incr (reciprocalField k) (0, -1) ((1), (2)) - incr (reciprocalField k) (0, -1) ((0), (3)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((1), (2)) - incr (reciprocalField k) (0, -1) ((2), (3)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((1), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (1) (2) (Or.inr rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((3), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (3) (2) (Or.inr rfl) (mem_raw_of_box k (3) (2) (by omega)) (mem_raw_of_box k (3) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((0), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (0) (3) (Or.inr rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((2), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (2) (3) (Or.inr rfl) (mem_raw_of_box k (2) (3) (by omega)) (mem_raw_of_box k (2) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_2_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((1), (2)) ≤ incr (reciprocalField k) (0, 1) ((3), (2)) ∧
    incr (reciprocalField k) (0, 1) ((1), (2)) - incr (reciprocalField k) (0, 1) ((0), (3)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((1), (2)) - incr (reciprocalField k) (0, 1) ((2), (3)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((1), (2)) = -((2)) := by
    rw [incr_vert k 1 (1) (2) (Or.inl rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((3), (2)) = -((2)) := by
    rw [incr_vert k 1 (3) (2) (Or.inl rfl) (mem_raw_of_box k (3) (2) (by omega)) (mem_raw_of_box k (3) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((0), (3)) = -((3)) := by
    rw [incr_vert k 1 (0) (3) (Or.inl rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((2), (3)) = -((3)) := by
    rw [incr_vert k 1 (2) (3) (Or.inl rfl) (mem_raw_of_box k (2) (3) (by omega)) (mem_raw_of_box k (2) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_3_p_mx (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (-1, 0) ((1), (3)) ≤ incr (reciprocalField k) (-1, 0) ((-1), (3)) ∧
    incr (reciprocalField k) (-1, 0) ((1), (3)) - incr (reciprocalField k) (-1, 0) ((0), (4)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((1), (3)) - incr (reciprocalField k) (-1, 0) ((-2), (4)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (-1, 0) ((1), (3)) = min ((1) + (-1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (1) (3) (mem_raw_of_box k ((1) + (-1)) (3) (by omega)) (mem_raw_of_box k (1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (3) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (-1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (3) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) ((-1), (3)) = min ((-1) + (-1) - 1) 0 - min ((-1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-1) (3) (mem_raw_of_box k ((-1) + (-1)) (3) (by omega)) (mem_raw_of_box k (-1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-1) (3) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-1) + (-1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-1) (3) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((0), (4)) = min ((0) + (-1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (0) (4) (mem_raw_of_box k ((0) + (-1)) (4) (by omega)) (mem_raw_of_box k (0) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (4) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) ((-2), (4)) = min ((-2) + (-1) - 1) 0 - min ((-2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-2) (4) (mem_raw_of_box k ((-2) + (-1)) (4) (by omega)) (mem_raw_of_box k (-2) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-2) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-2) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-2) (4) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_3_p_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((1), (3)) ≤ incr (reciprocalField k) (1, 0) ((-1), (3)) ∧
    incr (reciprocalField k) (1, 0) ((1), (3)) - incr (reciprocalField k) (1, 0) ((0), (4)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((1), (3)) - incr (reciprocalField k) (1, 0) ((-2), (4)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (1, 0) ((1), (3)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (3) (mem_raw_of_box k ((1) + (1)) (3) (by omega)) (mem_raw_of_box k (1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (3) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((-1), (3)) = min ((-1) + (1) - 1) 0 - min ((-1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (-1) (3) (mem_raw_of_box k ((-1) + (1)) (3) (by omega)) (mem_raw_of_box k (-1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-1) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((-1) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-1) (3) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((0), (4)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (4) (mem_raw_of_box k ((0) + (1)) (4) (by omega)) (mem_raw_of_box k (0) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (4) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (4) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((-2), (4)) = min ((-2) + (1) - 1) 0 - min ((-2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (-2) (4) (mem_raw_of_box k ((-2) + (1)) (4) (by omega)) (mem_raw_of_box k (-2) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-2) (4) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((-2) + (1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-2) (4) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_3_m_mx (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (-1, 0) ((1), (3)) ≤ incr (reciprocalField k) (-1, 0) ((3), (3)) ∧
    incr (reciprocalField k) (-1, 0) ((1), (3)) - incr (reciprocalField k) (-1, 0) ((0), (4)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((1), (3)) - incr (reciprocalField k) (-1, 0) ((2), (4)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (-1, 0) ((1), (3)) = min ((1) + (-1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (1) (3) (mem_raw_of_box k ((1) + (-1)) (3) (by omega)) (mem_raw_of_box k (1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (3) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (-1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (3) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) ((3), (3)) = min ((3) + (-1) - 1) 0 - min ((3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (3) (3) (mem_raw_of_box k ((3) + (-1)) (3) (by omega)) (mem_raw_of_box k (3) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3) (3) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((3) + (-1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3) (3) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((0), (4)) = min ((0) + (-1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (0) (4) (mem_raw_of_box k ((0) + (-1)) (4) (by omega)) (mem_raw_of_box k (0) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (4) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) ((2), (4)) = min ((2) + (-1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (2) (4) (mem_raw_of_box k ((2) + (-1)) (4) (by omega)) (mem_raw_of_box k (2) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (4) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_3_m_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((1), (3)) ≤ incr (reciprocalField k) (1, 0) ((3), (3)) ∧
    incr (reciprocalField k) (1, 0) ((1), (3)) - incr (reciprocalField k) (1, 0) ((0), (4)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((1), (3)) - incr (reciprocalField k) (1, 0) ((2), (4)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (1, 0) ((1), (3)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (3) (mem_raw_of_box k ((1) + (1)) (3) (by omega)) (mem_raw_of_box k (1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (3) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((3), (3)) = min ((3) + (1) - 1) 0 - min ((3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (3) (3) (mem_raw_of_box k ((3) + (1)) (3) (by omega)) (mem_raw_of_box k (3) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3) (3) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((0), (4)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (4) (mem_raw_of_box k ((0) + (1)) (4) (by omega)) (mem_raw_of_box k (0) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (4) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (4) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((2), (4)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (4) (mem_raw_of_box k ((2) + (1)) (4) (by omega)) (mem_raw_of_box k (2) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (4) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (4) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_4_p_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((1), (4)) ≤ incr (reciprocalField k) (0, -1) ((-1), (4)) ∧
    incr (reciprocalField k) (0, -1) ((1), (4)) - incr (reciprocalField k) (0, -1) ((0), (5)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((1), (4)) - incr (reciprocalField k) (0, -1) ((-2), (5)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((1), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (1) (4) (Or.inr rfl) (mem_raw_of_box k (1) (4) (by omega)) (mem_raw_of_box k (1) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((-1), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (-1) (4) (Or.inr rfl) (mem_raw_of_box k (-1) (4) (by omega)) (mem_raw_of_box k (-1) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((0), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) (0) (5) (Or.inr rfl) (mem_raw_of_box k (0) (5) (by omega)) (mem_raw_of_box k (0) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((-2), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) (-2) (5) (Or.inr rfl) (mem_raw_of_box k (-2) (5) (by omega)) (mem_raw_of_box k (-2) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_4_p_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((1), (4)) ≤ incr (reciprocalField k) (0, 1) ((-1), (4)) ∧
    incr (reciprocalField k) (0, 1) ((1), (4)) - incr (reciprocalField k) (0, 1) ((0), (5)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((1), (4)) - incr (reciprocalField k) (0, 1) ((-2), (5)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((1), (4)) = -((4)) := by
    rw [incr_vert k 1 (1) (4) (Or.inl rfl) (mem_raw_of_box k (1) (4) (by omega)) (mem_raw_of_box k (1) ((4) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((-1), (4)) = -((4)) := by
    rw [incr_vert k 1 (-1) (4) (Or.inl rfl) (mem_raw_of_box k (-1) (4) (by omega)) (mem_raw_of_box k (-1) ((4) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((0), (5)) = -((5)) := by
    rw [incr_vert k 1 (0) (5) (Or.inl rfl) (mem_raw_of_box k (0) (5) (by omega)) (mem_raw_of_box k (0) ((5) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((-2), (5)) = -((5)) := by
    rw [incr_vert k 1 (-2) (5) (Or.inl rfl) (mem_raw_of_box k (-2) (5) (by omega)) (mem_raw_of_box k (-2) ((5) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_4_m_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((1), (4)) ≤ incr (reciprocalField k) (0, -1) ((3), (4)) ∧
    incr (reciprocalField k) (0, -1) ((1), (4)) - incr (reciprocalField k) (0, -1) ((0), (5)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((1), (4)) - incr (reciprocalField k) (0, -1) ((2), (5)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((1), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (1) (4) (Or.inr rfl) (mem_raw_of_box k (1) (4) (by omega)) (mem_raw_of_box k (1) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((3), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (3) (4) (Or.inr rfl) (mem_raw_of_box k (3) (4) (by omega)) (mem_raw_of_box k (3) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((0), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) (0) (5) (Or.inr rfl) (mem_raw_of_box k (0) (5) (by omega)) (mem_raw_of_box k (0) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((2), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) (2) (5) (Or.inr rfl) (mem_raw_of_box k (2) (5) (by omega)) (mem_raw_of_box k (2) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_4_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((1), (4)) ≤ incr (reciprocalField k) (0, 1) ((3), (4)) ∧
    incr (reciprocalField k) (0, 1) ((1), (4)) - incr (reciprocalField k) (0, 1) ((0), (5)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((1), (4)) - incr (reciprocalField k) (0, 1) ((2), (5)) ≤ 1 := by
  have hZ2_0 : incr (reciprocalField k) (0, 1) ((3), (4)) = incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (3)) :=
    (incr_eq_U k (0, 1) ((3 - (2 * (k : ℤ) + 3)), (3)) ((3), (4)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (0, 1) ((1), (4)) = -((4)) := by
    rw [incr_vert k 1 (1) (4) (Or.inl rfl) (mem_raw_of_box k (1) (4) (by omega)) (mem_raw_of_box k (1) ((4) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (3)) = -((3)) := by
    rw [incr_vert k 1 (3 - (2 * (k : ℤ) + 3)) (3) (Or.inl rfl) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) (3) (by omega)) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((0), (5)) = -((5)) := by
    rw [incr_vert k 1 (0) (5) (Or.inl rfl) (mem_raw_of_box k (0) (5) (by omega)) (mem_raw_of_box k (0) ((5) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((2), (5)) = 1 - (2 * (k : ℤ) + 3) := by
    rw [show ((2), (5)) = ((2 : ℤ), 2 * (k : ℤ) + 3) from by ext <;> omega]
    exact incr_c2low_up k
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_5_p_mx (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (-1, 0) ((1), (5)) ≤ incr (reciprocalField k) (-1, 0) ((-1), (5)) ∧
    incr (reciprocalField k) (-1, 0) ((1), (5)) - incr (reciprocalField k) (-1, 0) ((0), (6)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((1), (5)) - incr (reciprocalField k) (-1, 0) ((-2), (6)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (-1, 0) ((1), (5)) = min ((1) + (-1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (1) (5) (mem_raw_of_box k ((1) + (-1)) (5) (by omega)) (mem_raw_of_box k (1) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (5) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (-1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (5) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) ((-1), (5)) = min ((-1) + (-1) - 1) 0 - min ((-1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-1) (5) (mem_raw_of_box k ((-1) + (-1)) (5) (by omega)) (mem_raw_of_box k (-1) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-1) (5) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-1) + (-1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-1) (5) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((0), (6)) = min ((0) + (-1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (0) (6) (mem_raw_of_box k ((0) + (-1)) (6) (by omega)) (mem_raw_of_box k (0) (6) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (6) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (-1)) (6) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (6) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) ((-2), (6)) = min ((-2) + (-1) - 1) 0 - min ((-2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (-2) (6) (mem_raw_of_box k ((-2) + (-1)) (6) (by omega)) (mem_raw_of_box k (-2) (6) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-2) (6) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((-2) + (-1)) (6) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-2) (6) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_5_p_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((1), (5)) ≤ incr (reciprocalField k) (1, 0) ((-1), (5)) ∧
    incr (reciprocalField k) (1, 0) ((1), (5)) - incr (reciprocalField k) (1, 0) ((0), (6)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((1), (5)) - incr (reciprocalField k) (1, 0) ((-2), (6)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (1, 0) ((1), (5)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (5) (mem_raw_of_box k ((1) + (1)) (5) (by omega)) (mem_raw_of_box k (1) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (5) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (5) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((-1), (5)) = min ((-1) + (1) - 1) 0 - min ((-1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (-1) (5) (mem_raw_of_box k ((-1) + (1)) (5) (by omega)) (mem_raw_of_box k (-1) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-1) (5) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((-1) + (1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-1) (5) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((0), (6)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (6) (mem_raw_of_box k ((0) + (1)) (6) (by omega)) (mem_raw_of_box k (0) (6) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (6) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (6) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (6) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((-2), (6)) = min ((-2) + (1) - 1) 0 - min ((-2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (-2) (6) (mem_raw_of_box k ((-2) + (1)) (6) (by omega)) (mem_raw_of_box k (-2) (6) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-2) (6) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((-2) + (1)) (6) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-2) (6) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_5_m_mx (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (-1, 0) ((1), (5)) ≤ incr (reciprocalField k) (-1, 0) ((3), (5)) ∧
    incr (reciprocalField k) (-1, 0) ((1), (5)) - incr (reciprocalField k) (-1, 0) ((0), (6)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((1), (5)) - incr (reciprocalField k) (-1, 0) ((2), (6)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (-1, 0) ((3), (5)) = incr (reciprocalField k) (-1, 0) ((3 - (2 * (k : ℤ) + 3)), (4)) :=
    (incr_eq_U k (-1, 0) ((3 - (2 * (k : ℤ) + 3)), (4)) ((3), (5)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (-1, 0) ((1), (5)) = min ((1) + (-1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (1) (5) (mem_raw_of_box k ((1) + (-1)) (5) (by omega)) (mem_raw_of_box k (1) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (5) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (-1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (5) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) ((3 - (2 * (k : ℤ) + 3)), (4)) = min ((3 - (2 * (k : ℤ) + 3)) + (-1) - 1) 0 - min ((3 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (3 - (2 * (k : ℤ) + 3)) (4) (mem_raw_of_box k ((3 - (2 * (k : ℤ) + 3)) + (-1)) (4) (by omega)) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (4) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((3 - (2 * (k : ℤ) + 3)) + (-1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (4) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((0), (6)) = min ((0) + (-1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (0) (6) (mem_raw_of_box k ((0) + (-1)) (6) (by omega)) (mem_raw_of_box k (0) (6) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (6) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (-1)) (6) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (6) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) ((2), (6)) = min ((2) + (-1) - 1) 0 - min ((2) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (-1) (2) (6) (mem_raw_of_box k ((2) + (-1)) (6) (by omega)) (mem_raw_corner2' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (2) (6) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (-1)) (6) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (2) (6) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_5_m_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((1), (5)) ≤ incr (reciprocalField k) (1, 0) ((3), (5)) ∧
    incr (reciprocalField k) (1, 0) ((1), (5)) - incr (reciprocalField k) (1, 0) ((0), (6)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((1), (5)) - incr (reciprocalField k) (1, 0) ((2), (6)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (1, 0) ((3), (5)) = incr (reciprocalField k) (1, 0) ((3 - (2 * (k : ℤ) + 3)), (4)) :=
    (incr_eq_U k (1, 0) ((3 - (2 * (k : ℤ) + 3)), (4)) ((3), (5)) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (1, 0) ((2), (6)) = incr (reciprocalField k) (1, 0) ((2 - (2 * (k : ℤ) + 3)), (5)) :=
    (incr_eq_U k (1, 0) ((2 - (2 * (k : ℤ) + 3)), (5)) ((2), (6)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (1, 0) ((1), (5)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (5) (mem_raw_of_box k ((1) + (1)) (5) (by omega)) (mem_raw_of_box k (1) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (5) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (5) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((3 - (2 * (k : ℤ) + 3)), (4)) = min ((3 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((3 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (3 - (2 * (k : ℤ) + 3)) (4) (mem_raw_of_box k ((3 - (2 * (k : ℤ) + 3)) + (1)) (4) (by omega)) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (4) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3 - (2 * (k : ℤ) + 3)) + (1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (4) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((0), (6)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (6) (mem_raw_of_box k ((0) + (1)) (6) (by omega)) (mem_raw_of_box k (0) (6) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (6) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (6) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (6) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((2 - (2 * (k : ℤ) + 3)), (5)) = min ((2 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((2 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2 - (2 * (k : ℤ) + 3)) (5) (mem_raw_of_box k ((2 - (2 * (k : ℤ) + 3)) + (1)) (5) (by omega)) (mem_raw_of_box k (2 - (2 * (k : ℤ) + 3)) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2 - (2 * (k : ℤ) + 3)) (5) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2 - (2 * (k : ℤ) + 3)) + (1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2 - (2 * (k : ℤ) + 3)) (5) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_6_p_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((1), (6)) ≤ incr (reciprocalField k) (0, 1) ((-1), (6)) ∧
    incr (reciprocalField k) (0, 1) ((1), (6)) - incr (reciprocalField k) (0, 1) ((0), (7)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((1), (6)) - incr (reciprocalField k) (0, 1) ((-2), (7)) ≤ 1 := by
  have hZ1_0 : incr (reciprocalField k) (0, 1) ((2 * (k : ℤ) + 3), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((1), (6)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) ((2 * (k : ℤ) + 3), (5 - (2 * (k : ℤ) + 3))) ((1), (6)) (by ext <;> (simp; try ring))
  have hZ2_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-1), (6)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) ((-1), (6)) (by ext <;> (simp; try ring))
  have hZ3_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 1), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((0), (7)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 1), (6 - (2 * (k : ℤ) + 3))) ((0), (7)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 3), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((-2), (7)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 3), (6 - (2 * (k : ℤ) + 3))) ((-2), (7)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, 1) ((2 * (k : ℤ) + 3), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (k : ℤ) + 3) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 2), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 2) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 1), (6 - (2 * (k : ℤ) + 3))) = -((6 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 1) (6 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) ((6 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 3), (6 - (2 * (k : ℤ) + 3))) = -((6 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 3) (6 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 3) ((6 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_1_6_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((1), (6)) ≤ incr (reciprocalField k) (0, 1) ((3), (6)) ∧
    incr (reciprocalField k) (0, 1) ((1), (6)) - incr (reciprocalField k) (0, 1) ((0), (7)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((1), (6)) - incr (reciprocalField k) (0, 1) ((2), (7)) ≤ 1 := by
  have hZ1_0 : incr (reciprocalField k) (0, 1) ((2 * (k : ℤ) + 3), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((1), (6)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) ((2 * (k : ℤ) + 3), (5 - (2 * (k : ℤ) + 3))) ((1), (6)) (by ext <;> (simp; try ring))
  have hZ2_0 : incr (reciprocalField k) (0, 1) ((3), (6)) = incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (5)) :=
    (incr_eq_U k (0, 1) ((3 - (2 * (k : ℤ) + 3)), (5)) ((3), (6)) (by ext <;> (simp; try ring))).symm
  have hZ3_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 1), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((0), (7)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) - 1), (6 - (2 * (k : ℤ) + 3))) ((0), (7)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) + 1), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((2), (7)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) (((2 * (k : ℤ) + 3) + 1), (6 - (2 * (k : ℤ) + 3))) ((2), (7)) (by ext <;> (simp; try ring))
  have hZ4_1 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) + 1), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((1), (5 - (2 * (k : ℤ) + 3))) :=
    (incr_eq_U k (0, 1) ((1), (5 - (2 * (k : ℤ) + 3))) (((2 * (k : ℤ) + 3) + 1), (6 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (0, 1) ((2 * (k : ℤ) + 3), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (k : ℤ) + 3) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (5)) = -((5)) := by
    rw [incr_vert k 1 (3 - (2 * (k : ℤ) + 3)) (5) (Or.inl rfl) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) (5) (by omega)) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) ((5) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) (((2 * (k : ℤ) + 3) - 1), (6 - (2 * (k : ℤ) + 3))) = -((6 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 ((2 * (k : ℤ) + 3) - 1) (6 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) ((6 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((1), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 (1) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k (1) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (1) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_2_0_p_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((2), (0)) ≤ incr (reciprocalField k) (1, 0) ((0), (0)) ∧
    incr (reciprocalField k) (1, 0) ((2), (0)) - incr (reciprocalField k) (1, 0) ((1), (1)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((2), (0)) - incr (reciprocalField k) (1, 0) ((-1), (1)) ≤ 0 := by
  have hZ4_0 : incr (reciprocalField k) (1, 0) ((-1), (1)) = incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 1), (2)) :=
    incr_eq_U k (1, 0) ((-1), (1)) (((2 * (k : ℤ) + 3) - 1), (2)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (1, 0) ((2), (0)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (0) (mem_raw_of_box k ((2) + (1)) (0) (by omega)) (mem_raw_of_box k (2) (0) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (0) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (0) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((0), (0)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) (0) (0) (mem_raw_of_box k ((0) + (1)) (0) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (0) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (0) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (0) (0) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((1), (1)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (1) (mem_raw_of_box k ((1) + (1)) (1) (by omega)) (mem_raw_of_box k (1) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (1) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 1), (2)) = min (((2 * (k : ℤ) + 3) - 1) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 1) (2) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 1) + (1)) (2) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 1) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 1) (2) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_2_0_m_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((2), (0)) ≤ incr (reciprocalField k) (1, 0) ((4), (0)) ∧
    incr (reciprocalField k) (1, 0) ((2), (0)) - incr (reciprocalField k) (1, 0) ((1), (1)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((2), (0)) - incr (reciprocalField k) (1, 0) ((3), (1)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (1, 0) ((2), (0)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (0) (mem_raw_of_box k ((2) + (1)) (0) (by omega)) (mem_raw_of_box k (2) (0) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (0) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (0) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((4), (0)) = min ((4) + (1) - 1) 0 - min ((4) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (4) (0) (mem_raw_of_box k ((4) + (1)) (0) (by omega)) (mem_raw_of_box k (4) (0) (by omega)), hG_nc (2 * (k : ℤ) + 3) (4) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((4) + (1)) (0) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (4) (0) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((1), (1)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (1) (mem_raw_of_box k ((1) + (1)) (1) (by omega)) (mem_raw_of_box k (1) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (1) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((3), (1)) = min ((3) + (1) - 1) 0 - min ((3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (3) (1) (mem_raw_of_box k ((3) + (1)) (1) (by omega)) (mem_raw_of_box k (3) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3) (1) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_2_1_p_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((2), (1)) ≤ incr (reciprocalField k) (0, -1) ((0), (1)) ∧
    incr (reciprocalField k) (0, -1) ((2), (1)) - incr (reciprocalField k) (0, -1) ((1), (2)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((2), (1)) - incr (reciprocalField k) (0, -1) ((-1), (2)) ≤ -1 := by
  have hZ4_0 : incr (reciprocalField k) (0, -1) ((-1), (2)) = incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 1), (3)) :=
    incr_eq_U k (0, -1) ((-1), (2)) (((2 * (k : ℤ) + 3) - 1), (3)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (0, -1) ((2), (1)) = ((1)) + -1 := by
    rw [incr_vert k (-1) (2) (1) (Or.inr rfl) (mem_raw_of_box k (2) (1) (by omega)) (mem_raw_of_box k (2) ((1) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((0), (1)) = 1 := by
    rw [show ((0), (1)) = ((0 : ℤ), (1 : ℤ)) from by ext <;> omega]
    exact incr_c0_fromdown k
  have vZ3 : incr (reciprocalField k) (0, -1) ((1), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (1) (2) (Or.inr rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) (((2 * (k : ℤ) + 3) - 1), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) ((2 * (k : ℤ) + 3) - 1) (3) (Or.inr rfl) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) (3) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 1) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_2_1_p_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((2), (1)) ≤ incr (reciprocalField k) (0, 1) ((0), (1)) ∧
    incr (reciprocalField k) (0, 1) ((2), (1)) - incr (reciprocalField k) (0, 1) ((1), (2)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((2), (1)) - incr (reciprocalField k) (0, 1) ((-1), (2)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((2), (1)) = -((1)) := by
    rw [incr_vert k 1 (2) (1) (Or.inl rfl) (mem_raw_of_box k (2) (1) (by omega)) (mem_raw_of_box k (2) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((0), (1)) = -((1)) := by
    rw [incr_vert k 1 (0) (1) (Or.inl rfl) (mem_raw_of_box k (0) (1) (by omega)) (mem_raw_of_box k (0) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((1), (2)) = -((2)) := by
    rw [incr_vert k 1 (1) (2) (Or.inl rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((-1), (2)) = -((2)) := by
    rw [incr_vert k 1 (-1) (2) (Or.inl rfl) (mem_raw_of_box k (-1) (2) (by omega)) (mem_raw_of_box k (-1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_2_1_m_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((2), (1)) ≤ incr (reciprocalField k) (0, -1) ((4), (1)) ∧
    incr (reciprocalField k) (0, -1) ((2), (1)) - incr (reciprocalField k) (0, -1) ((1), (2)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((2), (1)) - incr (reciprocalField k) (0, -1) ((3), (2)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((2), (1)) = ((1)) + -1 := by
    rw [incr_vert k (-1) (2) (1) (Or.inr rfl) (mem_raw_of_box k (2) (1) (by omega)) (mem_raw_of_box k (2) ((1) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((4), (1)) = ((1)) + -1 := by
    rw [incr_vert k (-1) (4) (1) (Or.inr rfl) (mem_raw_of_box k (4) (1) (by omega)) (mem_raw_of_box k (4) ((1) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((1), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (1) (2) (Or.inr rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((3), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (3) (2) (Or.inr rfl) (mem_raw_of_box k (3) (2) (by omega)) (mem_raw_of_box k (3) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_2_1_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((2), (1)) ≤ incr (reciprocalField k) (0, 1) ((4), (1)) ∧
    incr (reciprocalField k) (0, 1) ((2), (1)) - incr (reciprocalField k) (0, 1) ((1), (2)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((2), (1)) - incr (reciprocalField k) (0, 1) ((3), (2)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((2), (1)) = -((1)) := by
    rw [incr_vert k 1 (2) (1) (Or.inl rfl) (mem_raw_of_box k (2) (1) (by omega)) (mem_raw_of_box k (2) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((4), (1)) = -((1)) := by
    rw [incr_vert k 1 (4) (1) (Or.inl rfl) (mem_raw_of_box k (4) (1) (by omega)) (mem_raw_of_box k (4) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((1), (2)) = -((2)) := by
    rw [incr_vert k 1 (1) (2) (Or.inl rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((3), (2)) = -((2)) := by
    rw [incr_vert k 1 (3) (2) (Or.inl rfl) (mem_raw_of_box k (3) (2) (by omega)) (mem_raw_of_box k (3) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_2_2_p_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((2), (2)) ≤ incr (reciprocalField k) (1, 0) ((0), (2)) ∧
    incr (reciprocalField k) (1, 0) ((2), (2)) - incr (reciprocalField k) (1, 0) ((1), (3)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((2), (2)) - incr (reciprocalField k) (1, 0) ((-1), (3)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (1, 0) ((2), (2)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (2) (mem_raw_of_box k ((2) + (1)) (2) (by omega)) (mem_raw_of_box k (2) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (2) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((0), (2)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (2) (mem_raw_of_box k ((0) + (1)) (2) (by omega)) (mem_raw_of_box k (0) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (2) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((1), (3)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (3) (mem_raw_of_box k ((1) + (1)) (3) (by omega)) (mem_raw_of_box k (1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (3) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((-1), (3)) = min ((-1) + (1) - 1) 0 - min ((-1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (-1) (3) (mem_raw_of_box k ((-1) + (1)) (3) (by omega)) (mem_raw_of_box k (-1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-1) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((-1) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-1) (3) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_2_2_m_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((2), (2)) ≤ incr (reciprocalField k) (1, 0) ((4), (2)) ∧
    incr (reciprocalField k) (1, 0) ((2), (2)) - incr (reciprocalField k) (1, 0) ((1), (3)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((2), (2)) - incr (reciprocalField k) (1, 0) ((3), (3)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (1, 0) ((2), (2)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (2) (mem_raw_of_box k ((2) + (1)) (2) (by omega)) (mem_raw_of_box k (2) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (2) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((4), (2)) = min ((4) + (1) - 1) 0 - min ((4) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (4) (2) (mem_raw_of_box k ((4) + (1)) (2) (by omega)) (mem_raw_of_box k (4) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (4) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((4) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (4) (2) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((1), (3)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (3) (mem_raw_of_box k ((1) + (1)) (3) (by omega)) (mem_raw_of_box k (1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (3) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((3), (3)) = min ((3) + (1) - 1) 0 - min ((3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (3) (3) (mem_raw_of_box k ((3) + (1)) (3) (by omega)) (mem_raw_of_box k (3) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3) (3) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_2_3_p_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((2), (3)) ≤ incr (reciprocalField k) (0, -1) ((0), (3)) ∧
    incr (reciprocalField k) (0, -1) ((2), (3)) - incr (reciprocalField k) (0, -1) ((1), (4)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((2), (3)) - incr (reciprocalField k) (0, -1) ((-1), (4)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((2), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (2) (3) (Or.inr rfl) (mem_raw_of_box k (2) (3) (by omega)) (mem_raw_of_box k (2) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((0), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (0) (3) (Or.inr rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((1), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (1) (4) (Or.inr rfl) (mem_raw_of_box k (1) (4) (by omega)) (mem_raw_of_box k (1) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((-1), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (-1) (4) (Or.inr rfl) (mem_raw_of_box k (-1) (4) (by omega)) (mem_raw_of_box k (-1) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_2_3_p_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((2), (3)) ≤ incr (reciprocalField k) (0, 1) ((0), (3)) ∧
    incr (reciprocalField k) (0, 1) ((2), (3)) - incr (reciprocalField k) (0, 1) ((1), (4)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((2), (3)) - incr (reciprocalField k) (0, 1) ((-1), (4)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((2), (3)) = -((3)) := by
    rw [incr_vert k 1 (2) (3) (Or.inl rfl) (mem_raw_of_box k (2) (3) (by omega)) (mem_raw_of_box k (2) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((0), (3)) = -((3)) := by
    rw [incr_vert k 1 (0) (3) (Or.inl rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((1), (4)) = -((4)) := by
    rw [incr_vert k 1 (1) (4) (Or.inl rfl) (mem_raw_of_box k (1) (4) (by omega)) (mem_raw_of_box k (1) ((4) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((-1), (4)) = -((4)) := by
    rw [incr_vert k 1 (-1) (4) (Or.inl rfl) (mem_raw_of_box k (-1) (4) (by omega)) (mem_raw_of_box k (-1) ((4) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_2_3_m_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((2), (3)) ≤ incr (reciprocalField k) (0, -1) ((4), (3)) ∧
    incr (reciprocalField k) (0, -1) ((2), (3)) - incr (reciprocalField k) (0, -1) ((1), (4)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((2), (3)) - incr (reciprocalField k) (0, -1) ((3), (4)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((2), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (2) (3) (Or.inr rfl) (mem_raw_of_box k (2) (3) (by omega)) (mem_raw_of_box k (2) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((4), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (4) (3) (Or.inr rfl) (mem_raw_of_box k (4) (3) (by omega)) (mem_raw_of_box k (4) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((1), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (1) (4) (Or.inr rfl) (mem_raw_of_box k (1) (4) (by omega)) (mem_raw_of_box k (1) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((3), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (3) (4) (Or.inr rfl) (mem_raw_of_box k (3) (4) (by omega)) (mem_raw_of_box k (3) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_2_3_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((2), (3)) ≤ incr (reciprocalField k) (0, 1) ((4), (3)) ∧
    incr (reciprocalField k) (0, 1) ((2), (3)) - incr (reciprocalField k) (0, 1) ((1), (4)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((2), (3)) - incr (reciprocalField k) (0, 1) ((3), (4)) ≤ 1 := by
  have hZ2_0 : incr (reciprocalField k) (0, 1) ((4), (3)) = incr (reciprocalField k) (0, 1) ((4 - (2 * (k : ℤ) + 3)), (2)) :=
    (incr_eq_U k (0, 1) ((4 - (2 * (k : ℤ) + 3)), (2)) ((4), (3)) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (0, 1) ((3), (4)) = incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (3)) :=
    (incr_eq_U k (0, 1) ((3 - (2 * (k : ℤ) + 3)), (3)) ((3), (4)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (0, 1) ((2), (3)) = -((3)) := by
    rw [incr_vert k 1 (2) (3) (Or.inl rfl) (mem_raw_of_box k (2) (3) (by omega)) (mem_raw_of_box k (2) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((4 - (2 * (k : ℤ) + 3)), (2)) = -((2)) := by
    rw [incr_vert k 1 (4 - (2 * (k : ℤ) + 3)) (2) (Or.inl rfl) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) (2) (by omega)) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((1), (4)) = -((4)) := by
    rw [incr_vert k 1 (1) (4) (Or.inl rfl) (mem_raw_of_box k (1) (4) (by omega)) (mem_raw_of_box k (1) ((4) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (3)) = -((3)) := by
    rw [incr_vert k 1 (3 - (2 * (k : ℤ) + 3)) (3) (Or.inl rfl) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) (3) (by omega)) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_2_4_p_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((2), (4)) ≤ incr (reciprocalField k) (1, 0) ((0), (4)) ∧
    incr (reciprocalField k) (1, 0) ((2), (4)) - incr (reciprocalField k) (1, 0) ((1), (5)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((2), (4)) - incr (reciprocalField k) (1, 0) ((-1), (5)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (1, 0) ((2), (4)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (4) (mem_raw_of_box k ((2) + (1)) (4) (by omega)) (mem_raw_of_box k (2) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (4) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (4) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((0), (4)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (4) (mem_raw_of_box k ((0) + (1)) (4) (by omega)) (mem_raw_of_box k (0) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (4) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (4) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((1), (5)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (5) (mem_raw_of_box k ((1) + (1)) (5) (by omega)) (mem_raw_of_box k (1) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (5) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (5) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((-1), (5)) = min ((-1) + (1) - 1) 0 - min ((-1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (-1) (5) (mem_raw_of_box k ((-1) + (1)) (5) (by omega)) (mem_raw_of_box k (-1) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-1) (5) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((-1) + (1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-1) (5) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_2_4_m_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((2), (4)) ≤ incr (reciprocalField k) (1, 0) ((4), (4)) ∧
    incr (reciprocalField k) (1, 0) ((2), (4)) - incr (reciprocalField k) (1, 0) ((1), (5)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((2), (4)) - incr (reciprocalField k) (1, 0) ((3), (5)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (1, 0) ((4), (4)) = incr (reciprocalField k) (1, 0) ((4 - (2 * (k : ℤ) + 3)), (3)) :=
    (incr_eq_U k (1, 0) ((4 - (2 * (k : ℤ) + 3)), (3)) ((4), (4)) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (1, 0) ((3), (5)) = incr (reciprocalField k) (1, 0) ((3 - (2 * (k : ℤ) + 3)), (4)) :=
    (incr_eq_U k (1, 0) ((3 - (2 * (k : ℤ) + 3)), (4)) ((3), (5)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (1, 0) ((2), (4)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (4) (mem_raw_of_box k ((2) + (1)) (4) (by omega)) (mem_raw_of_box k (2) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (4) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (4) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((4 - (2 * (k : ℤ) + 3)), (3)) = min ((4 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((4 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (4 - (2 * (k : ℤ) + 3)) (3) (mem_raw_of_box k ((4 - (2 * (k : ℤ) + 3)) + (1)) (3) (by omega)) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (4 - (2 * (k : ℤ) + 3)) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((4 - (2 * (k : ℤ) + 3)) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (4 - (2 * (k : ℤ) + 3)) (3) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((1), (5)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (5) (mem_raw_of_box k ((1) + (1)) (5) (by omega)) (mem_raw_of_box k (1) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (5) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (5) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((3 - (2 * (k : ℤ) + 3)), (4)) = min ((3 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((3 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (3 - (2 * (k : ℤ) + 3)) (4) (mem_raw_of_box k ((3 - (2 * (k : ℤ) + 3)) + (1)) (4) (by omega)) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (4) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3 - (2 * (k : ℤ) + 3)) + (1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (4) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_2_5_p_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((2), (5)) ≤ incr (reciprocalField k) (0, -1) ((0), (5)) ∧
    incr (reciprocalField k) (0, -1) ((2), (5)) - incr (reciprocalField k) (0, -1) ((1), (6)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((2), (5)) - incr (reciprocalField k) (0, -1) ((-1), (6)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((2), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) (2) (5) (Or.inr rfl) (mem_raw_of_box k (2) (5) (by omega)) (mem_raw_of_box k (2) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((0), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) (0) (5) (Or.inr rfl) (mem_raw_of_box k (0) (5) (by omega)) (mem_raw_of_box k (0) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((1), (6)) = ((6)) + -1 := by
    rw [incr_vert k (-1) (1) (6) (Or.inr rfl) (mem_raw_of_box k (1) (6) (by omega)) (mem_raw_of_box k (1) ((6) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((-1), (6)) = ((6)) + -1 := by
    rw [incr_vert k (-1) (-1) (6) (Or.inr rfl) (mem_raw_of_box k (-1) (6) (by omega)) (mem_raw_of_box k (-1) ((6) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_2_5_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((2), (5)) ≤ incr (reciprocalField k) (0, 1) ((4), (5)) ∧
    incr (reciprocalField k) (0, 1) ((2), (5)) - incr (reciprocalField k) (0, 1) ((1), (6)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((2), (5)) - incr (reciprocalField k) (0, 1) ((3), (6)) ≤ 1 := by
  have hZ2_0 : incr (reciprocalField k) (0, 1) ((4), (5)) = incr (reciprocalField k) (0, 1) ((4 - (2 * (k : ℤ) + 3)), (4)) :=
    (incr_eq_U k (0, 1) ((4 - (2 * (k : ℤ) + 3)), (4)) ((4), (5)) (by ext <;> (simp; try ring))).symm
  have hZ3_0 : incr (reciprocalField k) (0, 1) ((2 * (k : ℤ) + 3), (5 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (0, 1) ((1), (6)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) ((2 * (k : ℤ) + 3), (5 - (2 * (k : ℤ) + 3))) ((1), (6)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (0, 1) ((3), (6)) = incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (5)) :=
    (incr_eq_U k (0, 1) ((3 - (2 * (k : ℤ) + 3)), (5)) ((3), (6)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (0, 1) ((2), (5)) = 1 - (2 * (k : ℤ) + 3) := by
    rw [show ((2), (5)) = ((2 : ℤ), 2 * (k : ℤ) + 3) from by ext <;> omega]
    exact incr_c2low_up k
  have vZ2 : incr (reciprocalField k) (0, 1) ((4 - (2 * (k : ℤ) + 3)), (4)) = -((4)) := by
    rw [incr_vert k 1 (4 - (2 * (k : ℤ) + 3)) (4) (Or.inl rfl) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) (4) (by omega)) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) ((4) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((2 * (k : ℤ) + 3), (5 - (2 * (k : ℤ) + 3))) = -((5 - (2 * (k : ℤ) + 3))) := by
    rw [incr_vert k 1 (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (Or.inl rfl) (mem_raw_of_box k (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (k : ℤ) + 3) ((5 - (2 * (k : ℤ) + 3)) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (5)) = -((5)) := by
    rw [incr_vert k 1 (3 - (2 * (k : ℤ) + 3)) (5) (Or.inl rfl) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) (5) (by omega)) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) ((5) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_2_6_p_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((2), (6)) ≤ incr (reciprocalField k) (1, 0) ((0), (6)) ∧
    incr (reciprocalField k) (1, 0) ((2), (6)) - incr (reciprocalField k) (1, 0) ((1), (7)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((2), (6)) - incr (reciprocalField k) (1, 0) ((-1), (7)) ≤ 0 := by
  have hZ1_0 : incr (reciprocalField k) (1, 0) ((2), (6)) = incr (reciprocalField k) (1, 0) ((2 - (2 * (k : ℤ) + 3)), (5)) :=
    (incr_eq_U k (1, 0) ((2 - (2 * (k : ℤ) + 3)), (5)) ((2), (6)) (by ext <;> (simp; try ring))).symm
  have hZ3_0 : incr (reciprocalField k) (1, 0) ((2 * (k : ℤ) + 3), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((1), (7)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) ((2 * (k : ℤ) + 3), (6 - (2 * (k : ℤ) + 3))) ((1), (7)) (by ext <;> (simp; try ring))
  have hZ3_1 : incr (reciprocalField k) (1, 0) ((2 * (k : ℤ) + 3), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((0), (5 - (2 * (k : ℤ) + 3))) :=
    (incr_eq_U k (1, 0) ((0), (5 - (2 * (k : ℤ) + 3))) ((2 * (k : ℤ) + 3), (6 - (2 * (k : ℤ) + 3))) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (1, 0) ((-1), (7)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) (((2 * (k : ℤ) + 3) - 2), (6 - (2 * (k : ℤ) + 3))) ((-1), (7)) (by ext <;> (simp; try ring))
  have vZ1 : incr (reciprocalField k) (1, 0) ((2 - (2 * (k : ℤ) + 3)), (5)) = min ((2 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((2 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2 - (2 * (k : ℤ) + 3)) (5) (mem_raw_of_box k ((2 - (2 * (k : ℤ) + 3)) + (1)) (5) (by omega)) (mem_raw_of_box k (2 - (2 * (k : ℤ) + 3)) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2 - (2 * (k : ℤ) + 3)) (5) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2 - (2 * (k : ℤ) + 3)) + (1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2 - (2 * (k : ℤ) + 3)) (5) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((0), (6)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (6) (mem_raw_of_box k ((0) + (1)) (6) (by omega)) (mem_raw_of_box k (0) (6) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (6) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (6) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (6) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((0), (5 - (2 * (k : ℤ) + 3))) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) (0) (5 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k ((0) + (1)) (5 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (0) (5 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (5 - (2 * (k : ℤ) + 3)) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (0) (5 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) (((2 * (k : ℤ) + 3) - 2), (6 - (2 * (k : ℤ) + 3))) = min (((2 * (k : ℤ) + 3) - 2) + (1) - 1) 0 - min (((2 * (k : ℤ) + 3) - 2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) ((2 * (k : ℤ) + 3) - 2) (6 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k (((2 * (k : ℤ) + 3) - 2) + (1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) - 2) (6 - (2 * (k : ℤ) + 3)) (by omega)), hG_nc (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (6 - (2 * (k : ℤ) + 3)) (1) (not_stairCorner (2 * (k : ℤ) + 3) (((2 * (k : ℤ) + 3) - 2) + (1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) - 2) (6 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_2_6_m_mx (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (-1, 0) ((2), (6)) ≤ incr (reciprocalField k) (-1, 0) ((4), (6)) ∧
    incr (reciprocalField k) (-1, 0) ((2), (6)) - incr (reciprocalField k) (-1, 0) ((1), (7)) ≤ 0 ∧
    incr (reciprocalField k) (-1, 0) ((2), (6)) - incr (reciprocalField k) (-1, 0) ((3), (7)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (-1, 0) ((4), (6)) = incr (reciprocalField k) (-1, 0) ((4 - (2 * (k : ℤ) + 3)), (5)) :=
    (incr_eq_U k (-1, 0) ((4 - (2 * (k : ℤ) + 3)), (5)) ((4), (6)) (by ext <;> (simp; try ring))).symm
  have hZ3_0 : incr (reciprocalField k) (-1, 0) ((2 * (k : ℤ) + 3), (6 - (2 * (k : ℤ) + 3))) = incr (reciprocalField k) (-1, 0) ((1), (7)) + ((2 * (k : ℤ) + 3) * 0 - -1) :=
    incr_eq_T k (-1, 0) ((2 * (k : ℤ) + 3), (6 - (2 * (k : ℤ) + 3))) ((1), (7)) (by ext <;> (simp; try ring))
  have hZ4_0 : incr (reciprocalField k) (-1, 0) ((3), (7)) = incr (reciprocalField k) (-1, 0) ((3 - (2 * (k : ℤ) + 3)), (6)) :=
    (incr_eq_U k (-1, 0) ((3 - (2 * (k : ℤ) + 3)), (6)) ((3), (7)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (-1, 0) ((2), (6)) = min ((2) + (-1) - 1) 0 - min ((2) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (-1) (2) (6) (mem_raw_of_box k ((2) + (-1)) (6) (by omega)) (mem_raw_corner2' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (2) (6) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (-1)) (6) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (2) (6) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (-1, 0) ((4 - (2 * (k : ℤ) + 3)), (5)) = min ((4 - (2 * (k : ℤ) + 3)) + (-1) - 1) 0 - min ((4 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (4 - (2 * (k : ℤ) + 3)) (5) (mem_raw_of_box k ((4 - (2 * (k : ℤ) + 3)) + (-1)) (5) (by omega)) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) (5) (by omega)), hG_nc (2 * (k : ℤ) + 3) (4 - (2 * (k : ℤ) + 3)) (5) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((4 - (2 * (k : ℤ) + 3)) + (-1)) (5) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (4 - (2 * (k : ℤ) + 3)) (5) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (-1, 0) ((2 * (k : ℤ) + 3), (6 - (2 * (k : ℤ) + 3))) = min ((2 * (k : ℤ) + 3) + (-1) - 1) 0 - min ((2 * (k : ℤ) + 3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (2 * (k : ℤ) + 3) (6 - (2 * (k : ℤ) + 3)) (mem_raw_of_box k ((2 * (k : ℤ) + 3) + (-1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (mem_raw_of_box k (2 * (k : ℤ) + 3) (6 - (2 * (k : ℤ) + 3)) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 3) (6 - (2 * (k : ℤ) + 3)) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((2 * (k : ℤ) + 3) + (-1)) (6 - (2 * (k : ℤ) + 3)) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 3) (6 - (2 * (k : ℤ) + 3)) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (-1, 0) ((3 - (2 * (k : ℤ) + 3)), (6)) = min ((3 - (2 * (k : ℤ) + 3)) + (-1) - 1) 0 - min ((3 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (-1) (3 - (2 * (k : ℤ) + 3)) (6) (mem_raw_of_box k ((3 - (2 * (k : ℤ) + 3)) + (-1)) (6) (by omega)) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) (6) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (6) (-1) (not_stairCorner (2 * (k : ℤ) + 3) ((3 - (2 * (k : ℤ) + 3)) + (-1)) (6) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3 - (2 * (k : ℤ) + 3)) (6) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_3_0_p_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((3), (0)) ≤ incr (reciprocalField k) (0, 1) ((1), (0)) ∧
    incr (reciprocalField k) (0, 1) ((3), (0)) - incr (reciprocalField k) (0, 1) ((2), (1)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((3), (0)) - incr (reciprocalField k) (0, 1) ((0), (1)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((3), (0)) = -((0)) := by
    rw [incr_vert k 1 (3) (0) (Or.inl rfl) (mem_raw_of_box k (3) (0) (by omega)) (mem_raw_of_box k (3) ((0) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((1), (0)) = -((0)) := by
    rw [incr_vert k 1 (1) (0) (Or.inl rfl) (mem_raw_of_box k (1) (0) (by omega)) (mem_raw_of_box k (1) ((0) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((2), (1)) = -((1)) := by
    rw [incr_vert k 1 (2) (1) (Or.inl rfl) (mem_raw_of_box k (2) (1) (by omega)) (mem_raw_of_box k (2) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((0), (1)) = -((1)) := by
    rw [incr_vert k 1 (0) (1) (Or.inl rfl) (mem_raw_of_box k (0) (1) (by omega)) (mem_raw_of_box k (0) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_3_0_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((3), (0)) ≤ incr (reciprocalField k) (0, 1) ((5), (0)) ∧
    incr (reciprocalField k) (0, 1) ((3), (0)) - incr (reciprocalField k) (0, 1) ((2), (1)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((3), (0)) - incr (reciprocalField k) (0, 1) ((4), (1)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((3), (0)) = -((0)) := by
    rw [incr_vert k 1 (3) (0) (Or.inl rfl) (mem_raw_of_box k (3) (0) (by omega)) (mem_raw_of_box k (3) ((0) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((5), (0)) = -((0)) := by
    rw [incr_vert k 1 (5) (0) (Or.inl rfl) (mem_raw_of_box k (5) (0) (by omega)) (mem_raw_of_box k (5) ((0) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((2), (1)) = -((1)) := by
    rw [incr_vert k 1 (2) (1) (Or.inl rfl) (mem_raw_of_box k (2) (1) (by omega)) (mem_raw_of_box k (2) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((4), (1)) = -((1)) := by
    rw [incr_vert k 1 (4) (1) (Or.inl rfl) (mem_raw_of_box k (4) (1) (by omega)) (mem_raw_of_box k (4) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_3_1_p_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((3), (1)) ≤ incr (reciprocalField k) (1, 0) ((1), (1)) ∧
    incr (reciprocalField k) (1, 0) ((3), (1)) - incr (reciprocalField k) (1, 0) ((2), (2)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((3), (1)) - incr (reciprocalField k) (1, 0) ((0), (2)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (1, 0) ((3), (1)) = min ((3) + (1) - 1) 0 - min ((3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (3) (1) (mem_raw_of_box k ((3) + (1)) (1) (by omega)) (mem_raw_of_box k (3) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3) (1) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((1), (1)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (1) (mem_raw_of_box k ((1) + (1)) (1) (by omega)) (mem_raw_of_box k (1) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (1) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((2), (2)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (2) (mem_raw_of_box k ((2) + (1)) (2) (by omega)) (mem_raw_of_box k (2) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (2) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((0), (2)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (2) (mem_raw_of_box k ((0) + (1)) (2) (by omega)) (mem_raw_of_box k (0) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (2) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_3_1_m_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((3), (1)) ≤ incr (reciprocalField k) (1, 0) ((5), (1)) ∧
    incr (reciprocalField k) (1, 0) ((3), (1)) - incr (reciprocalField k) (1, 0) ((2), (2)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((3), (1)) - incr (reciprocalField k) (1, 0) ((4), (2)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (1, 0) ((5), (1)) = incr (reciprocalField k) (1, 0) ((5 - (2 * (k : ℤ) + 3)), (0)) :=
    (incr_eq_U k (1, 0) ((5 - (2 * (k : ℤ) + 3)), (0)) ((5), (1)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (1, 0) ((3), (1)) = min ((3) + (1) - 1) 0 - min ((3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (3) (1) (mem_raw_of_box k ((3) + (1)) (1) (by omega)) (mem_raw_of_box k (3) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3) (1) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((5 - (2 * (k : ℤ) + 3)), (0)) = min ((5 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((5 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) (5 - (2 * (k : ℤ) + 3)) (0) (mem_raw_of_box k ((5 - (2 * (k : ℤ) + 3)) + (1)) (0) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((5 - (2 * (k : ℤ) + 3)) + (1)) (0) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (0) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((2), (2)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (2) (mem_raw_of_box k ((2) + (1)) (2) (by omega)) (mem_raw_of_box k (2) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (2) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((4), (2)) = min ((4) + (1) - 1) 0 - min ((4) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (4) (2) (mem_raw_of_box k ((4) + (1)) (2) (by omega)) (mem_raw_of_box k (4) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (4) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((4) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (4) (2) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_3_2_p_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((3), (2)) ≤ incr (reciprocalField k) (0, -1) ((1), (2)) ∧
    incr (reciprocalField k) (0, -1) ((3), (2)) - incr (reciprocalField k) (0, -1) ((2), (3)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((3), (2)) - incr (reciprocalField k) (0, -1) ((0), (3)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((3), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (3) (2) (Or.inr rfl) (mem_raw_of_box k (3) (2) (by omega)) (mem_raw_of_box k (3) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((1), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (1) (2) (Or.inr rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((2), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (2) (3) (Or.inr rfl) (mem_raw_of_box k (2) (3) (by omega)) (mem_raw_of_box k (2) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((0), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (0) (3) (Or.inr rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_3_2_p_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((3), (2)) ≤ incr (reciprocalField k) (0, 1) ((1), (2)) ∧
    incr (reciprocalField k) (0, 1) ((3), (2)) - incr (reciprocalField k) (0, 1) ((2), (3)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((3), (2)) - incr (reciprocalField k) (0, 1) ((0), (3)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((3), (2)) = -((2)) := by
    rw [incr_vert k 1 (3) (2) (Or.inl rfl) (mem_raw_of_box k (3) (2) (by omega)) (mem_raw_of_box k (3) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((1), (2)) = -((2)) := by
    rw [incr_vert k 1 (1) (2) (Or.inl rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((2), (3)) = -((3)) := by
    rw [incr_vert k 1 (2) (3) (Or.inl rfl) (mem_raw_of_box k (2) (3) (by omega)) (mem_raw_of_box k (2) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((0), (3)) = -((3)) := by
    rw [incr_vert k 1 (0) (3) (Or.inl rfl) (mem_raw_of_box k (0) (3) (by omega)) (mem_raw_of_box k (0) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_3_2_m_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((3), (2)) ≤ incr (reciprocalField k) (0, -1) ((5), (2)) ∧
    incr (reciprocalField k) (0, -1) ((3), (2)) - incr (reciprocalField k) (0, -1) ((2), (3)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((3), (2)) - incr (reciprocalField k) (0, -1) ((4), (3)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((3), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (3) (2) (Or.inr rfl) (mem_raw_of_box k (3) (2) (by omega)) (mem_raw_of_box k (3) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((5), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (5) (2) (Or.inr rfl) (mem_raw_of_box k (5) (2) (by omega)) (mem_raw_of_box k (5) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((2), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (2) (3) (Or.inr rfl) (mem_raw_of_box k (2) (3) (by omega)) (mem_raw_of_box k (2) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((4), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (4) (3) (Or.inr rfl) (mem_raw_of_box k (4) (3) (by omega)) (mem_raw_of_box k (4) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_3_2_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((3), (2)) ≤ incr (reciprocalField k) (0, 1) ((5), (2)) ∧
    incr (reciprocalField k) (0, 1) ((3), (2)) - incr (reciprocalField k) (0, 1) ((2), (3)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((3), (2)) - incr (reciprocalField k) (0, 1) ((4), (3)) ≤ 1 := by
  have hZ2_0 : incr (reciprocalField k) (0, 1) ((5), (2)) = incr (reciprocalField k) (0, 1) ((5 - (2 * (k : ℤ) + 3)), (1)) :=
    (incr_eq_U k (0, 1) ((5 - (2 * (k : ℤ) + 3)), (1)) ((5), (2)) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (0, 1) ((4), (3)) = incr (reciprocalField k) (0, 1) ((4 - (2 * (k : ℤ) + 3)), (2)) :=
    (incr_eq_U k (0, 1) ((4 - (2 * (k : ℤ) + 3)), (2)) ((4), (3)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (0, 1) ((3), (2)) = -((2)) := by
    rw [incr_vert k 1 (3) (2) (Or.inl rfl) (mem_raw_of_box k (3) (2) (by omega)) (mem_raw_of_box k (3) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((5 - (2 * (k : ℤ) + 3)), (1)) = -((1)) := by
    rw [incr_vert k 1 (5 - (2 * (k : ℤ) + 3)) (1) (Or.inl rfl) (mem_raw_of_box k (5 - (2 * (k : ℤ) + 3)) (1) (by omega)) (mem_raw_of_box k (5 - (2 * (k : ℤ) + 3)) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((2), (3)) = -((3)) := by
    rw [incr_vert k 1 (2) (3) (Or.inl rfl) (mem_raw_of_box k (2) (3) (by omega)) (mem_raw_of_box k (2) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((4 - (2 * (k : ℤ) + 3)), (2)) = -((2)) := by
    rw [incr_vert k 1 (4 - (2 * (k : ℤ) + 3)) (2) (Or.inl rfl) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) (2) (by omega)) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_3_3_p_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((3), (3)) ≤ incr (reciprocalField k) (1, 0) ((1), (3)) ∧
    incr (reciprocalField k) (1, 0) ((3), (3)) - incr (reciprocalField k) (1, 0) ((2), (4)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((3), (3)) - incr (reciprocalField k) (1, 0) ((0), (4)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (1, 0) ((3), (3)) = min ((3) + (1) - 1) 0 - min ((3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (3) (3) (mem_raw_of_box k ((3) + (1)) (3) (by omega)) (mem_raw_of_box k (3) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3) (3) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((1), (3)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (3) (mem_raw_of_box k ((1) + (1)) (3) (by omega)) (mem_raw_of_box k (1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (3) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((2), (4)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (4) (mem_raw_of_box k ((2) + (1)) (4) (by omega)) (mem_raw_of_box k (2) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (4) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (4) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((0), (4)) = min ((0) + (1) - 1) 0 - min ((0) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (0) (4) (mem_raw_of_box k ((0) + (1)) (4) (by omega)) (mem_raw_of_box k (0) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (0) (4) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((0) + (1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (0) (4) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_3_3_m_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((3), (3)) ≤ incr (reciprocalField k) (1, 0) ((5), (3)) ∧
    incr (reciprocalField k) (1, 0) ((3), (3)) - incr (reciprocalField k) (1, 0) ((2), (4)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((3), (3)) - incr (reciprocalField k) (1, 0) ((4), (4)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (1, 0) ((5), (3)) = incr (reciprocalField k) (1, 0) ((5 - (2 * (k : ℤ) + 3)), (2)) :=
    (incr_eq_U k (1, 0) ((5 - (2 * (k : ℤ) + 3)), (2)) ((5), (3)) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (1, 0) ((4), (4)) = incr (reciprocalField k) (1, 0) ((4 - (2 * (k : ℤ) + 3)), (3)) :=
    (incr_eq_U k (1, 0) ((4 - (2 * (k : ℤ) + 3)), (3)) ((4), (4)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (1, 0) ((3), (3)) = min ((3) + (1) - 1) 0 - min ((3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (3) (3) (mem_raw_of_box k ((3) + (1)) (3) (by omega)) (mem_raw_of_box k (3) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3) (3) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((5 - (2 * (k : ℤ) + 3)), (2)) = min ((5 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((5 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (5 - (2 * (k : ℤ) + 3)) (2) (mem_raw_of_box k ((5 - (2 * (k : ℤ) + 3)) + (1)) (2) (by omega)) (mem_raw_of_box k (5 - (2 * (k : ℤ) + 3)) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((5 - (2 * (k : ℤ) + 3)) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (2) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((2), (4)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (4) (mem_raw_of_box k ((2) + (1)) (4) (by omega)) (mem_raw_of_box k (2) (4) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (4) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (4) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (4) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((4 - (2 * (k : ℤ) + 3)), (3)) = min ((4 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((4 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (4 - (2 * (k : ℤ) + 3)) (3) (mem_raw_of_box k ((4 - (2 * (k : ℤ) + 3)) + (1)) (3) (by omega)) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (4 - (2 * (k : ℤ) + 3)) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((4 - (2 * (k : ℤ) + 3)) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (4 - (2 * (k : ℤ) + 3)) (3) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_3_4_p_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((3), (4)) ≤ incr (reciprocalField k) (0, -1) ((1), (4)) ∧
    incr (reciprocalField k) (0, -1) ((3), (4)) - incr (reciprocalField k) (0, -1) ((2), (5)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((3), (4)) - incr (reciprocalField k) (0, -1) ((0), (5)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((3), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (3) (4) (Or.inr rfl) (mem_raw_of_box k (3) (4) (by omega)) (mem_raw_of_box k (3) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((1), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (1) (4) (Or.inr rfl) (mem_raw_of_box k (1) (4) (by omega)) (mem_raw_of_box k (1) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((2), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) (2) (5) (Or.inr rfl) (mem_raw_of_box k (2) (5) (by omega)) (mem_raw_of_box k (2) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((0), (5)) = ((5)) + -1 := by
    rw [incr_vert k (-1) (0) (5) (Or.inr rfl) (mem_raw_of_box k (0) (5) (by omega)) (mem_raw_of_box k (0) ((5) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_3_4_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((3), (4)) ≤ incr (reciprocalField k) (0, 1) ((5), (4)) ∧
    incr (reciprocalField k) (0, 1) ((3), (4)) - incr (reciprocalField k) (0, 1) ((2), (5)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((3), (4)) - incr (reciprocalField k) (0, 1) ((4), (5)) ≤ 1 := by
  have hZ1_0 : incr (reciprocalField k) (0, 1) ((3), (4)) = incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (3)) :=
    (incr_eq_U k (0, 1) ((3 - (2 * (k : ℤ) + 3)), (3)) ((3), (4)) (by ext <;> (simp; try ring))).symm
  have hZ2_0 : incr (reciprocalField k) (0, 1) ((5), (4)) = incr (reciprocalField k) (0, 1) ((5 - (2 * (k : ℤ) + 3)), (3)) :=
    (incr_eq_U k (0, 1) ((5 - (2 * (k : ℤ) + 3)), (3)) ((5), (4)) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (0, 1) ((4), (5)) = incr (reciprocalField k) (0, 1) ((4 - (2 * (k : ℤ) + 3)), (4)) :=
    (incr_eq_U k (0, 1) ((4 - (2 * (k : ℤ) + 3)), (4)) ((4), (5)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (3)) = -((3)) := by
    rw [incr_vert k 1 (3 - (2 * (k : ℤ) + 3)) (3) (Or.inl rfl) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) (3) (by omega)) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((5 - (2 * (k : ℤ) + 3)), (3)) = -((3)) := by
    rw [incr_vert k 1 (5 - (2 * (k : ℤ) + 3)) (3) (Or.inl rfl) (mem_raw_of_box k (5 - (2 * (k : ℤ) + 3)) (3) (by omega)) (mem_raw_of_box k (5 - (2 * (k : ℤ) + 3)) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((2), (5)) = 1 - (2 * (k : ℤ) + 3) := by
    rw [show ((2), (5)) = ((2 : ℤ), 2 * (k : ℤ) + 3) from by ext <;> omega]
    exact incr_c2low_up k
  have vZ4 : incr (reciprocalField k) (0, 1) ((4 - (2 * (k : ℤ) + 3)), (4)) = -((4)) := by
    rw [incr_vert k 1 (4 - (2 * (k : ℤ) + 3)) (4) (Or.inl rfl) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) (4) (by omega)) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) ((4) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_4_0_p_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((4), (0)) ≤ incr (reciprocalField k) (1, 0) ((2), (0)) ∧
    incr (reciprocalField k) (1, 0) ((4), (0)) - incr (reciprocalField k) (1, 0) ((3), (1)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((4), (0)) - incr (reciprocalField k) (1, 0) ((1), (1)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (1, 0) ((4), (0)) = min ((4) + (1) - 1) 0 - min ((4) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (4) (0) (mem_raw_of_box k ((4) + (1)) (0) (by omega)) (mem_raw_of_box k (4) (0) (by omega)), hG_nc (2 * (k : ℤ) + 3) (4) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((4) + (1)) (0) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (4) (0) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((2), (0)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (0) (mem_raw_of_box k ((2) + (1)) (0) (by omega)) (mem_raw_of_box k (2) (0) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (0) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (0) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((3), (1)) = min ((3) + (1) - 1) 0 - min ((3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (3) (1) (mem_raw_of_box k ((3) + (1)) (1) (by omega)) (mem_raw_of_box k (3) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3) (1) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((1), (1)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (1) (mem_raw_of_box k ((1) + (1)) (1) (by omega)) (mem_raw_of_box k (1) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (1) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_4_0_m_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((4), (0)) ≤ incr (reciprocalField k) (1, 0) ((6), (0)) ∧
    incr (reciprocalField k) (1, 0) ((4), (0)) - incr (reciprocalField k) (1, 0) ((3), (1)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((4), (0)) - incr (reciprocalField k) (1, 0) ((5), (1)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (1, 0) ((6), (0)) = incr (reciprocalField k) (1, 0) ((7 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) + ((2 * (k : ℤ) + 3) * 0 - 1) :=
    incr_eq_T k (1, 0) ((6), (0)) ((7 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) (by ext <;> (simp; try ring))
  have hZ2_1 : incr (reciprocalField k) (1, 0) ((7 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) = incr (reciprocalField k) (1, 0) ((-2 * (2 * (k : ℤ) + 3) + 7), (2 * (k : ℤ) + 3)) :=
    (incr_eq_U k (1, 0) ((-2 * (2 * (k : ℤ) + 3) + 7), (2 * (k : ℤ) + 3)) ((7 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (1, 0) ((5), (1)) = incr (reciprocalField k) (1, 0) ((5 - (2 * (k : ℤ) + 3)), (0)) :=
    (incr_eq_U k (1, 0) ((5 - (2 * (k : ℤ) + 3)), (0)) ((5), (1)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (1, 0) ((4), (0)) = min ((4) + (1) - 1) 0 - min ((4) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (4) (0) (mem_raw_of_box k ((4) + (1)) (0) (by omega)) (mem_raw_of_box k (4) (0) (by omega)), hG_nc (2 * (k : ℤ) + 3) (4) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((4) + (1)) (0) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (4) (0) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((-2 * (2 * (k : ℤ) + 3) + 7), (2 * (k : ℤ) + 3)) = min ((-2 * (2 * (k : ℤ) + 3) + 7) + (1) - 1) 0 - min ((-2 * (2 * (k : ℤ) + 3) + 7) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (-2 * (2 * (k : ℤ) + 3) + 7) (2 * (k : ℤ) + 3) (mem_raw_of_box k ((-2 * (2 * (k : ℤ) + 3) + 7) + (1)) (2 * (k : ℤ) + 3) (by omega)) (mem_raw_of_box k (-2 * (2 * (k : ℤ) + 3) + 7) (2 * (k : ℤ) + 3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (-2 * (2 * (k : ℤ) + 3) + 7) (2 * (k : ℤ) + 3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((-2 * (2 * (k : ℤ) + 3) + 7) + (1)) (2 * (k : ℤ) + 3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (-2 * (2 * (k : ℤ) + 3) + 7) (2 * (k : ℤ) + 3) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((3), (1)) = min ((3) + (1) - 1) 0 - min ((3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (3) (1) (mem_raw_of_box k ((3) + (1)) (1) (by omega)) (mem_raw_of_box k (3) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3) (1) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((5 - (2 * (k : ℤ) + 3)), (0)) = min ((5 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((5 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) (5 - (2 * (k : ℤ) + 3)) (0) (mem_raw_of_box k ((5 - (2 * (k : ℤ) + 3)) + (1)) (0) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((5 - (2 * (k : ℤ) + 3)) + (1)) (0) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (0) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_4_1_p_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((4), (1)) ≤ incr (reciprocalField k) (0, -1) ((2), (1)) ∧
    incr (reciprocalField k) (0, -1) ((4), (1)) - incr (reciprocalField k) (0, -1) ((3), (2)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((4), (1)) - incr (reciprocalField k) (0, -1) ((1), (2)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((4), (1)) = ((1)) + -1 := by
    rw [incr_vert k (-1) (4) (1) (Or.inr rfl) (mem_raw_of_box k (4) (1) (by omega)) (mem_raw_of_box k (4) ((1) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((2), (1)) = ((1)) + -1 := by
    rw [incr_vert k (-1) (2) (1) (Or.inr rfl) (mem_raw_of_box k (2) (1) (by omega)) (mem_raw_of_box k (2) ((1) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((3), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (3) (2) (Or.inr rfl) (mem_raw_of_box k (3) (2) (by omega)) (mem_raw_of_box k (3) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((1), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (1) (2) (Or.inr rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_4_1_p_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((4), (1)) ≤ incr (reciprocalField k) (0, 1) ((2), (1)) ∧
    incr (reciprocalField k) (0, 1) ((4), (1)) - incr (reciprocalField k) (0, 1) ((3), (2)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((4), (1)) - incr (reciprocalField k) (0, 1) ((1), (2)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((4), (1)) = -((1)) := by
    rw [incr_vert k 1 (4) (1) (Or.inl rfl) (mem_raw_of_box k (4) (1) (by omega)) (mem_raw_of_box k (4) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((2), (1)) = -((1)) := by
    rw [incr_vert k 1 (2) (1) (Or.inl rfl) (mem_raw_of_box k (2) (1) (by omega)) (mem_raw_of_box k (2) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((3), (2)) = -((2)) := by
    rw [incr_vert k 1 (3) (2) (Or.inl rfl) (mem_raw_of_box k (3) (2) (by omega)) (mem_raw_of_box k (3) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((1), (2)) = -((2)) := by
    rw [incr_vert k 1 (1) (2) (Or.inl rfl) (mem_raw_of_box k (1) (2) (by omega)) (mem_raw_of_box k (1) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_4_1_m_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((4), (1)) ≤ incr (reciprocalField k) (0, -1) ((6), (1)) ∧
    incr (reciprocalField k) (0, -1) ((4), (1)) - incr (reciprocalField k) (0, -1) ((3), (2)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((4), (1)) - incr (reciprocalField k) (0, -1) ((5), (2)) ≤ -1 := by
  have hZ2_0 : incr (reciprocalField k) (0, -1) ((6), (1)) = incr (reciprocalField k) (0, -1) ((7 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 2)) + ((2 * (k : ℤ) + 3) * -1 - 0) :=
    incr_eq_T k (0, -1) ((6), (1)) ((7 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 2)) (by ext <;> (simp; try ring))
  have hZ2_1 : incr (reciprocalField k) (0, -1) ((7 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 2)) = incr (reciprocalField k) (0, -1) ((-2 * (2 * (k : ℤ) + 3) + 7), ((2 * (k : ℤ) + 3) + 1)) :=
    (incr_eq_U k (0, -1) ((-2 * (2 * (k : ℤ) + 3) + 7), ((2 * (k : ℤ) + 3) + 1)) ((7 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 2)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (0, -1) ((4), (1)) = ((1)) + -1 := by
    rw [incr_vert k (-1) (4) (1) (Or.inr rfl) (mem_raw_of_box k (4) (1) (by omega)) (mem_raw_of_box k (4) ((1) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((-2 * (2 * (k : ℤ) + 3) + 7), ((2 * (k : ℤ) + 3) + 1)) = (((2 * (k : ℤ) + 3) + 1)) + -1 := by
    rw [incr_vert k (-1) (-2 * (2 * (k : ℤ) + 3) + 7) ((2 * (k : ℤ) + 3) + 1) (Or.inr rfl) (mem_raw_of_box k (-2 * (2 * (k : ℤ) + 3) + 7) ((2 * (k : ℤ) + 3) + 1) (by omega)) (mem_raw_of_box k (-2 * (2 * (k : ℤ) + 3) + 7) (((2 * (k : ℤ) + 3) + 1) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((3), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (3) (2) (Or.inr rfl) (mem_raw_of_box k (3) (2) (by omega)) (mem_raw_of_box k (3) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((5), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (5) (2) (Or.inr rfl) (mem_raw_of_box k (5) (2) (by omega)) (mem_raw_of_box k (5) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_4_1_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((4), (1)) ≤ incr (reciprocalField k) (0, 1) ((6), (1)) ∧
    incr (reciprocalField k) (0, 1) ((4), (1)) - incr (reciprocalField k) (0, 1) ((3), (2)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((4), (1)) - incr (reciprocalField k) (0, 1) ((5), (2)) ≤ 1 := by
  have hZ2_0 : incr (reciprocalField k) (0, 1) ((6), (1)) = incr (reciprocalField k) (0, 1) ((6 - (2 * (k : ℤ) + 3)), (0)) :=
    (incr_eq_U k (0, 1) ((6 - (2 * (k : ℤ) + 3)), (0)) ((6), (1)) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (0, 1) ((5), (2)) = incr (reciprocalField k) (0, 1) ((5 - (2 * (k : ℤ) + 3)), (1)) :=
    (incr_eq_U k (0, 1) ((5 - (2 * (k : ℤ) + 3)), (1)) ((5), (2)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (0, 1) ((4), (1)) = -((1)) := by
    rw [incr_vert k 1 (4) (1) (Or.inl rfl) (mem_raw_of_box k (4) (1) (by omega)) (mem_raw_of_box k (4) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((6 - (2 * (k : ℤ) + 3)), (0)) = -((0)) := by
    rw [incr_vert k 1 (6 - (2 * (k : ℤ) + 3)) (0) (Or.inl rfl) (mem_raw_of_box k (6 - (2 * (k : ℤ) + 3)) (0) (by omega)) (mem_raw_of_box k (6 - (2 * (k : ℤ) + 3)) ((0) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((3), (2)) = -((2)) := by
    rw [incr_vert k 1 (3) (2) (Or.inl rfl) (mem_raw_of_box k (3) (2) (by omega)) (mem_raw_of_box k (3) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((5 - (2 * (k : ℤ) + 3)), (1)) = -((1)) := by
    rw [incr_vert k 1 (5 - (2 * (k : ℤ) + 3)) (1) (Or.inl rfl) (mem_raw_of_box k (5 - (2 * (k : ℤ) + 3)) (1) (by omega)) (mem_raw_of_box k (5 - (2 * (k : ℤ) + 3)) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_4_2_p_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((4), (2)) ≤ incr (reciprocalField k) (1, 0) ((2), (2)) ∧
    incr (reciprocalField k) (1, 0) ((4), (2)) - incr (reciprocalField k) (1, 0) ((3), (3)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((4), (2)) - incr (reciprocalField k) (1, 0) ((1), (3)) ≤ 0 := by
  have vZ1 : incr (reciprocalField k) (1, 0) ((4), (2)) = min ((4) + (1) - 1) 0 - min ((4) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (4) (2) (mem_raw_of_box k ((4) + (1)) (2) (by omega)) (mem_raw_of_box k (4) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (4) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((4) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (4) (2) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((2), (2)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (2) (mem_raw_of_box k ((2) + (1)) (2) (by omega)) (mem_raw_of_box k (2) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (2) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((3), (3)) = min ((3) + (1) - 1) 0 - min ((3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (3) (3) (mem_raw_of_box k ((3) + (1)) (3) (by omega)) (mem_raw_of_box k (3) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3) (3) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((1), (3)) = min ((1) + (1) - 1) 0 - min ((1) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (1) (3) (mem_raw_of_box k ((1) + (1)) (3) (by omega)) (mem_raw_of_box k (1) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (1) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((1) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (1) (3) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_4_2_m_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((4), (2)) ≤ incr (reciprocalField k) (1, 0) ((6), (2)) ∧
    incr (reciprocalField k) (1, 0) ((4), (2)) - incr (reciprocalField k) (1, 0) ((3), (3)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((4), (2)) - incr (reciprocalField k) (1, 0) ((5), (3)) ≤ 0 := by
  have hZ2_0 : incr (reciprocalField k) (1, 0) ((6), (2)) = incr (reciprocalField k) (1, 0) ((6 - (2 * (k : ℤ) + 3)), (1)) :=
    (incr_eq_U k (1, 0) ((6 - (2 * (k : ℤ) + 3)), (1)) ((6), (2)) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (1, 0) ((5), (3)) = incr (reciprocalField k) (1, 0) ((5 - (2 * (k : ℤ) + 3)), (2)) :=
    (incr_eq_U k (1, 0) ((5 - (2 * (k : ℤ) + 3)), (2)) ((5), (3)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (1, 0) ((4), (2)) = min ((4) + (1) - 1) 0 - min ((4) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (4) (2) (mem_raw_of_box k ((4) + (1)) (2) (by omega)) (mem_raw_of_box k (4) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (4) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((4) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (4) (2) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((6 - (2 * (k : ℤ) + 3)), (1)) = min ((6 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((6 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (6 - (2 * (k : ℤ) + 3)) (1) (mem_raw_of_box k ((6 - (2 * (k : ℤ) + 3)) + (1)) (1) (by omega)) (mem_raw_of_box k (6 - (2 * (k : ℤ) + 3)) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (6 - (2 * (k : ℤ) + 3)) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((6 - (2 * (k : ℤ) + 3)) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (6 - (2 * (k : ℤ) + 3)) (1) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((3), (3)) = min ((3) + (1) - 1) 0 - min ((3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (3) (3) (mem_raw_of_box k ((3) + (1)) (3) (by omega)) (mem_raw_of_box k (3) (3) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3) (3) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3) + (1)) (3) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3) (3) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((5 - (2 * (k : ℤ) + 3)), (2)) = min ((5 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((5 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (5 - (2 * (k : ℤ) + 3)) (2) (mem_raw_of_box k ((5 - (2 * (k : ℤ) + 3)) + (1)) (2) (by omega)) (mem_raw_of_box k (5 - (2 * (k : ℤ) + 3)) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((5 - (2 * (k : ℤ) + 3)) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (2) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_4_3_p_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((4), (3)) ≤ incr (reciprocalField k) (0, -1) ((2), (3)) ∧
    incr (reciprocalField k) (0, -1) ((4), (3)) - incr (reciprocalField k) (0, -1) ((3), (4)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((4), (3)) - incr (reciprocalField k) (0, -1) ((1), (4)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((4), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (4) (3) (Or.inr rfl) (mem_raw_of_box k (4) (3) (by omega)) (mem_raw_of_box k (4) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((2), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (2) (3) (Or.inr rfl) (mem_raw_of_box k (2) (3) (by omega)) (mem_raw_of_box k (2) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((3), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (3) (4) (Or.inr rfl) (mem_raw_of_box k (3) (4) (by omega)) (mem_raw_of_box k (3) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((1), (4)) = ((4)) + -1 := by
    rw [incr_vert k (-1) (1) (4) (Or.inr rfl) (mem_raw_of_box k (1) (4) (by omega)) (mem_raw_of_box k (1) ((4) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_4_3_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((4), (3)) ≤ incr (reciprocalField k) (0, 1) ((6), (3)) ∧
    incr (reciprocalField k) (0, 1) ((4), (3)) - incr (reciprocalField k) (0, 1) ((3), (4)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((4), (3)) - incr (reciprocalField k) (0, 1) ((5), (4)) ≤ 1 := by
  have hZ1_0 : incr (reciprocalField k) (0, 1) ((4), (3)) = incr (reciprocalField k) (0, 1) ((4 - (2 * (k : ℤ) + 3)), (2)) :=
    (incr_eq_U k (0, 1) ((4 - (2 * (k : ℤ) + 3)), (2)) ((4), (3)) (by ext <;> (simp; try ring))).symm
  have hZ2_0 : incr (reciprocalField k) (0, 1) ((6), (3)) = incr (reciprocalField k) (0, 1) ((6 - (2 * (k : ℤ) + 3)), (2)) :=
    (incr_eq_U k (0, 1) ((6 - (2 * (k : ℤ) + 3)), (2)) ((6), (3)) (by ext <;> (simp; try ring))).symm
  have hZ3_0 : incr (reciprocalField k) (0, 1) ((3), (4)) = incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (3)) :=
    (incr_eq_U k (0, 1) ((3 - (2 * (k : ℤ) + 3)), (3)) ((3), (4)) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (0, 1) ((5), (4)) = incr (reciprocalField k) (0, 1) ((5 - (2 * (k : ℤ) + 3)), (3)) :=
    (incr_eq_U k (0, 1) ((5 - (2 * (k : ℤ) + 3)), (3)) ((5), (4)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (0, 1) ((4 - (2 * (k : ℤ) + 3)), (2)) = -((2)) := by
    rw [incr_vert k 1 (4 - (2 * (k : ℤ) + 3)) (2) (Or.inl rfl) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) (2) (by omega)) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((6 - (2 * (k : ℤ) + 3)), (2)) = -((2)) := by
    rw [incr_vert k 1 (6 - (2 * (k : ℤ) + 3)) (2) (Or.inl rfl) (mem_raw_of_box k (6 - (2 * (k : ℤ) + 3)) (2) (by omega)) (mem_raw_of_box k (6 - (2 * (k : ℤ) + 3)) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((3 - (2 * (k : ℤ) + 3)), (3)) = -((3)) := by
    rw [incr_vert k 1 (3 - (2 * (k : ℤ) + 3)) (3) (Or.inl rfl) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) (3) (by omega)) (mem_raw_of_box k (3 - (2 * (k : ℤ) + 3)) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((5 - (2 * (k : ℤ) + 3)), (3)) = -((3)) := by
    rw [incr_vert k 1 (5 - (2 * (k : ℤ) + 3)) (3) (Or.inl rfl) (mem_raw_of_box k (5 - (2 * (k : ℤ) + 3)) (3) (by omega)) (mem_raw_of_box k (5 - (2 * (k : ℤ) + 3)) ((3) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_5_0_p_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((5), (0)) ≤ incr (reciprocalField k) (0, 1) ((3), (0)) ∧
    incr (reciprocalField k) (0, 1) ((5), (0)) - incr (reciprocalField k) (0, 1) ((4), (1)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((5), (0)) - incr (reciprocalField k) (0, 1) ((2), (1)) ≤ 1 := by
  have vZ1 : incr (reciprocalField k) (0, 1) ((5), (0)) = -((0)) := by
    rw [incr_vert k 1 (5) (0) (Or.inl rfl) (mem_raw_of_box k (5) (0) (by omega)) (mem_raw_of_box k (5) ((0) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((3), (0)) = -((0)) := by
    rw [incr_vert k 1 (3) (0) (Or.inl rfl) (mem_raw_of_box k (3) (0) (by omega)) (mem_raw_of_box k (3) ((0) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((4), (1)) = -((1)) := by
    rw [incr_vert k 1 (4) (1) (Or.inl rfl) (mem_raw_of_box k (4) (1) (by omega)) (mem_raw_of_box k (4) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((2), (1)) = -((1)) := by
    rw [incr_vert k 1 (2) (1) (Or.inl rfl) (mem_raw_of_box k (2) (1) (by omega)) (mem_raw_of_box k (2) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_5_0_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((5), (0)) ≤ incr (reciprocalField k) (0, 1) ((7), (0)) ∧
    incr (reciprocalField k) (0, 1) ((5), (0)) - incr (reciprocalField k) (0, 1) ((4), (1)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((5), (0)) - incr (reciprocalField k) (0, 1) ((6), (1)) ≤ 1 := by
  have hZ2_0 : incr (reciprocalField k) (0, 1) ((7), (0)) = incr (reciprocalField k) (0, 1) ((8 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) + ((2 * (k : ℤ) + 3) * 1 - 0) :=
    incr_eq_T k (0, 1) ((7), (0)) ((8 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) (by ext <;> (simp; try ring))
  have hZ2_1 : incr (reciprocalField k) (0, 1) ((8 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) = incr (reciprocalField k) (0, 1) ((-2 * (2 * (k : ℤ) + 3) + 8), (2 * (k : ℤ) + 3)) :=
    (incr_eq_U k (0, 1) ((-2 * (2 * (k : ℤ) + 3) + 8), (2 * (k : ℤ) + 3)) ((8 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) + 1)) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (0, 1) ((6), (1)) = incr (reciprocalField k) (0, 1) ((6 - (2 * (k : ℤ) + 3)), (0)) :=
    (incr_eq_U k (0, 1) ((6 - (2 * (k : ℤ) + 3)), (0)) ((6), (1)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (0, 1) ((5), (0)) = -((0)) := by
    rw [incr_vert k 1 (5) (0) (Or.inl rfl) (mem_raw_of_box k (5) (0) (by omega)) (mem_raw_of_box k (5) ((0) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((-2 * (2 * (k : ℤ) + 3) + 8), (2 * (k : ℤ) + 3)) = -((2 * (k : ℤ) + 3)) := by
    rw [incr_vert k 1 (-2 * (2 * (k : ℤ) + 3) + 8) (2 * (k : ℤ) + 3) (Or.inl rfl) (mem_raw_of_box k (-2 * (2 * (k : ℤ) + 3) + 8) (2 * (k : ℤ) + 3) (by omega)) (mem_raw_of_box k (-2 * (2 * (k : ℤ) + 3) + 8) ((2 * (k : ℤ) + 3) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((4), (1)) = -((1)) := by
    rw [incr_vert k 1 (4) (1) (Or.inl rfl) (mem_raw_of_box k (4) (1) (by omega)) (mem_raw_of_box k (4) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((6 - (2 * (k : ℤ) + 3)), (0)) = -((0)) := by
    rw [incr_vert k 1 (6 - (2 * (k : ℤ) + 3)) (0) (Or.inl rfl) (mem_raw_of_box k (6 - (2 * (k : ℤ) + 3)) (0) (by omega)) (mem_raw_of_box k (6 - (2 * (k : ℤ) + 3)) ((0) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_5_1_p_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((5), (1)) ≤ incr (reciprocalField k) (1, 0) ((3), (1)) ∧
    incr (reciprocalField k) (1, 0) ((5), (1)) - incr (reciprocalField k) (1, 0) ((4), (2)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((5), (1)) - incr (reciprocalField k) (1, 0) ((2), (2)) ≤ 0 := by
  have hZ1_0 : incr (reciprocalField k) (1, 0) ((5), (1)) = incr (reciprocalField k) (1, 0) ((5 - (2 * (k : ℤ) + 3)), (0)) :=
    (incr_eq_U k (1, 0) ((5 - (2 * (k : ℤ) + 3)), (0)) ((5), (1)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (1, 0) ((5 - (2 * (k : ℤ) + 3)), (0)) = min ((5 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((5 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) (5 - (2 * (k : ℤ) + 3)) (0) (mem_raw_of_box k ((5 - (2 * (k : ℤ) + 3)) + (1)) (0) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((5 - (2 * (k : ℤ) + 3)) + (1)) (0) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (0) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((3), (1)) = min ((3) + (1) - 1) 0 - min ((3) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (3) (1) (mem_raw_of_box k ((3) + (1)) (1) (by omega)) (mem_raw_of_box k (3) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (3) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((3) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (3) (1) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((4), (2)) = min ((4) + (1) - 1) 0 - min ((4) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (4) (2) (mem_raw_of_box k ((4) + (1)) (2) (by omega)) (mem_raw_of_box k (4) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (4) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((4) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (4) (2) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((2), (2)) = min ((2) + (1) - 1) 0 - min ((2) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (2) (2) (mem_raw_of_box k ((2) + (1)) (2) (by omega)) (mem_raw_of_box k (2) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (2) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((2) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (2) (2) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_5_1_m_px (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (1, 0) ((5), (1)) ≤ incr (reciprocalField k) (1, 0) ((7), (1)) ∧
    incr (reciprocalField k) (1, 0) ((5), (1)) - incr (reciprocalField k) (1, 0) ((4), (2)) ≤ 0 ∧
    incr (reciprocalField k) (1, 0) ((5), (1)) - incr (reciprocalField k) (1, 0) ((6), (2)) ≤ 0 := by
  have hZ1_0 : incr (reciprocalField k) (1, 0) ((5), (1)) = incr (reciprocalField k) (1, 0) ((5 - (2 * (k : ℤ) + 3)), (0)) :=
    (incr_eq_U k (1, 0) ((5 - (2 * (k : ℤ) + 3)), (0)) ((5), (1)) (by ext <;> (simp; try ring))).symm
  have hZ2_0 : incr (reciprocalField k) (1, 0) ((7), (1)) = incr (reciprocalField k) (1, 0) ((7 - (2 * (k : ℤ) + 3)), (0)) :=
    (incr_eq_U k (1, 0) ((7 - (2 * (k : ℤ) + 3)), (0)) ((7), (1)) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (1, 0) ((6), (2)) = incr (reciprocalField k) (1, 0) ((6 - (2 * (k : ℤ) + 3)), (1)) :=
    (incr_eq_U k (1, 0) ((6 - (2 * (k : ℤ) + 3)), (1)) ((6), (2)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (1, 0) ((5 - (2 * (k : ℤ) + 3)), (0)) = min ((5 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((5 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 1) := by
    rw [incr_hG k (1) (5 - (2 * (k : ℤ) + 3)) (0) (mem_raw_of_box k ((5 - (2 * (k : ℤ) + 3)) + (1)) (0) (by omega)) (mem_raw_corner0' k _ _ (by omega) (by omega)), hG_c_minus (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((5 - (2 * (k : ℤ) + 3)) + (1)) (0) (by omega)) (corner_yes (2 * (k : ℤ) + 3) (5 - (2 * (k : ℤ) + 3)) (0) (by omega))]
    ring
  have vZ2 : incr (reciprocalField k) (1, 0) ((7 - (2 * (k : ℤ) + 3)), (0)) = min ((7 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((7 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (7 - (2 * (k : ℤ) + 3)) (0) (mem_raw_of_box k ((7 - (2 * (k : ℤ) + 3)) + (1)) (0) (by omega)) (mem_raw_of_box k (7 - (2 * (k : ℤ) + 3)) (0) (by omega)), hG_nc (2 * (k : ℤ) + 3) (7 - (2 * (k : ℤ) + 3)) (0) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((7 - (2 * (k : ℤ) + 3)) + (1)) (0) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (7 - (2 * (k : ℤ) + 3)) (0) (by omega))]
    ring
  have vZ3 : incr (reciprocalField k) (1, 0) ((4), (2)) = min ((4) + (1) - 1) 0 - min ((4) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (4) (2) (mem_raw_of_box k ((4) + (1)) (2) (by omega)) (mem_raw_of_box k (4) (2) (by omega)), hG_nc (2 * (k : ℤ) + 3) (4) (2) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((4) + (1)) (2) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (4) (2) (by omega))]
    ring
  have vZ4 : incr (reciprocalField k) (1, 0) ((6 - (2 * (k : ℤ) + 3)), (1)) = min ((6 - (2 * (k : ℤ) + 3)) + (1) - 1) 0 - min ((6 - (2 * (k : ℤ) + 3)) - 1) 0 + (0 - 0) := by
    rw [incr_hG k (1) (6 - (2 * (k : ℤ) + 3)) (1) (mem_raw_of_box k ((6 - (2 * (k : ℤ) + 3)) + (1)) (1) (by omega)) (mem_raw_of_box k (6 - (2 * (k : ℤ) + 3)) (1) (by omega)), hG_nc (2 * (k : ℤ) + 3) (6 - (2 * (k : ℤ) + 3)) (1) (1) (not_stairCorner (2 * (k : ℤ) + 3) ((6 - (2 * (k : ℤ) + 3)) + (1)) (1) (by omega)) (not_stairCorner (2 * (k : ℤ) + 3) (6 - (2 * (k : ℤ) + 3)) (1) (by omega))]
    ring
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_5_2_p_my (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, -1) ((5), (2)) ≤ incr (reciprocalField k) (0, -1) ((3), (2)) ∧
    incr (reciprocalField k) (0, -1) ((5), (2)) - incr (reciprocalField k) (0, -1) ((4), (3)) ≤ -1 ∧
    incr (reciprocalField k) (0, -1) ((5), (2)) - incr (reciprocalField k) (0, -1) ((2), (3)) ≤ -1 := by
  have vZ1 : incr (reciprocalField k) (0, -1) ((5), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (5) (2) (Or.inr rfl) (mem_raw_of_box k (5) (2) (by omega)) (mem_raw_of_box k (5) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ2 : incr (reciprocalField k) (0, -1) ((3), (2)) = ((2)) + -1 := by
    rw [incr_vert k (-1) (3) (2) (Or.inr rfl) (mem_raw_of_box k (3) (2) (by omega)) (mem_raw_of_box k (3) ((2) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ3 : incr (reciprocalField k) (0, -1) ((4), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (4) (3) (Or.inr rfl) (mem_raw_of_box k (4) (3) (by omega)) (mem_raw_of_box k (4) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  have vZ4 : incr (reciprocalField k) (0, -1) ((2), (3)) = ((3)) + -1 := by
    rw [incr_vert k (-1) (2) (3) (Or.inr rfl) (mem_raw_of_box k (2) (3) (by omega)) (mem_raw_of_box k (2) ((3) + -1) (by omega)) (by omega) (by omega), vG_neg_one]
  exact ⟨by omega, by omega, by omega⟩

theorem tr1_5_2_m_py (k : ℕ) (hk : (k : ℤ) = 1) :
    incr (reciprocalField k) (0, 1) ((5), (2)) ≤ incr (reciprocalField k) (0, 1) ((7), (2)) ∧
    incr (reciprocalField k) (0, 1) ((5), (2)) - incr (reciprocalField k) (0, 1) ((4), (3)) ≤ 1 ∧
    incr (reciprocalField k) (0, 1) ((5), (2)) - incr (reciprocalField k) (0, 1) ((6), (3)) ≤ 1 := by
  have hZ1_0 : incr (reciprocalField k) (0, 1) ((5), (2)) = incr (reciprocalField k) (0, 1) ((5 - (2 * (k : ℤ) + 3)), (1)) :=
    (incr_eq_U k (0, 1) ((5 - (2 * (k : ℤ) + 3)), (1)) ((5), (2)) (by ext <;> (simp; try ring))).symm
  have hZ2_0 : incr (reciprocalField k) (0, 1) ((7), (2)) = incr (reciprocalField k) (0, 1) ((7 - (2 * (k : ℤ) + 3)), (1)) :=
    (incr_eq_U k (0, 1) ((7 - (2 * (k : ℤ) + 3)), (1)) ((7), (2)) (by ext <;> (simp; try ring))).symm
  have hZ3_0 : incr (reciprocalField k) (0, 1) ((4), (3)) = incr (reciprocalField k) (0, 1) ((4 - (2 * (k : ℤ) + 3)), (2)) :=
    (incr_eq_U k (0, 1) ((4 - (2 * (k : ℤ) + 3)), (2)) ((4), (3)) (by ext <;> (simp; try ring))).symm
  have hZ4_0 : incr (reciprocalField k) (0, 1) ((6), (3)) = incr (reciprocalField k) (0, 1) ((6 - (2 * (k : ℤ) + 3)), (2)) :=
    (incr_eq_U k (0, 1) ((6 - (2 * (k : ℤ) + 3)), (2)) ((6), (3)) (by ext <;> (simp; try ring))).symm
  have vZ1 : incr (reciprocalField k) (0, 1) ((5 - (2 * (k : ℤ) + 3)), (1)) = -((1)) := by
    rw [incr_vert k 1 (5 - (2 * (k : ℤ) + 3)) (1) (Or.inl rfl) (mem_raw_of_box k (5 - (2 * (k : ℤ) + 3)) (1) (by omega)) (mem_raw_of_box k (5 - (2 * (k : ℤ) + 3)) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ2 : incr (reciprocalField k) (0, 1) ((7 - (2 * (k : ℤ) + 3)), (1)) = -((1)) := by
    rw [incr_vert k 1 (7 - (2 * (k : ℤ) + 3)) (1) (Or.inl rfl) (mem_raw_of_box k (7 - (2 * (k : ℤ) + 3)) (1) (by omega)) (mem_raw_of_box k (7 - (2 * (k : ℤ) + 3)) ((1) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ3 : incr (reciprocalField k) (0, 1) ((4 - (2 * (k : ℤ) + 3)), (2)) = -((2)) := by
    rw [incr_vert k 1 (4 - (2 * (k : ℤ) + 3)) (2) (Or.inl rfl) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) (2) (by omega)) (mem_raw_of_box k (4 - (2 * (k : ℤ) + 3)) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  have vZ4 : incr (reciprocalField k) (0, 1) ((6 - (2 * (k : ℤ) + 3)), (2)) = -((2)) := by
    rw [incr_vert k 1 (6 - (2 * (k : ℤ) + 3)) (2) (Or.inl rfl) (mem_raw_of_box k (6 - (2 * (k : ℤ) + 3)) (2) (by omega)) (mem_raw_of_box k (6 - (2 * (k : ℤ) + 3)) ((2) + 1) (by omega)) (by omega) (by omega), vG_one]
  exact ⟨by omega, by omega, by omega⟩


theorem cov1_m3_4_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-3 : ℤ), (4 : ℤ))) (hc : ECover k (1 : ℤ) ((-3 : ℤ), (4 : ℤ)) e) :
    SE k (1 : ℤ) ((-3 : ℤ), (4 : ℤ)) e ∧ PE k ((-3 : ℤ), (4 : ℤ)) e ∧ CE k (1 : ℤ) ((-3 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-3 : ℤ), (4 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((-3 : ℤ), (4 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_m3_4_p_my 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_m3_4_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-3 : ℤ), (4 : ℤ))) (hc : ECover k (-1 : ℤ) ((-3 : ℤ), (4 : ℤ)) e) :
    SE k (-1 : ℤ) ((-3 : ℤ), (4 : ℤ)) e ∧ PE k ((-3 : ℤ), (4 : ℤ)) e ∧ CE k (-1 : ℤ) ((-3 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-3 : ℤ), (4 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((-3 : ℤ), (4 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_m3_4_m_py 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_m3_5_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-3 : ℤ), (5 : ℤ))) (hc : ECover k (1 : ℤ) ((-3 : ℤ), (5 : ℤ)) e) :
    SE k (1 : ℤ) ((-3 : ℤ), (5 : ℤ)) e ∧ PE k ((-3 : ℤ), (5 : ℤ)) e ∧ CE k (1 : ℤ) ((-3 : ℤ), (5 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-3 : ℤ), (5 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((-3 : ℤ), (5 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_m3_5_p_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_m3_5_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-3 : ℤ), (5 : ℤ))) (hc : ECover k (-1 : ℤ) ((-3 : ℤ), (5 : ℤ)) e) :
    SE k (-1 : ℤ) ((-3 : ℤ), (5 : ℤ)) e ∧ PE k ((-3 : ℤ), (5 : ℤ)) e ∧ CE k (-1 : ℤ) ((-3 : ℤ), (5 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-3 : ℤ), (5 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((-3 : ℤ), (5 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_m3_5_m_mx 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_m3_6_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-3 : ℤ), (6 : ℤ))) (hc : ECover k (1 : ℤ) ((-3 : ℤ), (6 : ℤ)) e) :
    SE k (1 : ℤ) ((-3 : ℤ), (6 : ℤ)) e ∧ PE k ((-3 : ℤ), (6 : ℤ)) e ∧ CE k (1 : ℤ) ((-3 : ℤ), (6 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-3 : ℤ), (6 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((-3 : ℤ), (6 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_m3_6_p_my 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_m3_6_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-3 : ℤ), (6 : ℤ))) (hc : ECover k (-1 : ℤ) ((-3 : ℤ), (6 : ℤ)) e) :
    SE k (-1 : ℤ) ((-3 : ℤ), (6 : ℤ)) e ∧ PE k ((-3 : ℤ), (6 : ℤ)) e ∧ CE k (-1 : ℤ) ((-3 : ℤ), (6 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-3 : ℤ), (6 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((-3 : ℤ), (6 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_m3_6_m_py 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_m2_3_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-2 : ℤ), (3 : ℤ))) (hc : ECover k (1 : ℤ) ((-2 : ℤ), (3 : ℤ)) e) :
    SE k (1 : ℤ) ((-2 : ℤ), (3 : ℤ)) e ∧ PE k ((-2 : ℤ), (3 : ℤ)) e ∧ CE k (1 : ℤ) ((-2 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-2 : ℤ), (3 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((-2 : ℤ), (3 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_m2_3_p_my 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_m2_3_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-2 : ℤ), (3 : ℤ))) (hc : ECover k (-1 : ℤ) ((-2 : ℤ), (3 : ℤ)) e) :
    SE k (-1 : ℤ) ((-2 : ℤ), (3 : ℤ)) e ∧ PE k ((-2 : ℤ), (3 : ℤ)) e ∧ CE k (-1 : ℤ) ((-2 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-2 : ℤ), (3 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((-2 : ℤ), (3 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_m2_3_m_py 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_m2_4_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-2 : ℤ), (4 : ℤ))) (hc : ECover k (1 : ℤ) ((-2 : ℤ), (4 : ℤ)) e) :
    SE k (1 : ℤ) ((-2 : ℤ), (4 : ℤ)) e ∧ PE k ((-2 : ℤ), (4 : ℤ)) e ∧ CE k (1 : ℤ) ((-2 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-2 : ℤ), (4 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((-2 : ℤ), (4 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_m2_4_p_mx 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_m2_4_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-2 : ℤ), (4 : ℤ))) (hc : ECover k (-1 : ℤ) ((-2 : ℤ), (4 : ℤ)) e) :
    SE k (-1 : ℤ) ((-2 : ℤ), (4 : ℤ)) e ∧ PE k ((-2 : ℤ), (4 : ℤ)) e ∧ CE k (-1 : ℤ) ((-2 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-2 : ℤ), (4 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((-2 : ℤ), (4 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_m2_4_m_mx 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_m2_5_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-2 : ℤ), (5 : ℤ))) (hc : ECover k (1 : ℤ) ((-2 : ℤ), (5 : ℤ)) e) :
    SE k (1 : ℤ) ((-2 : ℤ), (5 : ℤ)) e ∧ PE k ((-2 : ℤ), (5 : ℤ)) e ∧ CE k (1 : ℤ) ((-2 : ℤ), (5 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-2 : ℤ), (5 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((-2 : ℤ), (5 : ℤ)) - ((-2 : ℤ), (5 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_m2_5_p_my 1 (by norm_num)
  · have hs : incomingPos ((-2 : ℤ), (5 : ℤ)) - ((-2 : ℤ), (5 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_m2_5_p_py 1 (by norm_num)

theorem cov1_m2_5_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-2 : ℤ), (5 : ℤ))) (hc : ECover k (-1 : ℤ) ((-2 : ℤ), (5 : ℤ)) e) :
    SE k (-1 : ℤ) ((-2 : ℤ), (5 : ℤ)) e ∧ PE k ((-2 : ℤ), (5 : ℤ)) e ∧ CE k (-1 : ℤ) ((-2 : ℤ), (5 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-2 : ℤ), (5 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((-2 : ℤ), (5 : ℤ)) - ((-2 : ℤ), (5 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_m2_5_m_my 1 (by norm_num)
  · have hs : incomingPos ((-2 : ℤ), (5 : ℤ)) - ((-2 : ℤ), (5 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_m2_5_m_py 1 (by norm_num)

theorem cov1_m2_6_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-2 : ℤ), (6 : ℤ))) (hc : ECover k (1 : ℤ) ((-2 : ℤ), (6 : ℤ)) e) :
    SE k (1 : ℤ) ((-2 : ℤ), (6 : ℤ)) e ∧ PE k ((-2 : ℤ), (6 : ℤ)) e ∧ CE k (1 : ℤ) ((-2 : ℤ), (6 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-2 : ℤ), (6 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((-2 : ℤ), (6 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_m2_6_p_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_m2_6_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-2 : ℤ), (6 : ℤ))) (hc : ECover k (-1 : ℤ) ((-2 : ℤ), (6 : ℤ)) e) :
    SE k (-1 : ℤ) ((-2 : ℤ), (6 : ℤ)) e ∧ PE k ((-2 : ℤ), (6 : ℤ)) e ∧ CE k (-1 : ℤ) ((-2 : ℤ), (6 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-2 : ℤ), (6 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((-2 : ℤ), (6 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_m2_6_m_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_m1_2_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-1 : ℤ), (2 : ℤ))) (hc : ECover k (1 : ℤ) ((-1 : ℤ), (2 : ℤ)) e) :
    SE k (1 : ℤ) ((-1 : ℤ), (2 : ℤ)) e ∧ PE k ((-1 : ℤ), (2 : ℤ)) e ∧ CE k (1 : ℤ) ((-1 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-1 : ℤ), (2 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((-1 : ℤ), (2 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_m1_2_p_my 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_m1_2_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-1 : ℤ), (2 : ℤ))) (hc : ECover k (-1 : ℤ) ((-1 : ℤ), (2 : ℤ)) e) :
    SE k (-1 : ℤ) ((-1 : ℤ), (2 : ℤ)) e ∧ PE k ((-1 : ℤ), (2 : ℤ)) e ∧ CE k (-1 : ℤ) ((-1 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-1 : ℤ), (2 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((-1 : ℤ), (2 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_m1_2_m_py 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_m1_3_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-1 : ℤ), (3 : ℤ))) (hc : ECover k (1 : ℤ) ((-1 : ℤ), (3 : ℤ)) e) :
    SE k (1 : ℤ) ((-1 : ℤ), (3 : ℤ)) e ∧ PE k ((-1 : ℤ), (3 : ℤ)) e ∧ CE k (1 : ℤ) ((-1 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-1 : ℤ), (3 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((-1 : ℤ), (3 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_m1_3_p_mx 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_m1_3_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-1 : ℤ), (3 : ℤ))) (hc : ECover k (-1 : ℤ) ((-1 : ℤ), (3 : ℤ)) e) :
    SE k (-1 : ℤ) ((-1 : ℤ), (3 : ℤ)) e ∧ PE k ((-1 : ℤ), (3 : ℤ)) e ∧ CE k (-1 : ℤ) ((-1 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-1 : ℤ), (3 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((-1 : ℤ), (3 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_m1_3_m_mx 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_m1_4_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-1 : ℤ), (4 : ℤ))) (hc : ECover k (1 : ℤ) ((-1 : ℤ), (4 : ℤ)) e) :
    SE k (1 : ℤ) ((-1 : ℤ), (4 : ℤ)) e ∧ PE k ((-1 : ℤ), (4 : ℤ)) e ∧ CE k (1 : ℤ) ((-1 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-1 : ℤ), (4 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((-1 : ℤ), (4 : ℤ)) - ((-1 : ℤ), (4 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_m1_4_p_my 1 (by norm_num)
  · have hs : incomingPos ((-1 : ℤ), (4 : ℤ)) - ((-1 : ℤ), (4 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_m1_4_p_py 1 (by norm_num)

theorem cov1_m1_4_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-1 : ℤ), (4 : ℤ))) (hc : ECover k (-1 : ℤ) ((-1 : ℤ), (4 : ℤ)) e) :
    SE k (-1 : ℤ) ((-1 : ℤ), (4 : ℤ)) e ∧ PE k ((-1 : ℤ), (4 : ℤ)) e ∧ CE k (-1 : ℤ) ((-1 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-1 : ℤ), (4 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((-1 : ℤ), (4 : ℤ)) - ((-1 : ℤ), (4 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_m1_4_m_my 1 (by norm_num)
  · have hs : incomingPos ((-1 : ℤ), (4 : ℤ)) - ((-1 : ℤ), (4 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_m1_4_m_py 1 (by norm_num)

theorem cov1_m1_5_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-1 : ℤ), (5 : ℤ))) (hc : ECover k (1 : ℤ) ((-1 : ℤ), (5 : ℤ)) e) :
    SE k (1 : ℤ) ((-1 : ℤ), (5 : ℤ)) e ∧ PE k ((-1 : ℤ), (5 : ℤ)) e ∧ CE k (1 : ℤ) ((-1 : ℤ), (5 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-1 : ℤ), (5 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((-1 : ℤ), (5 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_m1_5_p_mx 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_m1_5_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-1 : ℤ), (5 : ℤ))) (hc : ECover k (-1 : ℤ) ((-1 : ℤ), (5 : ℤ)) e) :
    SE k (-1 : ℤ) ((-1 : ℤ), (5 : ℤ)) e ∧ PE k ((-1 : ℤ), (5 : ℤ)) e ∧ CE k (-1 : ℤ) ((-1 : ℤ), (5 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-1 : ℤ), (5 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((-1 : ℤ), (5 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_m1_5_m_mx 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_m1_6_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-1 : ℤ), (6 : ℤ))) (hc : ECover k (1 : ℤ) ((-1 : ℤ), (6 : ℤ)) e) :
    SE k (1 : ℤ) ((-1 : ℤ), (6 : ℤ)) e ∧ PE k ((-1 : ℤ), (6 : ℤ)) e ∧ CE k (1 : ℤ) ((-1 : ℤ), (6 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-1 : ℤ), (6 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((-1 : ℤ), (6 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_m1_6_p_py 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_m1_6_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((-1 : ℤ), (6 : ℤ))) (hc : ECover k (-1 : ℤ) ((-1 : ℤ), (6 : ℤ)) e) :
    SE k (-1 : ℤ) ((-1 : ℤ), (6 : ℤ)) e ∧ PE k ((-1 : ℤ), (6 : ℤ)) e ∧ CE k (-1 : ℤ) ((-1 : ℤ), (6 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((-1 : ℤ), (6 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((-1 : ℤ), (6 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_m1_6_m_py 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_0_0_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (0 : ℤ))) (hc : ECover k (1 : ℤ) ((0 : ℤ), (0 : ℤ)) e) :
    SE k (1 : ℤ) ((0 : ℤ), (0 : ℤ)) e ∧ PE k ((0 : ℤ), (0 : ℤ)) e ∧ CE k (1 : ℤ) ((0 : ℤ), (0 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((0 : ℤ), (0 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((0 : ℤ), (0 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_0_0_p_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_0_0_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (0 : ℤ))) (hc : ECover k (-1 : ℤ) ((0 : ℤ), (0 : ℤ)) e) :
    SE k (-1 : ℤ) ((0 : ℤ), (0 : ℤ)) e ∧ PE k ((0 : ℤ), (0 : ℤ)) e ∧ CE k (-1 : ℤ) ((0 : ℤ), (0 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((0 : ℤ), (0 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((0 : ℤ), (0 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_0_0_m_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_0_1_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (1 : ℤ))) (hc : ECover k (1 : ℤ) ((0 : ℤ), (1 : ℤ)) e) :
    SE k (1 : ℤ) ((0 : ℤ), (1 : ℤ)) e ∧ PE k ((0 : ℤ), (1 : ℤ)) e ∧ CE k (1 : ℤ) ((0 : ℤ), (1 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((0 : ℤ), (1 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((0 : ℤ), (1 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_0_1_p_my 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_0_1_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (1 : ℤ))) (hc : ECover k (-1 : ℤ) ((0 : ℤ), (1 : ℤ)) e) :
    SE k (-1 : ℤ) ((0 : ℤ), (1 : ℤ)) e ∧ PE k ((0 : ℤ), (1 : ℤ)) e ∧ CE k (-1 : ℤ) ((0 : ℤ), (1 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((0 : ℤ), (1 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((0 : ℤ), (1 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_0_1_m_py 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_0_2_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (2 : ℤ))) (hc : ECover k (1 : ℤ) ((0 : ℤ), (2 : ℤ)) e) :
    SE k (1 : ℤ) ((0 : ℤ), (2 : ℤ)) e ∧ PE k ((0 : ℤ), (2 : ℤ)) e ∧ CE k (1 : ℤ) ((0 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((0 : ℤ), (2 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((0 : ℤ), (2 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_0_2_p_mx 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_0_2_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (2 : ℤ))) (hc : ECover k (-1 : ℤ) ((0 : ℤ), (2 : ℤ)) e) :
    SE k (-1 : ℤ) ((0 : ℤ), (2 : ℤ)) e ∧ PE k ((0 : ℤ), (2 : ℤ)) e ∧ CE k (-1 : ℤ) ((0 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((0 : ℤ), (2 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((0 : ℤ), (2 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_0_2_m_mx 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_0_3_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (3 : ℤ))) (hc : ECover k (1 : ℤ) ((0 : ℤ), (3 : ℤ)) e) :
    SE k (1 : ℤ) ((0 : ℤ), (3 : ℤ)) e ∧ PE k ((0 : ℤ), (3 : ℤ)) e ∧ CE k (1 : ℤ) ((0 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((0 : ℤ), (3 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((0 : ℤ), (3 : ℤ)) - ((0 : ℤ), (3 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_0_3_p_my 1 (by norm_num)
  · have hs : incomingPos ((0 : ℤ), (3 : ℤ)) - ((0 : ℤ), (3 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_0_3_p_py 1 (by norm_num)

theorem cov1_0_3_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (3 : ℤ))) (hc : ECover k (-1 : ℤ) ((0 : ℤ), (3 : ℤ)) e) :
    SE k (-1 : ℤ) ((0 : ℤ), (3 : ℤ)) e ∧ PE k ((0 : ℤ), (3 : ℤ)) e ∧ CE k (-1 : ℤ) ((0 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((0 : ℤ), (3 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((0 : ℤ), (3 : ℤ)) - ((0 : ℤ), (3 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_0_3_m_my 1 (by norm_num)
  · have hs : incomingPos ((0 : ℤ), (3 : ℤ)) - ((0 : ℤ), (3 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_0_3_m_py 1 (by norm_num)

theorem cov1_0_4_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (4 : ℤ))) (hc : ECover k (1 : ℤ) ((0 : ℤ), (4 : ℤ)) e) :
    SE k (1 : ℤ) ((0 : ℤ), (4 : ℤ)) e ∧ PE k ((0 : ℤ), (4 : ℤ)) e ∧ CE k (1 : ℤ) ((0 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((0 : ℤ), (4 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((0 : ℤ), (4 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_0_4_p_mx 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_0_4_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (4 : ℤ))) (hc : ECover k (-1 : ℤ) ((0 : ℤ), (4 : ℤ)) e) :
    SE k (-1 : ℤ) ((0 : ℤ), (4 : ℤ)) e ∧ PE k ((0 : ℤ), (4 : ℤ)) e ∧ CE k (-1 : ℤ) ((0 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((0 : ℤ), (4 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((0 : ℤ), (4 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_0_4_m_mx 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_0_5_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (5 : ℤ))) (hc : ECover k (1 : ℤ) ((0 : ℤ), (5 : ℤ)) e) :
    SE k (1 : ℤ) ((0 : ℤ), (5 : ℤ)) e ∧ PE k ((0 : ℤ), (5 : ℤ)) e ∧ CE k (1 : ℤ) ((0 : ℤ), (5 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((0 : ℤ), (5 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((0 : ℤ), (5 : ℤ)) - ((0 : ℤ), (5 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_0_5_p_my 1 (by norm_num)
  · have hs : incomingPos ((0 : ℤ), (5 : ℤ)) - ((0 : ℤ), (5 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_0_5_p_py 1 (by norm_num)

theorem cov1_0_5_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (5 : ℤ))) (hc : ECover k (-1 : ℤ) ((0 : ℤ), (5 : ℤ)) e) :
    SE k (-1 : ℤ) ((0 : ℤ), (5 : ℤ)) e ∧ PE k ((0 : ℤ), (5 : ℤ)) e ∧ CE k (-1 : ℤ) ((0 : ℤ), (5 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((0 : ℤ), (5 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((0 : ℤ), (5 : ℤ)) - ((0 : ℤ), (5 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_0_5_m_my 1 (by norm_num)
  · have hs : incomingPos ((0 : ℤ), (5 : ℤ)) - ((0 : ℤ), (5 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_0_5_m_py 1 (by norm_num)

theorem cov1_0_6_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (6 : ℤ))) (hc : ECover k (1 : ℤ) ((0 : ℤ), (6 : ℤ)) e) :
    SE k (1 : ℤ) ((0 : ℤ), (6 : ℤ)) e ∧ PE k ((0 : ℤ), (6 : ℤ)) e ∧ CE k (1 : ℤ) ((0 : ℤ), (6 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((0 : ℤ), (6 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((0 : ℤ), (6 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_0_6_p_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_0_6_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (6 : ℤ))) (hc : ECover k (-1 : ℤ) ((0 : ℤ), (6 : ℤ)) e) :
    SE k (-1 : ℤ) ((0 : ℤ), (6 : ℤ)) e ∧ PE k ((0 : ℤ), (6 : ℤ)) e ∧ CE k (-1 : ℤ) ((0 : ℤ), (6 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((0 : ℤ), (6 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((0 : ℤ), (6 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_0_6_m_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_1_0_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (0 : ℤ))) (hc : ECover k (1 : ℤ) ((1 : ℤ), (0 : ℤ)) e) :
    SE k (1 : ℤ) ((1 : ℤ), (0 : ℤ)) e ∧ PE k ((1 : ℤ), (0 : ℤ)) e ∧ CE k (1 : ℤ) ((1 : ℤ), (0 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((1 : ℤ), (0 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((1 : ℤ), (0 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_0_p_my 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_1_0_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (0 : ℤ))) (hc : ECover k (-1 : ℤ) ((1 : ℤ), (0 : ℤ)) e) :
    SE k (-1 : ℤ) ((1 : ℤ), (0 : ℤ)) e ∧ PE k ((1 : ℤ), (0 : ℤ)) e ∧ CE k (-1 : ℤ) ((1 : ℤ), (0 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((1 : ℤ), (0 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((1 : ℤ), (0 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_0_m_py 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_1_1_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (1 : ℤ))) (hc : ECover k (1 : ℤ) ((1 : ℤ), (1 : ℤ)) e) :
    SE k (1 : ℤ) ((1 : ℤ), (1 : ℤ)) e ∧ PE k ((1 : ℤ), (1 : ℤ)) e ∧ CE k (1 : ℤ) ((1 : ℤ), (1 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((1 : ℤ), (1 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((1 : ℤ), (1 : ℤ)) - ((1 : ℤ), (1 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_1_p_mx 1 (by norm_num)
  · have hs : incomingPos ((1 : ℤ), (1 : ℤ)) - ((1 : ℤ), (1 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_1_p_px 1 (by norm_num)

theorem cov1_1_1_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (1 : ℤ))) (hc : ECover k (-1 : ℤ) ((1 : ℤ), (1 : ℤ)) e) :
    SE k (-1 : ℤ) ((1 : ℤ), (1 : ℤ)) e ∧ PE k ((1 : ℤ), (1 : ℤ)) e ∧ CE k (-1 : ℤ) ((1 : ℤ), (1 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((1 : ℤ), (1 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((1 : ℤ), (1 : ℤ)) - ((1 : ℤ), (1 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_1_m_mx 1 (by norm_num)
  · have hs : incomingPos ((1 : ℤ), (1 : ℤ)) - ((1 : ℤ), (1 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_1_m_px 1 (by norm_num)

theorem cov1_1_2_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (2 : ℤ))) (hc : ECover k (1 : ℤ) ((1 : ℤ), (2 : ℤ)) e) :
    SE k (1 : ℤ) ((1 : ℤ), (2 : ℤ)) e ∧ PE k ((1 : ℤ), (2 : ℤ)) e ∧ CE k (1 : ℤ) ((1 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((1 : ℤ), (2 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((1 : ℤ), (2 : ℤ)) - ((1 : ℤ), (2 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_2_p_my 1 (by norm_num)
  · have hs : incomingPos ((1 : ℤ), (2 : ℤ)) - ((1 : ℤ), (2 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_2_p_py 1 (by norm_num)

theorem cov1_1_2_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (2 : ℤ))) (hc : ECover k (-1 : ℤ) ((1 : ℤ), (2 : ℤ)) e) :
    SE k (-1 : ℤ) ((1 : ℤ), (2 : ℤ)) e ∧ PE k ((1 : ℤ), (2 : ℤ)) e ∧ CE k (-1 : ℤ) ((1 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((1 : ℤ), (2 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((1 : ℤ), (2 : ℤ)) - ((1 : ℤ), (2 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_2_m_my 1 (by norm_num)
  · have hs : incomingPos ((1 : ℤ), (2 : ℤ)) - ((1 : ℤ), (2 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_2_m_py 1 (by norm_num)

theorem cov1_1_3_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (3 : ℤ))) (hc : ECover k (1 : ℤ) ((1 : ℤ), (3 : ℤ)) e) :
    SE k (1 : ℤ) ((1 : ℤ), (3 : ℤ)) e ∧ PE k ((1 : ℤ), (3 : ℤ)) e ∧ CE k (1 : ℤ) ((1 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((1 : ℤ), (3 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((1 : ℤ), (3 : ℤ)) - ((1 : ℤ), (3 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_3_p_mx 1 (by norm_num)
  · have hs : incomingPos ((1 : ℤ), (3 : ℤ)) - ((1 : ℤ), (3 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_3_p_px 1 (by norm_num)

theorem cov1_1_3_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (3 : ℤ))) (hc : ECover k (-1 : ℤ) ((1 : ℤ), (3 : ℤ)) e) :
    SE k (-1 : ℤ) ((1 : ℤ), (3 : ℤ)) e ∧ PE k ((1 : ℤ), (3 : ℤ)) e ∧ CE k (-1 : ℤ) ((1 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((1 : ℤ), (3 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((1 : ℤ), (3 : ℤ)) - ((1 : ℤ), (3 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_3_m_mx 1 (by norm_num)
  · have hs : incomingPos ((1 : ℤ), (3 : ℤ)) - ((1 : ℤ), (3 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_3_m_px 1 (by norm_num)

theorem cov1_1_4_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (4 : ℤ))) (hc : ECover k (1 : ℤ) ((1 : ℤ), (4 : ℤ)) e) :
    SE k (1 : ℤ) ((1 : ℤ), (4 : ℤ)) e ∧ PE k ((1 : ℤ), (4 : ℤ)) e ∧ CE k (1 : ℤ) ((1 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((1 : ℤ), (4 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((1 : ℤ), (4 : ℤ)) - ((1 : ℤ), (4 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_4_p_my 1 (by norm_num)
  · have hs : incomingPos ((1 : ℤ), (4 : ℤ)) - ((1 : ℤ), (4 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_4_p_py 1 (by norm_num)

theorem cov1_1_4_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (4 : ℤ))) (hc : ECover k (-1 : ℤ) ((1 : ℤ), (4 : ℤ)) e) :
    SE k (-1 : ℤ) ((1 : ℤ), (4 : ℤ)) e ∧ PE k ((1 : ℤ), (4 : ℤ)) e ∧ CE k (-1 : ℤ) ((1 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((1 : ℤ), (4 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((1 : ℤ), (4 : ℤ)) - ((1 : ℤ), (4 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_4_m_my 1 (by norm_num)
  · have hs : incomingPos ((1 : ℤ), (4 : ℤ)) - ((1 : ℤ), (4 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_4_m_py 1 (by norm_num)

theorem cov1_1_5_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (5 : ℤ))) (hc : ECover k (1 : ℤ) ((1 : ℤ), (5 : ℤ)) e) :
    SE k (1 : ℤ) ((1 : ℤ), (5 : ℤ)) e ∧ PE k ((1 : ℤ), (5 : ℤ)) e ∧ CE k (1 : ℤ) ((1 : ℤ), (5 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((1 : ℤ), (5 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((1 : ℤ), (5 : ℤ)) - ((1 : ℤ), (5 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_5_p_mx 1 (by norm_num)
  · have hs : incomingPos ((1 : ℤ), (5 : ℤ)) - ((1 : ℤ), (5 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_5_p_px 1 (by norm_num)

theorem cov1_1_5_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (5 : ℤ))) (hc : ECover k (-1 : ℤ) ((1 : ℤ), (5 : ℤ)) e) :
    SE k (-1 : ℤ) ((1 : ℤ), (5 : ℤ)) e ∧ PE k ((1 : ℤ), (5 : ℤ)) e ∧ CE k (-1 : ℤ) ((1 : ℤ), (5 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((1 : ℤ), (5 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((1 : ℤ), (5 : ℤ)) - ((1 : ℤ), (5 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_5_m_mx 1 (by norm_num)
  · have hs : incomingPos ((1 : ℤ), (5 : ℤ)) - ((1 : ℤ), (5 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_5_m_px 1 (by norm_num)

theorem cov1_1_6_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (6 : ℤ))) (hc : ECover k (1 : ℤ) ((1 : ℤ), (6 : ℤ)) e) :
    SE k (1 : ℤ) ((1 : ℤ), (6 : ℤ)) e ∧ PE k ((1 : ℤ), (6 : ℤ)) e ∧ CE k (1 : ℤ) ((1 : ℤ), (6 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((1 : ℤ), (6 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((1 : ℤ), (6 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_6_p_py 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_1_6_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((1 : ℤ), (6 : ℤ))) (hc : ECover k (-1 : ℤ) ((1 : ℤ), (6 : ℤ)) e) :
    SE k (-1 : ℤ) ((1 : ℤ), (6 : ℤ)) e ∧ PE k ((1 : ℤ), (6 : ℤ)) e ∧ CE k (-1 : ℤ) ((1 : ℤ), (6 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((1 : ℤ), (6 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((1 : ℤ), (6 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_1_6_m_py 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_2_0_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (0 : ℤ))) (hc : ECover k (1 : ℤ) ((2 : ℤ), (0 : ℤ)) e) :
    SE k (1 : ℤ) ((2 : ℤ), (0 : ℤ)) e ∧ PE k ((2 : ℤ), (0 : ℤ)) e ∧ CE k (1 : ℤ) ((2 : ℤ), (0 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((2 : ℤ), (0 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((2 : ℤ), (0 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_2_0_p_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_2_0_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (0 : ℤ))) (hc : ECover k (-1 : ℤ) ((2 : ℤ), (0 : ℤ)) e) :
    SE k (-1 : ℤ) ((2 : ℤ), (0 : ℤ)) e ∧ PE k ((2 : ℤ), (0 : ℤ)) e ∧ CE k (-1 : ℤ) ((2 : ℤ), (0 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((2 : ℤ), (0 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((2 : ℤ), (0 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_2_0_m_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_2_1_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (1 : ℤ))) (hc : ECover k (1 : ℤ) ((2 : ℤ), (1 : ℤ)) e) :
    SE k (1 : ℤ) ((2 : ℤ), (1 : ℤ)) e ∧ PE k ((2 : ℤ), (1 : ℤ)) e ∧ CE k (1 : ℤ) ((2 : ℤ), (1 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((2 : ℤ), (1 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((2 : ℤ), (1 : ℤ)) - ((2 : ℤ), (1 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_2_1_p_my 1 (by norm_num)
  · have hs : incomingPos ((2 : ℤ), (1 : ℤ)) - ((2 : ℤ), (1 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_2_1_p_py 1 (by norm_num)

theorem cov1_2_1_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (1 : ℤ))) (hc : ECover k (-1 : ℤ) ((2 : ℤ), (1 : ℤ)) e) :
    SE k (-1 : ℤ) ((2 : ℤ), (1 : ℤ)) e ∧ PE k ((2 : ℤ), (1 : ℤ)) e ∧ CE k (-1 : ℤ) ((2 : ℤ), (1 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((2 : ℤ), (1 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((2 : ℤ), (1 : ℤ)) - ((2 : ℤ), (1 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_2_1_m_my 1 (by norm_num)
  · have hs : incomingPos ((2 : ℤ), (1 : ℤ)) - ((2 : ℤ), (1 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_2_1_m_py 1 (by norm_num)

theorem cov1_2_2_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (2 : ℤ))) (hc : ECover k (1 : ℤ) ((2 : ℤ), (2 : ℤ)) e) :
    SE k (1 : ℤ) ((2 : ℤ), (2 : ℤ)) e ∧ PE k ((2 : ℤ), (2 : ℤ)) e ∧ CE k (1 : ℤ) ((2 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((2 : ℤ), (2 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((2 : ℤ), (2 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_2_2_p_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_2_2_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (2 : ℤ))) (hc : ECover k (-1 : ℤ) ((2 : ℤ), (2 : ℤ)) e) :
    SE k (-1 : ℤ) ((2 : ℤ), (2 : ℤ)) e ∧ PE k ((2 : ℤ), (2 : ℤ)) e ∧ CE k (-1 : ℤ) ((2 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((2 : ℤ), (2 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((2 : ℤ), (2 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_2_2_m_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_2_3_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (3 : ℤ))) (hc : ECover k (1 : ℤ) ((2 : ℤ), (3 : ℤ)) e) :
    SE k (1 : ℤ) ((2 : ℤ), (3 : ℤ)) e ∧ PE k ((2 : ℤ), (3 : ℤ)) e ∧ CE k (1 : ℤ) ((2 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((2 : ℤ), (3 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((2 : ℤ), (3 : ℤ)) - ((2 : ℤ), (3 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_2_3_p_my 1 (by norm_num)
  · have hs : incomingPos ((2 : ℤ), (3 : ℤ)) - ((2 : ℤ), (3 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_2_3_p_py 1 (by norm_num)

theorem cov1_2_3_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (3 : ℤ))) (hc : ECover k (-1 : ℤ) ((2 : ℤ), (3 : ℤ)) e) :
    SE k (-1 : ℤ) ((2 : ℤ), (3 : ℤ)) e ∧ PE k ((2 : ℤ), (3 : ℤ)) e ∧ CE k (-1 : ℤ) ((2 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((2 : ℤ), (3 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((2 : ℤ), (3 : ℤ)) - ((2 : ℤ), (3 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_2_3_m_my 1 (by norm_num)
  · have hs : incomingPos ((2 : ℤ), (3 : ℤ)) - ((2 : ℤ), (3 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_2_3_m_py 1 (by norm_num)

theorem cov1_2_4_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (4 : ℤ))) (hc : ECover k (1 : ℤ) ((2 : ℤ), (4 : ℤ)) e) :
    SE k (1 : ℤ) ((2 : ℤ), (4 : ℤ)) e ∧ PE k ((2 : ℤ), (4 : ℤ)) e ∧ CE k (1 : ℤ) ((2 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((2 : ℤ), (4 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((2 : ℤ), (4 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_2_4_p_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_2_4_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (4 : ℤ))) (hc : ECover k (-1 : ℤ) ((2 : ℤ), (4 : ℤ)) e) :
    SE k (-1 : ℤ) ((2 : ℤ), (4 : ℤ)) e ∧ PE k ((2 : ℤ), (4 : ℤ)) e ∧ CE k (-1 : ℤ) ((2 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((2 : ℤ), (4 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((2 : ℤ), (4 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_2_4_m_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_2_5_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (5 : ℤ))) (hc : ECover k (1 : ℤ) ((2 : ℤ), (5 : ℤ)) e) :
    SE k (1 : ℤ) ((2 : ℤ), (5 : ℤ)) e ∧ PE k ((2 : ℤ), (5 : ℤ)) e ∧ CE k (1 : ℤ) ((2 : ℤ), (5 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((2 : ℤ), (5 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((2 : ℤ), (5 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_2_5_p_my 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_2_5_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (5 : ℤ))) (hc : ECover k (-1 : ℤ) ((2 : ℤ), (5 : ℤ)) e) :
    SE k (-1 : ℤ) ((2 : ℤ), (5 : ℤ)) e ∧ PE k ((2 : ℤ), (5 : ℤ)) e ∧ CE k (-1 : ℤ) ((2 : ℤ), (5 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((2 : ℤ), (5 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((2 : ℤ), (5 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_2_5_m_py 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_2_6_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (6 : ℤ))) (hc : ECover k (1 : ℤ) ((2 : ℤ), (6 : ℤ)) e) :
    SE k (1 : ℤ) ((2 : ℤ), (6 : ℤ)) e ∧ PE k ((2 : ℤ), (6 : ℤ)) e ∧ CE k (1 : ℤ) ((2 : ℤ), (6 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((2 : ℤ), (6 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((2 : ℤ), (6 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_2_6_p_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_2_6_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((2 : ℤ), (6 : ℤ))) (hc : ECover k (-1 : ℤ) ((2 : ℤ), (6 : ℤ)) e) :
    SE k (-1 : ℤ) ((2 : ℤ), (6 : ℤ)) e ∧ PE k ((2 : ℤ), (6 : ℤ)) e ∧ CE k (-1 : ℤ) ((2 : ℤ), (6 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((2 : ℤ), (6 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((2 : ℤ), (6 : ℤ)) = (-1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_2_6_m_mx 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_3_0_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((3 : ℤ), (0 : ℤ))) (hc : ECover k (1 : ℤ) ((3 : ℤ), (0 : ℤ)) e) :
    SE k (1 : ℤ) ((3 : ℤ), (0 : ℤ)) e ∧ PE k ((3 : ℤ), (0 : ℤ)) e ∧ CE k (1 : ℤ) ((3 : ℤ), (0 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((3 : ℤ), (0 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((3 : ℤ), (0 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_3_0_p_py 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_3_0_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((3 : ℤ), (0 : ℤ))) (hc : ECover k (-1 : ℤ) ((3 : ℤ), (0 : ℤ)) e) :
    SE k (-1 : ℤ) ((3 : ℤ), (0 : ℤ)) e ∧ PE k ((3 : ℤ), (0 : ℤ)) e ∧ CE k (-1 : ℤ) ((3 : ℤ), (0 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((3 : ℤ), (0 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((3 : ℤ), (0 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_3_0_m_py 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_3_1_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((3 : ℤ), (1 : ℤ))) (hc : ECover k (1 : ℤ) ((3 : ℤ), (1 : ℤ)) e) :
    SE k (1 : ℤ) ((3 : ℤ), (1 : ℤ)) e ∧ PE k ((3 : ℤ), (1 : ℤ)) e ∧ CE k (1 : ℤ) ((3 : ℤ), (1 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((3 : ℤ), (1 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((3 : ℤ), (1 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_3_1_p_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_3_1_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((3 : ℤ), (1 : ℤ))) (hc : ECover k (-1 : ℤ) ((3 : ℤ), (1 : ℤ)) e) :
    SE k (-1 : ℤ) ((3 : ℤ), (1 : ℤ)) e ∧ PE k ((3 : ℤ), (1 : ℤ)) e ∧ CE k (-1 : ℤ) ((3 : ℤ), (1 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((3 : ℤ), (1 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((3 : ℤ), (1 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_3_1_m_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_3_2_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((3 : ℤ), (2 : ℤ))) (hc : ECover k (1 : ℤ) ((3 : ℤ), (2 : ℤ)) e) :
    SE k (1 : ℤ) ((3 : ℤ), (2 : ℤ)) e ∧ PE k ((3 : ℤ), (2 : ℤ)) e ∧ CE k (1 : ℤ) ((3 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((3 : ℤ), (2 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((3 : ℤ), (2 : ℤ)) - ((3 : ℤ), (2 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_3_2_p_my 1 (by norm_num)
  · have hs : incomingPos ((3 : ℤ), (2 : ℤ)) - ((3 : ℤ), (2 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_3_2_p_py 1 (by norm_num)

theorem cov1_3_2_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((3 : ℤ), (2 : ℤ))) (hc : ECover k (-1 : ℤ) ((3 : ℤ), (2 : ℤ)) e) :
    SE k (-1 : ℤ) ((3 : ℤ), (2 : ℤ)) e ∧ PE k ((3 : ℤ), (2 : ℤ)) e ∧ CE k (-1 : ℤ) ((3 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((3 : ℤ), (2 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((3 : ℤ), (2 : ℤ)) - ((3 : ℤ), (2 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_3_2_m_my 1 (by norm_num)
  · have hs : incomingPos ((3 : ℤ), (2 : ℤ)) - ((3 : ℤ), (2 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_3_2_m_py 1 (by norm_num)

theorem cov1_3_3_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((3 : ℤ), (3 : ℤ))) (hc : ECover k (1 : ℤ) ((3 : ℤ), (3 : ℤ)) e) :
    SE k (1 : ℤ) ((3 : ℤ), (3 : ℤ)) e ∧ PE k ((3 : ℤ), (3 : ℤ)) e ∧ CE k (1 : ℤ) ((3 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((3 : ℤ), (3 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((3 : ℤ), (3 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_3_3_p_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_3_3_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((3 : ℤ), (3 : ℤ))) (hc : ECover k (-1 : ℤ) ((3 : ℤ), (3 : ℤ)) e) :
    SE k (-1 : ℤ) ((3 : ℤ), (3 : ℤ)) e ∧ PE k ((3 : ℤ), (3 : ℤ)) e ∧ CE k (-1 : ℤ) ((3 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((3 : ℤ), (3 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((3 : ℤ), (3 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_3_3_m_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_3_4_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((3 : ℤ), (4 : ℤ))) (hc : ECover k (1 : ℤ) ((3 : ℤ), (4 : ℤ)) e) :
    SE k (1 : ℤ) ((3 : ℤ), (4 : ℤ)) e ∧ PE k ((3 : ℤ), (4 : ℤ)) e ∧ CE k (1 : ℤ) ((3 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((3 : ℤ), (4 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((3 : ℤ), (4 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_3_4_p_my 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_3_4_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((3 : ℤ), (4 : ℤ))) (hc : ECover k (-1 : ℤ) ((3 : ℤ), (4 : ℤ)) e) :
    SE k (-1 : ℤ) ((3 : ℤ), (4 : ℤ)) e ∧ PE k ((3 : ℤ), (4 : ℤ)) e ∧ CE k (-1 : ℤ) ((3 : ℤ), (4 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((3 : ℤ), (4 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((3 : ℤ), (4 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_3_4_m_py 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_4_0_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((4 : ℤ), (0 : ℤ))) (hc : ECover k (1 : ℤ) ((4 : ℤ), (0 : ℤ)) e) :
    SE k (1 : ℤ) ((4 : ℤ), (0 : ℤ)) e ∧ PE k ((4 : ℤ), (0 : ℤ)) e ∧ CE k (1 : ℤ) ((4 : ℤ), (0 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((4 : ℤ), (0 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((4 : ℤ), (0 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_4_0_p_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_4_0_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((4 : ℤ), (0 : ℤ))) (hc : ECover k (-1 : ℤ) ((4 : ℤ), (0 : ℤ)) e) :
    SE k (-1 : ℤ) ((4 : ℤ), (0 : ℤ)) e ∧ PE k ((4 : ℤ), (0 : ℤ)) e ∧ CE k (-1 : ℤ) ((4 : ℤ), (0 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((4 : ℤ), (0 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((4 : ℤ), (0 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_4_0_m_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_4_1_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((4 : ℤ), (1 : ℤ))) (hc : ECover k (1 : ℤ) ((4 : ℤ), (1 : ℤ)) e) :
    SE k (1 : ℤ) ((4 : ℤ), (1 : ℤ)) e ∧ PE k ((4 : ℤ), (1 : ℤ)) e ∧ CE k (1 : ℤ) ((4 : ℤ), (1 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((4 : ℤ), (1 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((4 : ℤ), (1 : ℤ)) - ((4 : ℤ), (1 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_4_1_p_my 1 (by norm_num)
  · have hs : incomingPos ((4 : ℤ), (1 : ℤ)) - ((4 : ℤ), (1 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_4_1_p_py 1 (by norm_num)

theorem cov1_4_1_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((4 : ℤ), (1 : ℤ))) (hc : ECover k (-1 : ℤ) ((4 : ℤ), (1 : ℤ)) e) :
    SE k (-1 : ℤ) ((4 : ℤ), (1 : ℤ)) e ∧ PE k ((4 : ℤ), (1 : ℤ)) e ∧ CE k (-1 : ℤ) ((4 : ℤ), (1 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((4 : ℤ), (1 : ℤ)) = -1 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', he | he⟩
  · exfalso
    rw [hl] at hl'
    norm_num at hl'
  · have hs : incomingNeg ((4 : ℤ), (1 : ℤ)) - ((4 : ℤ), (1 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_4_1_m_my 1 (by norm_num)
  · have hs : incomingPos ((4 : ℤ), (1 : ℤ)) - ((4 : ℤ), (1 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_4_1_m_py 1 (by norm_num)

theorem cov1_4_2_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((4 : ℤ), (2 : ℤ))) (hc : ECover k (1 : ℤ) ((4 : ℤ), (2 : ℤ)) e) :
    SE k (1 : ℤ) ((4 : ℤ), (2 : ℤ)) e ∧ PE k ((4 : ℤ), (2 : ℤ)) e ∧ CE k (1 : ℤ) ((4 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((4 : ℤ), (2 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((4 : ℤ), (2 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_4_2_p_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_4_2_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((4 : ℤ), (2 : ℤ))) (hc : ECover k (-1 : ℤ) ((4 : ℤ), (2 : ℤ)) e) :
    SE k (-1 : ℤ) ((4 : ℤ), (2 : ℤ)) e ∧ PE k ((4 : ℤ), (2 : ℤ)) e ∧ CE k (-1 : ℤ) ((4 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((4 : ℤ), (2 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((4 : ℤ), (2 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_4_2_m_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_4_3_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((4 : ℤ), (3 : ℤ))) (hc : ECover k (1 : ℤ) ((4 : ℤ), (3 : ℤ)) e) :
    SE k (1 : ℤ) ((4 : ℤ), (3 : ℤ)) e ∧ PE k ((4 : ℤ), (3 : ℤ)) e ∧ CE k (1 : ℤ) ((4 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((4 : ℤ), (3 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((4 : ℤ), (3 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_4_3_p_my 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_4_3_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((4 : ℤ), (3 : ℤ))) (hc : ECover k (-1 : ℤ) ((4 : ℤ), (3 : ℤ)) e) :
    SE k (-1 : ℤ) ((4 : ℤ), (3 : ℤ)) e ∧ PE k ((4 : ℤ), (3 : ℤ)) e ∧ CE k (-1 : ℤ) ((4 : ℤ), (3 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((4 : ℤ), (3 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((4 : ℤ), (3 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_4_3_m_py 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_5_0_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((5 : ℤ), (0 : ℤ))) (hc : ECover k (1 : ℤ) ((5 : ℤ), (0 : ℤ)) e) :
    SE k (1 : ℤ) ((5 : ℤ), (0 : ℤ)) e ∧ PE k ((5 : ℤ), (0 : ℤ)) e ∧ CE k (1 : ℤ) ((5 : ℤ), (0 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((5 : ℤ), (0 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((5 : ℤ), (0 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_5_0_p_py 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_5_0_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((5 : ℤ), (0 : ℤ))) (hc : ECover k (-1 : ℤ) ((5 : ℤ), (0 : ℤ)) e) :
    SE k (-1 : ℤ) ((5 : ℤ), (0 : ℤ)) e ∧ PE k ((5 : ℤ), (0 : ℤ)) e ∧ CE k (-1 : ℤ) ((5 : ℤ), (0 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((5 : ℤ), (0 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((5 : ℤ), (0 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_5_0_m_py 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_5_1_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((5 : ℤ), (1 : ℤ))) (hc : ECover k (1 : ℤ) ((5 : ℤ), (1 : ℤ)) e) :
    SE k (1 : ℤ) ((5 : ℤ), (1 : ℤ)) e ∧ PE k ((5 : ℤ), (1 : ℤ)) e ∧ CE k (1 : ℤ) ((5 : ℤ), (1 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((5 : ℤ), (1 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((5 : ℤ), (1 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_5_1_p_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_5_1_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((5 : ℤ), (1 : ℤ))) (hc : ECover k (-1 : ℤ) ((5 : ℤ), (1 : ℤ)) e) :
    SE k (-1 : ℤ) ((5 : ℤ), (1 : ℤ)) e ∧ PE k ((5 : ℤ), (1 : ℤ)) e ∧ CE k (-1 : ℤ) ((5 : ℤ), (1 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((5 : ℤ), (1 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((5 : ℤ), (1 : ℤ)) = (1, 0) := by decide
    rw [hs] at he
    subst he
    exact tr1_5_1_m_px 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_5_2_p (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((5 : ℤ), (2 : ℤ))) (hc : ECover k (1 : ℤ) ((5 : ℤ), (2 : ℤ)) e) :
    SE k (1 : ℤ) ((5 : ℤ), (2 : ℤ)) e ∧ PE k ((5 : ℤ), (2 : ℤ)) e ∧ CE k (1 : ℤ) ((5 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((5 : ℤ), (2 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (1 : ℤ) ((5 : ℤ), (2 : ℤ)) = (0, -1) := by decide
    rw [hs] at he
    subst he
    exact tr1_5_2_p_my 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cov1_5_2_m (k : ℕ) (hk : (k : ℤ) = 1) (e : Site)
    (hN : NativeP (2 * (k : ℤ) + 3) ((5 : ℤ), (2 : ℤ))) (hc : ECover k (-1 : ℤ) ((5 : ℤ), (2 : ℤ)) e) :
    SE k (-1 : ℤ) ((5 : ℤ), (2 : ℤ)) e ∧ PE k ((5 : ℤ), (2 : ℤ)) e ∧ CE k (-1 : ℤ) ((5 : ℤ), (2 : ℤ)) e := by
  obtain rfl : k = 1 := by omega
  have hl : laplacian (reciprocalField 1) ((5 : ℤ), (2 : ℤ)) = 0 := by
    rw [laplacian_reciprocal_native 1 hN]
    decide
  rcases hc with ⟨hl', he⟩ | ⟨hl', -⟩
  · have hs : selDisp (2 * ((1 : ℕ) : ℤ) + 3) (-1 : ℤ) ((5 : ℤ), (2 : ℤ)) = (0, 1) := by decide
    rw [hs] at he
    subst he
    exact tr1_5_2_m_py 1 (by norm_num)
  · exfalso
    rw [hl] at hl'
    norm_num at hl'

theorem cover_small1 (k : ℕ) (hk : (k : ℤ) = 1) (r : Site)
    (hr : NativeP (2 * (k : ℤ) + 3) r) (η : ℤ) (hη : η = 1 ∨ η = -1) (e : Site) (hc : ECover k η r e) :
    SE k η r e ∧ PE k r e ∧ CE k η r e := by
  obtain ⟨a, b⟩ := r
  have hN := hr
  unfold NativeP at hN
  simp only [Prod.mk.injEq] at hN
  have ha1 : -3 ≤ a := by omega
  have ha2 : a ≤ 5 := by omega
  have hb1 : 0 ≤ b := by omega
  have hb2 : b ≤ 6 := by omega
  rcases hη with rfl | rfl
  · interval_cases a <;> interval_cases b
    · exfalso
      omega
    · exfalso
      omega
    · exfalso
      omega
    · exfalso
      omega
    · exact cov1_m3_4_p k hk e hr hc
    · exact cov1_m3_5_p k hk e hr hc
    · exact cov1_m3_6_p k hk e hr hc
    · exfalso
      omega
    · exfalso
      omega
    · exfalso
      omega
    · exact cov1_m2_3_p k hk e hr hc
    · exact cov1_m2_4_p k hk e hr hc
    · exact cov1_m2_5_p k hk e hr hc
    · exact cov1_m2_6_p k hk e hr hc
    · exfalso
      omega
    · exfalso
      omega
    · exact cov1_m1_2_p k hk e hr hc
    · exact cov1_m1_3_p k hk e hr hc
    · exact cov1_m1_4_p k hk e hr hc
    · exact cov1_m1_5_p k hk e hr hc
    · exact cov1_m1_6_p k hk e hr hc
    · exact cov1_0_0_p k hk e hr hc
    · exact cov1_0_1_p k hk e hr hc
    · exact cov1_0_2_p k hk e hr hc
    · exact cov1_0_3_p k hk e hr hc
    · exact cov1_0_4_p k hk e hr hc
    · exact cov1_0_5_p k hk e hr hc
    · exact cov1_0_6_p k hk e hr hc
    · exact cov1_1_0_p k hk e hr hc
    · exact cov1_1_1_p k hk e hr hc
    · exact cov1_1_2_p k hk e hr hc
    · exact cov1_1_3_p k hk e hr hc
    · exact cov1_1_4_p k hk e hr hc
    · exact cov1_1_5_p k hk e hr hc
    · exact cov1_1_6_p k hk e hr hc
    · exact cov1_2_0_p k hk e hr hc
    · exact cov1_2_1_p k hk e hr hc
    · exact cov1_2_2_p k hk e hr hc
    · exact cov1_2_3_p k hk e hr hc
    · exact cov1_2_4_p k hk e hr hc
    · exact cov1_2_5_p k hk e hr hc
    · exact cov1_2_6_p k hk e hr hc
    · exact cov1_3_0_p k hk e hr hc
    · exact cov1_3_1_p k hk e hr hc
    · exact cov1_3_2_p k hk e hr hc
    · exact cov1_3_3_p k hk e hr hc
    · exact cov1_3_4_p k hk e hr hc
    · exfalso
      omega
    · exfalso
      omega
    · exact cov1_4_0_p k hk e hr hc
    · exact cov1_4_1_p k hk e hr hc
    · exact cov1_4_2_p k hk e hr hc
    · exact cov1_4_3_p k hk e hr hc
    · exfalso
      omega
    · exfalso
      omega
    · exfalso
      omega
    · exact cov1_5_0_p k hk e hr hc
    · exact cov1_5_1_p k hk e hr hc
    · exact cov1_5_2_p k hk e hr hc
    · exfalso
      omega
    · exfalso
      omega
    · exfalso
      omega
    · exfalso
      omega
  · interval_cases a <;> interval_cases b
    · exfalso
      omega
    · exfalso
      omega
    · exfalso
      omega
    · exfalso
      omega
    · exact cov1_m3_4_m k hk e hr hc
    · exact cov1_m3_5_m k hk e hr hc
    · exact cov1_m3_6_m k hk e hr hc
    · exfalso
      omega
    · exfalso
      omega
    · exfalso
      omega
    · exact cov1_m2_3_m k hk e hr hc
    · exact cov1_m2_4_m k hk e hr hc
    · exact cov1_m2_5_m k hk e hr hc
    · exact cov1_m2_6_m k hk e hr hc
    · exfalso
      omega
    · exfalso
      omega
    · exact cov1_m1_2_m k hk e hr hc
    · exact cov1_m1_3_m k hk e hr hc
    · exact cov1_m1_4_m k hk e hr hc
    · exact cov1_m1_5_m k hk e hr hc
    · exact cov1_m1_6_m k hk e hr hc
    · exact cov1_0_0_m k hk e hr hc
    · exact cov1_0_1_m k hk e hr hc
    · exact cov1_0_2_m k hk e hr hc
    · exact cov1_0_3_m k hk e hr hc
    · exact cov1_0_4_m k hk e hr hc
    · exact cov1_0_5_m k hk e hr hc
    · exact cov1_0_6_m k hk e hr hc
    · exact cov1_1_0_m k hk e hr hc
    · exact cov1_1_1_m k hk e hr hc
    · exact cov1_1_2_m k hk e hr hc
    · exact cov1_1_3_m k hk e hr hc
    · exact cov1_1_4_m k hk e hr hc
    · exact cov1_1_5_m k hk e hr hc
    · exact cov1_1_6_m k hk e hr hc
    · exact cov1_2_0_m k hk e hr hc
    · exact cov1_2_1_m k hk e hr hc
    · exact cov1_2_2_m k hk e hr hc
    · exact cov1_2_3_m k hk e hr hc
    · exact cov1_2_4_m k hk e hr hc
    · exact cov1_2_5_m k hk e hr hc
    · exact cov1_2_6_m k hk e hr hc
    · exact cov1_3_0_m k hk e hr hc
    · exact cov1_3_1_m k hk e hr hc
    · exact cov1_3_2_m k hk e hr hc
    · exact cov1_3_3_m k hk e hr hc
    · exact cov1_3_4_m k hk e hr hc
    · exfalso
      omega
    · exfalso
      omega
    · exact cov1_4_0_m k hk e hr hc
    · exact cov1_4_1_m k hk e hr hc
    · exact cov1_4_2_m k hk e hr hc
    · exact cov1_4_3_m k hk e hr hc
    · exfalso
      omega
    · exfalso
      omega
    · exfalso
      omega
    · exact cov1_5_0_m k hk e hr hc
    · exact cov1_5_1_m k hk e hr hc
    · exact cov1_5_2_m k hk e hr hc
    · exfalso
      omega
    · exfalso
      omega
    · exfalso
      omega
    · exfalso
      omega


end FLatticePaper.EPolicy
