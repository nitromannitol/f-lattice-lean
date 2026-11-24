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

end FLatticePaper.EPolicy
