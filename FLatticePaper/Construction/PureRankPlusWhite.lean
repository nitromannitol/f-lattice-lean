import FLatticePaper.Construction.PureRankPlus

/-!
# The plus retained edges, the plus rank family and the Q_plus gate (task 118, W1 base)

`RetainedP` is the retained-edge predicate of the plus rule: the parity-axis condition, and either no white, or a free
alias translate whose plus prescription `prescribedPlus` is the direction, or a corner hit. It differs from `Retained`
only in the free hits. `qRankP` is the plus rank family on the native domain. `qplus_gate`: for a native point and a unit
edge retained by the plus rule, every plus rank of the target is below `qRankP` of the source.
-/

namespace FLatticePaper.PureRank

open Classical

/-- A free alias translate whose plus prescription is `(dx, dy)`. -/
def freeHitP (d X Y dx dy : ℤ) : Prop :=
  ∃ i j, IsAlias i j ∧ IsFreeP d (shiftP d (X, Y) i j) ∧ prescribedPlus d (shiftP d (X, Y) i j) = (dx, dy)

/-- The retained-edge predicate of the plus rule. -/
def RetainedP (d X Y dx dy : ℤ) : Prop :=
  (((X + Y) % 2 = 0 ∧ dy = 0) ∨ ((X + Y) % 2 ≠ 0 ∧ dx = 0)) ∧
    (¬ hasWhite d X Y ∨ freeHitP d X Y dx dy ∨ cgHit d X Y dx dy)

/-- Rank values transfer along equal points. -/
theorem rankOfP_congr {d : ℤ} {p q : Pt} {r : ℤ} (h : RankOfP d p r) (e : p = q) : RankOfP d q r :=
  e ▸ h

/-- The plus prescription is never `(0, 1)`. -/
theorem prescribedPlus_ne_zero_one (d : ℤ) (q : Pt) : prescribedPlus d q ≠ (0, 1) := by
  unfold prescribedPlus
  split_ifs <;> simp

theorem not_freeHitP_zero_one (d X Y : ℤ) : ¬ freeHitP d X Y 0 1 := by
  rintro ⟨i, j, -, -, h⟩
  exact prescribedPlus_ne_zero_one d _ h

theorem retainedP_witness (d X Y dx dy : ℤ)
    (hw : ∃ i j, IsAlias i j ∧ IsFreeP d (shiftP d (X, Y) i j)) (hR : RetainedP d X Y dx dy) :
    freeHitP d X Y dx dy := by
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

/-- With a free translate, the edge `(0, 1)` is not retained by the plus rule. -/
theorem not_retainedP_zero_one_of_witness (d X Y : ℤ)
    (hw : ∃ i j, IsAlias i j ∧ IsFreeP d (shiftP d (X, Y) i j)) : ¬ RetainedP d X Y 0 1 :=
  fun hR => not_freeHitP_zero_one d X Y (retainedP_witness d X Y 0 1 hw hR)

/-- A retained unit edge at a free native point is its plus prescription. -/
theorem retainedP_free_root_eq (d x y dx dy : ℤ) (hd : 3 ≤ d) (hf : IsFreeP d (x, y))
    (hR : RetainedP d x y dx dy) : prescribedPlus d (x, y) = (dx, dy) := by
  have hself : shiftP d (x, y) 0 0 = (x, y) := by simp [shiftP]
  have hw : ∃ i j, IsAlias i j ∧ IsFreeP d (shiftP d (x, y) i j) :=
    ⟨0, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, by rw [hself]; exact hf⟩
  obtain ⟨i, j, hij, hfree, hpres⟩ := retainedP_witness d x y dx dy hw hR
  by_cases h0 : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h0
    rw [hself] at hpres
    exact hpres
  · exact absurd hfree (free_translate_not_free d hd (x, y) hf i j hij h0)

/-- Without free translates the plus and minus retained edges agree. -/
theorem retainedP_iff_of_noFree (d X Y dx dy : ℤ) (hnf : noFree d X Y) :
    RetainedP d X Y dx dy ↔ Retained d X Y dx dy := by
  have hF : ¬ freeHitP d X Y dx dy := by
    rintro ⟨i, j, hij, hfree, -⟩
    exact hnf i j hij hfree
  have hF' : ¬ freeHit d X Y dx dy := by
    rintro ⟨i, j, hij, hfree, -⟩
    exact hnf i j hij hfree
  unfold RetainedP Retained
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    rcases h with h1 | h1 | h1
    · exact Or.inl h1
    · exact absurd h1 hF
    · exact Or.inr (Or.inr h1)
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    rcases h with h1 | h1 | h1
    · exact Or.inl h1
    · exact absurd h1 hF'
    · exact Or.inr (Or.inr h1)

/-! ### Per-alias checks: no free translate carries the excluded plus prescription -/

set_option maxHeartbeats 400000 in
/-- The top even point `(x, d+1)`, `x ≤ 0`: no free translate has plus prescription `(1, 0)`. -/
theorem noFreeHitP_top_even (d x : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 0)
    (hev : x % 2 = 0) : ¬ freeHitP d x (d + 1) 1 0 := by
  rintro ⟨i, j, hij, hfree, hpres⟩
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hij
  unfold IsFreeP IsHc IsVc at hfree
  unfold prescribedPlus IsHc at hpres
  simp only [shiftP, Prod.mk.injEq] at hfree hpres
  interval_cases i <;> interval_cases j <;> (split_ifs at hpres <;> simp only [Prod.mk.injEq] at hpres <;> omega)

set_option maxHeartbeats 400000 in
/-- The corner `(2, d+1)`: no free translate has plus prescription `(1, 0)`. -/
theorem noFreeHitP_corner (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) : ¬ freeHitP d 2 (d + 1) 1 0 := by
  rintro ⟨i, j, hij, hfree, hpres⟩
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hij
  unfold IsFreeP IsHc IsVc at hfree
  unfold prescribedPlus IsHc at hpres
  simp only [shiftP, Prod.mk.injEq] at hfree hpres
  interval_cases i <;> interval_cases j <;> (split_ifs at hpres <;> simp only [Prod.mk.injEq] at hpres <;> omega)

set_option maxHeartbeats 400000 in
/-- The fifth point `(d, 1)`: no free translate has plus prescription `(-1, 0)`. -/
theorem noFreeHitP_fifth_left (d : ℤ) (hd : 3 ≤ d) : ¬ freeHitP d d 1 (-1) 0 := by
  rintro ⟨i, j, hij, hfree, hpres⟩
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hij
  unfold IsFreeP IsHc IsVc at hfree
  unfold prescribedPlus IsHc at hpres
  simp only [shiftP, Prod.mk.injEq] at hfree hpres
  interval_cases i <;> interval_cases j <;> (split_ifs at hpres <;> simp only [Prod.mk.injEq] at hpres <;> omega)

theorem not_retainedP_top_even_right (d x : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 2 - d ≤ x)
    (hx2 : x ≤ 0) (hev : x % 2 = 0) : ¬ RetainedP d x (d + 1) 1 0 :=
  fun hR => noFreeHitP_top_even d x hd hdodd hx1 hx2 hev
    (retainedP_witness d x (d + 1) 1 0 (top_H_witness d x hx1 hx2) hR)

theorem not_retainedP_corner_right (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) :
    ¬ RetainedP d 2 (d + 1) 1 0 :=
  fun hR => noFreeHitP_corner d hd hdodd (retainedP_witness d 2 (d + 1) 1 0 (corner_witness d) hR)

theorem not_retainedP_fifth_left (d : ℤ) (hd : 3 ≤ d) : ¬ RetainedP d d 1 (-1) 0 :=
  fun hR => noFreeHitP_fifth_left d hd (retainedP_witness d d 1 (-1) 0 (fifth_witness d) hR)

/-! ### The plus rank family on the native domain -/

/-- The plus rank family `Q_plus` on the native domain, by the boundary conventions of `qRank`. -/
noncomputable def qRankP (d : ℤ) (p : Pt) : ℤ :=
  if IsFreeP d p then valPlus d p
  else if p.2 = d + 1 ∧ p.1 ≤ 1 then valPlus d (p.1 + d - 1, 0) + 2 * (d + 1)
  else if p = (2, d + 1) then valPlus d (2 - d, d) + 2 * d
  else if p.1 + p.2 = d + 2 then valPlus d (p.1 - d, p.2 - 1) + 2 * d
  else if p = (d, 1) then valPlus d (0, 0) + 2 * d
  else valPlus d p

theorem qRankP_free (d x y : ℤ) (hf : IsFreeP d (x, y)) : qRankP d (x, y) = valPlus d (x, y) := by
  unfold qRankP
  rw [if_pos hf]

theorem qRankP_interior (d x y : ℤ) (hf : ¬ IsFreeP d (x, y))
    (hy : y ≤ d) (h4 : x + y ≠ d + 2) (h5 : ¬ (x = d ∧ y = 1)) : qRankP d (x, y) = valPlus d (x, y) := by
  have h2 : ¬ ((x, y).2 = d + 1 ∧ (x, y).1 ≤ 1) := fun h => by dsimp only at h; omega
  have h3 : ¬ ((x, y) = (2, d + 1)) := fun h => by simp only [Prod.mk.injEq] at h; omega
  have h4' : ¬ ((x, y).1 + (x, y).2 = d + 2) := fun h => h4 h
  have h5' : ¬ ((x, y) = (d, 1)) := fun h => by simp only [Prod.mk.injEq] at h; exact h5 h
  unfold qRankP
  rw [if_neg hf, if_neg h2, if_neg h3, if_neg h4', if_neg h5']

theorem qRankP_top (d x : ℤ) (hd : 3 ≤ d) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 1) :
    qRankP d (x, d + 1) = valPlus d (x + d - 1, 0) + 2 * (d + 1) := by
  have hF : ¬ IsFreeP d (x, d + 1) := by
    unfold IsFreeP IsHc IsVc
    simp only [Prod.mk.injEq]
    omega
  have hc : (x, d + 1).2 = d + 1 ∧ (x, d + 1).1 ≤ 1 := ⟨rfl, hx2⟩
  unfold qRankP
  rw [if_neg hF, if_pos hc]

theorem qRankP_top_even (d x : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 0)
    (hev : x % 2 = 0) : qRankP d (x, d + 1) = 2 * x + 4 * d - 4 := by
  rw [qRankP_top d x hd hx1 (by omega), valPlus_H_even d (x + d - 1) (by omega) (by omega) (by omega)]
  ring

theorem qRankP_top_odd (d x : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 0)
    (hod : x % 2 = 1) : qRankP d (x, d + 1) = 2 * x + 4 * d - 3 := by
  rw [qRankP_top d x hd hx1 (by omega), valPlus_H_odd d (x + d - 1) (by omega) (by omega) (by omega)]
  ring

theorem qRankP_top_one (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) : qRankP d (1, d + 1) = 4 * d - 1 := by
  rw [qRankP_top d 1 hd (by omega) le_rfl, show (1 : ℤ) + d - 1 = d by ring,
    valPlus_H_odd d d (by omega) le_rfl hdodd]
  ring

theorem qRankP_corner (d : ℤ) (hd : 3 ≤ d) : qRankP d (2, d + 1) = 4 * d := by
  have hF : ¬ IsFreeP d (2, d + 1) := by
    unfold IsFreeP IsHc IsVc
    simp only [Prod.mk.injEq]
    omega
  have h2 : ¬ (((2, d + 1) : Pt).2 = d + 1 ∧ ((2, d + 1) : Pt).1 ≤ 1) := fun h => by
    dsimp only at h
    omega
  have h3 : ((2 : ℤ), d + 1) = (2, d + 1) := rfl
  unfold qRankP
  rw [if_neg hF, if_neg h2, if_pos h3, valPlus_Vlast d hd]
  ring

theorem qRankP_anti (d x y : ℤ) (hd : 3 ≤ d) (hs : x + y = d + 2) (hx : 2 ≤ x) (hxd : x ≤ d) (hyd : y ≤ d) :
    qRankP d (x, y) = 4 * d + 1 - 2 * x := by
  have hF : ¬ IsFreeP d (x, y) := by
    unfold IsFreeP IsHc IsVc
    simp only [Prod.mk.injEq]
    omega
  have h2 : ¬ ((x, y).2 = d + 1 ∧ (x, y).1 ≤ 1) := fun h => by dsimp only at h; omega
  have h3 : ¬ ((x, y) = (2, d + 1)) := fun h => by simp only [Prod.mk.injEq] at h; omega
  have h4 : (x, y).1 + (x, y).2 = d + 2 := hs
  unfold qRankP
  rw [if_neg hF, if_neg h2, if_neg h3, if_pos h4]
  dsimp only
  have e : y - 1 = 1 - (x - d) := by omega
  rw [e, valPlus_V_odd d (x - d) (by omega) (by omega)]
  ring

theorem qRankP_fifth (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) : qRankP d (d, 1) = 2 * d := by
  have hF : ¬ IsFreeP d (d, 1) := by
    unfold IsFreeP IsHc IsVc
    simp only [Prod.mk.injEq]
    omega
  have h2 : ¬ (((d, 1) : Pt).2 = d + 1 ∧ ((d, 1) : Pt).1 ≤ 1) := fun h => by
    dsimp only at h
    omega
  have h3 : ¬ ((d, 1) = (2, d + 1)) := fun h => by simp only [Prod.mk.injEq] at h; omega
  have h4 : ¬ (((d, 1) : Pt).1 + ((d, 1) : Pt).2 = d + 2) := fun h => by
    dsimp only at h
    omega
  have h5 : ((d : ℤ), (1 : ℤ)) = (d, 1) := rfl
  unfold qRankP
  rw [if_neg hF, if_neg h2, if_neg h3, if_neg h4, if_pos h5, valPlus_origin d]
  ring

/-! ### The plus free-root gate -/

/-- **The plus free-root gate.** A free native point retaining its plus prescription: the target rank is below the value. -/
theorem free_root_gate_P (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (x y dx dy : ℤ) (hf : IsFreeP d (x, y))
    (hdir : prescribedPlus d (x, y) = (dx, dy)) (r : ℤ) (hr : RankOfP d (x + dx, y + dy) r) :
    r < valPlus d (x, y) := by
  have key : (y = 0 ∧ 1 ≤ x ∧ x ≤ d) ∨ (x = 0 ∧ y = 0) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∨
      (x = 2 - d ∧ y = d) := by
    rcases hf with hH | hV
    · exact Or.inl ⟨hH.1, hH.2.1, hH.2.2⟩
    · simp only [IsVc, Prod.mk.injEq] at hV
      omega
  unfold prescribedPlus at hdir
  rcases key with ⟨hy, hx1, hxd⟩ | ⟨hx, hy⟩ | ⟨hs, hy1, hy2⟩ | ⟨hx, hy⟩
  · subst y
    have hHc : IsHc d (x, 0) := ⟨rfl, hx1, hxd⟩
    by_cases hev : (x + 0) % 2 = 0
    · rw [if_pos hev, if_pos hHc] at hdir
      simp only [Prod.mk.injEq] at hdir
      obtain ⟨rfl, rfl⟩ := hdir
      have hxe : x % 2 = 0 := by omega
      rw [valPlus_H_even d x (by omega) hxd hxe]
      exact gateP_H_even d x hd hdodd (by omega) hxd hxe r
        (rankOfP_congr hr (by simp only [Prod.mk.injEq]; constructor <;> ring))
    · rw [if_neg hev] at hdir
      simp only [Prod.mk.injEq] at hdir
      obtain ⟨rfl, rfl⟩ := hdir
      have hxo : x % 2 = 1 := by omega
      rw [valPlus_H_odd d x hx1 hxd hxo]
      exact gateP_H_odd d x hd hdodd hx1 hxd hxo r
        (rankOfP_congr hr (by simp only [Prod.mk.injEq]; constructor <;> ring))
  · subst x
    subst y
    have hev0 : ((0 : ℤ) + 0) % 2 = 0 := by norm_num
    have hH0 : ¬ IsHc d (0, 0) := fun h => by
      have h1 : 1 ≤ (0 : ℤ) := h.2.1
      omega
    have hV0 : ¬ ((0 : ℤ), (0 : ℤ)) = (2 - d, d) := fun h => by
      simp only [Prod.mk.injEq] at h
      omega
    rw [if_pos hev0, if_neg hH0, if_neg hV0] at hdir
    simp only [Prod.mk.injEq] at hdir
    obtain ⟨rfl, rfl⟩ := hdir
    rw [valPlus_origin d]
    exact gateP_origin d hd hdodd r (rankOfP_congr hr (by simp only [Prod.mk.injEq]; constructor <;> ring))
  · have hodd : ¬ ((x + y) % 2 = 0) := by omega
    rw [if_neg hodd] at hdir
    simp only [Prod.mk.injEq] at hdir
    obtain ⟨rfl, rfl⟩ := hdir
    have hy' : y = 1 - x := by omega
    subst y
    rw [valPlus_V_odd d x (by omega) (by omega)]
    exact gateP_V_odd d x hd hdodd (by omega) (by omega) r
      (rankOfP_congr hr (by simp only [Prod.mk.injEq]; constructor <;> ring))
  · subst x
    subst y
    have hev2 : ((2 - d : ℤ) + d) % 2 = 0 := by omega
    have hH2 : ¬ IsHc d (2 - d, d) := fun h => by
      have h1 : d = 0 := h.1
      omega
    rw [if_pos hev2, if_neg hH2, if_pos (rfl : ((2 - d : ℤ), d) = (2 - d, d))] at hdir
    simp only [Prod.mk.injEq] at hdir
    obtain ⟨rfl, rfl⟩ := hdir
    rw [valPlus_Vlast d hd]
    exact gateP_Vlast d hd hdodd r (rankOfP_congr hr (by simp only [Prod.mk.injEq]; constructor <;> ring))

/-! ### The plus gate on retained unit edges -/

theorem L_top_even_P (d x dx dy : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 0)
    (hev : x % 2 = 0)
    (hunit : (dx, dy) = (1, 0) ∨ (dx, dy) = (-1, 0) ∨ (dx, dy) = (0, 1) ∨ (dx, dy) = (0, -1))
    (hR : RetainedP d x (d + 1) dx dy) (r : ℤ) (hr : RankOfP d (x + dx, d + 1 + dy) r) :
    r < qRankP d (x, d + 1) := by
  rw [qRankP_top_even d x hd hdodd hx1 hx2 hev]
  rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · exact absurd hR (not_retainedP_top_even_right d x hd hdodd hx1 hx2 hev)
  · have hr' : RankOfP d (x - 1, d + 1) r :=
      rankOfP_congr hr (by simp only [Prod.mk.injEq]; constructor <;> ring)
    exact gateP_top_even d x hd hdodd hx1 hx2 hev r hr'
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem L_top_odd_P (d x dx dy : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 0)
    (hod : x % 2 = 1)
    (hunit : (dx, dy) = (1, 0) ∨ (dx, dy) = (-1, 0) ∨ (dx, dy) = (0, 1) ∨ (dx, dy) = (0, -1))
    (hR : RetainedP d x (d + 1) dx dy) (r : ℤ) (hr : RankOfP d (x + dx, d + 1 + dy) r) :
    r < qRankP d (x, d + 1) := by
  rw [qRankP_top_odd d x hd hdodd hx1 hx2 hod]
  rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · exact absurd hR (not_retainedP_zero_one_of_witness d x (d + 1) (top_H_witness d x hx1 hx2))
  · have hr' : RankOfP d (x, d) r :=
      rankOfP_congr hr (by simp only [Prod.mk.injEq]; constructor <;> ring)
    exact gateP_top_odd d x hd hdodd hx1 hx2 hod r hr'

theorem L_top_one_P (d dx dy : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1)
    (hunit : (dx, dy) = (1, 0) ∨ (dx, dy) = (-1, 0) ∨ (dx, dy) = (0, 1) ∨ (dx, dy) = (0, -1))
    (hR : RetainedP d 1 (d + 1) dx dy) (r : ℤ) (hr : RankOfP d (1 + dx, d + 1 + dy) r) :
    r < qRankP d (1, d + 1) := by
  rw [qRankP_top_one d hd hdodd]
  rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · exact absurd hR (not_retainedP_zero_one_of_witness d 1 (d + 1) (top_one_witness d hd))
  · have hr' : RankOfP d (1, d) r :=
      rankOfP_congr hr (by simp only [Prod.mk.injEq]; constructor <;> ring)
    exact gateP_top_one d hd hdodd r hr'

theorem L_corner_P (d dx dy : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1)
    (hunit : (dx, dy) = (1, 0) ∨ (dx, dy) = (-1, 0) ∨ (dx, dy) = (0, 1) ∨ (dx, dy) = (0, -1))
    (hR : RetainedP d 2 (d + 1) dx dy) (r : ℤ) (hr : RankOfP d (2 + dx, d + 1 + dy) r) :
    r < qRankP d (2, d + 1) := by
  rw [qRankP_corner d hd]
  rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · exact absurd hR (not_retainedP_corner_right d hd hdodd)
  · have hr' : RankOfP d (1, d + 1) r :=
      rankOfP_congr hr (by simp only [Prod.mk.injEq]; constructor <;> ring)
    exact gateP_corner d hd hdodd r hr'
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem L_anti_P (d x y dx dy : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hs : x + y = d + 2) (hx : 2 ≤ x)
    (hxd : x ≤ d) (hyd : y ≤ d)
    (hunit : (dx, dy) = (1, 0) ∨ (dx, dy) = (-1, 0) ∨ (dx, dy) = (0, 1) ∨ (dx, dy) = (0, -1))
    (hR : RetainedP d x y dx dy) (r : ℤ) (hr : RankOfP d (x + dx, y + dy) r) :
    r < qRankP d (x, y) := by
  rw [qRankP_anti d x y hd hs hx hxd hyd]
  rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · exact absurd hR (not_retainedP_zero_one_of_witness d x y (anti_witness d x y hs hx hxd))
  · have hr' : RankOfP d (x, y - 1) r :=
      rankOfP_congr hr (by simp only [Prod.mk.injEq]; constructor <;> ring)
    exact gateP_anti d x y hd hdodd hs hx hxd hyd r hr'

theorem L_fifth_P (d dx dy : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1)
    (hunit : (dx, dy) = (1, 0) ∨ (dx, dy) = (-1, 0) ∨ (dx, dy) = (0, 1) ∨ (dx, dy) = (0, -1))
    (hR : RetainedP d d 1 dx dy) (r : ℤ) (hr : RankOfP d (d + dx, 1 + dy) r) :
    r < qRankP d (d, 1) := by
  rw [qRankP_fifth d hd hdodd]
  rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · have hr' : RankOfP d (d + 1, 1) r := rankOfP_congr hr (by norm_num)
    exact gateP_fifth d hd hdodd r hr'
  · exact absurd hR (not_retainedP_fifth_left d hd)
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · obtain ⟨hp, -⟩ := hR
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem L_interior_P (d x y dx dy : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y))
    (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (h4 : x + y ≠ d + 2) (h5 : ¬ (x = d ∧ y = 1))
    (hunit : (dx, dy) = (1, 0) ∨ (dx, dy) = (-1, 0) ∨ (dx, dy) = (0, 1) ∨ (dx, dy) = (0, -1))
    (hR : RetainedP d x y dx dy) (r : ℤ) (hr : RankOfP d (x + dx, y + dy) r) :
    r < qRankP d (x, y) := by
  have hnf := interior_noFree d x y hd hn hf hy h4 h5
  have hR' : Retained d x y dx dy := (retainedP_iff_of_noFree d x y dx dy hnf).1 hR
  rw [qRankP_interior d x y hf hy h4 h5]
  rcases (show (x + y) % 2 = 0 ∨ (x + y) % 2 = 1 by omega) with hpar | hodd
  · rcases (show x ≤ 0 ∨ x = 1 ∨ 2 ≤ x by omega) with hx0 | hx1 | hx2
    · rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
      · exact absurd hR' (excl_left_even_one_zero d x y hd hdodd hn hf hy h4 h5 hpar hx0)
      · have hr' : RankOfP d (x - 1, y) r := by
          rwa [show x + -1 = x - 1 by ring, show y + 0 = y by ring] at hr
        by_cases hs : x + y = 2
        · exact gateP_int_left_diag d x y hd hdodd hn hf hy hx0 hs r hr'
        · exact gateP_int_left_even d x y hd hdodd hn hf hy hx0 hpar hs r hr'
      · obtain ⟨hp, -⟩ := hR
        rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · obtain ⟨hp, -⟩ := hR
        rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
      · exact gateP_int_right_even d x y hd hdodd hn hf hy (by omega) hpar r
          (by rwa [show y + 0 = y by ring] at hr)
      · have hr' : RankOfP d (x - 1, y) r := by
          rwa [show x + -1 = x - 1 by ring, show y + 0 = y by ring] at hr
        exact gateP_int_one_left d x y hd hdodd hn hf hy hx1 hpar r hr'
      · obtain ⟨hp, -⟩ := hR
        rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · obtain ⟨hp, -⟩ := hR
        rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
      · exact gateP_int_right_even d x y hd hdodd hn hf hy (by omega) hpar r
          (by rwa [show y + 0 = y by ring] at hr)
      · exact absurd hR' (excl_right_even_neg_one d x y hd hdodd hn hf hy h4 h5 hpar hx2)
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
      · have hr' : RankOfP d (x, y + 1) r := by rwa [show x + 0 = x by ring] at hr
        exact gateP_int_odd_left_up d x y hd hdodd hn hf hy hx0 hodd r hr'
      · have hr' : RankOfP d (x, y - 1) r := by
          rwa [show x + 0 = x by ring, show y + -1 = y - 1 by ring] at hr
        exact gateP_int_odd_left_down d x y hd hdodd hn hf hy hx0 hodd r hr'
    · rcases hunit with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
      · obtain ⟨hp, -⟩ := hR
        rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · obtain ⟨hp, -⟩ := hR
        rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · have hr' : RankOfP d (x, y + 1) r := by rwa [show x + 0 = x by ring] at hr
        exact gateP_int_odd_right_up d x y hd hdodd hn hf hy h4 hx1 hodd r hr'
      · have hr' : RankOfP d (x, y - 1) r := by
          rwa [show x + 0 = x by ring, show y + -1 = y - 1 by ring] at hr
        exact gateP_int_odd_right_down d x y hd hdodd hn hf hy h4 hx1 hodd r hr'

/-- **The Q_plus gate on retained unit edges.** For every native point and every unit edge retained by the plus rule,
every plus rank of the target is below the plus rank of the source. -/
theorem qplus_gate (d x y dx dy : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y))
    (hunit : (dx, dy) = (1, 0) ∨ (dx, dy) = (-1, 0) ∨ (dx, dy) = (0, 1) ∨ (dx, dy) = (0, -1))
    (hR : RetainedP d x y dx dy) (r : ℤ) (hr : RankOfP d (x + dx, y + dy) r) : r < qRankP d (x, y) := by
  by_cases hf : IsFreeP d (x, y)
  · rw [qRankP_free d x y hf]
    exact free_root_gate_P d hd hdodd x y dx dy hf (retainedP_free_root_eq d x y dx dy hd hf hR) r hr
  · by_cases htop : y = d + 1 ∧ x ≤ 1
    · obtain ⟨rfl, hx1⟩ := htop
      have hb : 2 - d ≤ x := by
        unfold NativeP at hn
        simp only [Prod.mk.injEq] at hn
        omega
      rcases (show (x % 2 = 0 ∧ x ≤ 0) ∨ (x % 2 = 1 ∧ x ≤ 0) ∨ x = 1 by omega) with
        ⟨hev, hx0⟩ | ⟨hod, hx0⟩ | hx1'
      · exact L_top_even_P d x dx dy hd hdodd hb hx0 hev hunit hR r hr
      · exact L_top_odd_P d x dx dy hd hdodd hb hx0 hod hunit hR r hr
      · subst hx1'
        exact L_top_one_P d dx dy hd hdodd hunit hR r hr
    by_cases hc : x = 2 ∧ y = d + 1
    · obtain ⟨rfl, rfl⟩ := hc
      exact L_corner_P d dx dy hd hdodd hunit hR r hr
    by_cases ha : x + y = d + 2 ∧ y ≤ d
    · obtain ⟨hs, hyd⟩ := ha
      have hx2 : 2 ≤ x := by omega
      have hxd : x ≤ d := by
        unfold NativeP at hn
        simp only [Prod.mk.injEq] at hn
        omega
      exact L_anti_P d x y dx dy hd hdodd hs hx2 hxd hyd hunit hR r hr
    by_cases hfi : x = d ∧ y = 1
    · obtain ⟨hxd, rfl⟩ := hfi
      rw [hxd] at hR hr ⊢
      exact L_fifth_P d dx dy hd hdodd hunit hR r hr
    · have hyd : y ≤ d := by
        unfold NativeP at hn
        simp only [Prod.mk.injEq] at hn
        omega
      have h4 : x + y ≠ d + 2 := fun h => ha ⟨h, hyd⟩
      exact L_interior_P d x y dx dy hd hdodd hn hf hyd h4 hfi hunit hR r hr

end FLatticePaper.PureRank
