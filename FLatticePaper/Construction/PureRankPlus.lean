import FLatticePaper.Construction.PureRankWhite

/-!
# The Q_plus rank (task 118, W1 base, the mirror rule)

The plus rank of prove_rank_plus.py: the value `valPlus` at a representative, with the alias offset `−i·2d − j·2(d+1)`.
The representatives are the same as for Q_minus (they depend only on the geometry), so the uniqueness argument of
`PureRank` carries over with the index.
-/

namespace FLatticePaper.PureRank

open Classical

/-- The plus value at a point (prove_rank_plus.py `val`). -/
noncomputable def valPlus (d : ℤ) (p : Pt) : ℤ :=
  let p0 := (p.1 + p.2) % 2
  if IsHc d p then 2 * p.1 + p0 - 4
  else if IsVc d p then 2 * p.2 - p0
  else if p.1 ≤ 0 ∧ p.1 + p.2 = 2 then 2 * p.2
  else if p.1 ≤ 0 then 2 * p.1 + 4 * d - 4 + p0
  else 4 * d - 2 * p.1 + p0

/-- The plus rank of a point: some alias translate is a representative, with its offset. -/
def RankOfP (d : ℤ) (p : Pt) (r : ℤ) : Prop :=
  ∃ i j, IsAlias i j ∧ IsRepP d (shiftP d p i j) ∧ r = valPlus d (shiftP d p i j) - i * (2 * d) - j * (2 * (d + 1))

/-- The prescribed direction of a free point for the plus rule (the hits of prove_rank_plus.py). -/
noncomputable def prescribedPlus (d : ℤ) (p : Pt) : Pt :=
  if (p.1 + p.2) % 2 = 0 then (if IsHc d p then (-1, 0) else if p = (2 - d, d) then (-1, 0) else (1, 0))
  else (0, -1)

theorem valPlus_H_even (d x : ℤ) (hx1 : 2 ≤ x) (hxd : x ≤ d) (hev : x % 2 = 0) :
    valPlus d (x, 0) = 2 * x - 4 := by
  have hH : IsHc d (x, 0) := ⟨rfl, by show 1 ≤ x; omega, by show x ≤ d; omega⟩
  dsimp only [valPlus]
  rw [if_pos hH]
  show 2 * x + (x + 0) % 2 - 4 = 2 * x - 4
  omega

theorem valPlus_H_odd (d x : ℤ) (hx : 1 ≤ x) (hxd : x ≤ d) (hodd : x % 2 = 1) :
    valPlus d (x, 0) = 2 * x - 3 := by
  have hH : IsHc d (x, 0) := ⟨rfl, by show 1 ≤ x; omega, by show x ≤ d; omega⟩
  dsimp only [valPlus]
  rw [if_pos hH]
  show 2 * x + (x + 0) % 2 - 4 = 2 * x - 3
  omega

theorem valPlus_origin (d : ℤ) : valPlus d (0, 0) = 0 := by
  have hV : IsVc d (0, 0) := Or.inl rfl
  have hH : ¬ IsHc d (0, 0) := by
    rintro ⟨-, h1, -⟩
    have : (1 : ℤ) ≤ 0 := h1
    omega
  dsimp only [valPlus]
  rw [if_neg hH, if_pos hV]
  show 2 * 0 - (0 + 0) % 2 = 0
  norm_num

theorem valPlus_Vlast (d : ℤ) (hd : 3 ≤ d) : valPlus d (2 - d, d) = 2 * d := by
  have hV : IsVc d (2 - d, d) := Or.inr (Or.inr rfl)
  have hH : ¬ IsHc d (2 - d, d) := by
    rintro ⟨h1, -, -⟩
    have : d = 0 := h1
    omega
  dsimp only [valPlus]
  rw [if_neg hH, if_pos hV]
  show 2 * d - (2 - d + d) % 2 = 2 * d
  omega

theorem valPlus_V_odd (d x : ℤ) (hx1 : 2 - d ≤ x) (hx0 : x ≤ 0) :
    valPlus d (x, 1 - x) = 1 - 2 * x := by
  have hH : ¬ IsHc d (x, 1 - x) := by
    rintro ⟨h1, -, -⟩
    have : 1 - x = 0 := h1
    omega
  have hV : IsVc d (x, 1 - x) := by
    unfold IsVc
    right
    left
    exact ⟨by show x + (1 - x) = 1; ring, by show 1 ≤ 1 - x; omega, by show 1 - x < d; omega⟩
  dsimp only [valPlus]
  rw [if_neg hH, if_pos hV]
  show 2 * (1 - x) - (x + (1 - x)) % 2 = 1 - 2 * x
  omega

/-- The shift is injective on alias indices: two representative translates of a point have the same alias. -/
theorem shift_index_unique (d : ℤ) (hd : 3 ≤ d) (p : Pt) (i j i' j' : ℤ) (hi : IsAlias i j) (hi' : IsAlias i' j')
    (hrep : IsRepP d (shiftP d p i j)) (hrep' : IsRepP d (shiftP d p i' j')) : i = i' ∧ j = j' := by
  have hnat : ∀ a b, IsAlias a b → IsRepP d (shiftP d p a b) → NativeP d (shiftP d p a b) := by
    intro a b _ hr
    rcases hr with hf | ⟨hn, -, -⟩
    · exact freeP_native d hd _ hf
    · exact hn
  have hnq : NativeP d (shiftP d p i j) := hnat i j hi hrep
  have hnq' : NativeP d (shiftP d p i' j') := hnat i' j' hi' hrep'
  by_cases hk : i' - i = 0 ∧ j' - j = 0
  · omega
  · exfalso
    set q := shiftP d p i j with hqdef
    have hq' : shiftP d p i' j' = shiftP d q (i' - i) (j' - j) := by
      rw [hqdef, shiftP_shiftP]
      congr 1 <;> ring_nf
    have hwin := window_alias d hd q (shiftP d p i' j') hnq hnq' (i' - i) (j' - j) hq'
    have hki : IsAlias (i' - i) (j' - j) := by
      obtain ⟨a1, a2, a3, a4⟩ := hwin
      exact ⟨a1, a2, a3, a4⟩
    rw [hq'] at hrep'
    by_cases hqf : IsFreeP d q
    · exact absurd hrep' (not_rep_of_free_translate d hd q hqf _ _ hki hk)
    · exact absurd hrep' (not_rep_of_bulk_translate d hd q hrep hqf _ _ hki hk)

/-- The plus rank is unique. -/
theorem rankOfP_unique (d : ℤ) (hd : 3 ≤ d) (p : Pt) (r r' : ℤ) (h : RankOfP d p r) (h' : RankOfP d p r') :
    r = r' := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := h
  obtain ⟨i', j', hi', hrep', rfl⟩ := h'
  obtain ⟨rfl, rfl⟩ := shift_index_unique d hd p i j i' j' hi hi' hrep hrep'
  rfl

theorem rankOfP_top (d x : ℤ) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 1) :
    RankOfP d (x, d + 1) (valPlus d (x + d - 1, 0) + 2 * (d + 1)) := by
  have hs : shiftP d (x, d + 1) 0 (-1) = (x + d - 1, 0) := by
    simp only [shiftP, Prod.mk.injEq]
    constructor <;> ring
  refine ⟨0, -1, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, ?_⟩
  · rw [hs]
    left
    unfold IsFreeP
    left
    unfold IsHc
    exact ⟨rfl, by show 1 ≤ x + d - 1; omega, by show x + d - 1 ≤ d; omega⟩
  · rw [hs]
    ring

theorem rankOfP_corner (d : ℤ) : RankOfP d (2, d + 1) (valPlus d (2 - d, d) + 2 * d) := by
  have hs : shiftP d (2, d + 1) (-1) 0 = (2 - d, d) := by
    simp only [shiftP, Prod.mk.injEq]
    constructor <;> ring
  refine ⟨-1, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, ?_⟩
  · rw [hs]
    left
    unfold IsFreeP
    right
    unfold IsVc
    exact Or.inr (Or.inr rfl)
  · rw [hs]
    ring

theorem rankOfP_anti (d x y : ℤ) (hs : x + y = d + 2) (hxd : x ≤ d) (hyd : y ≤ d) :
    RankOfP d (x, y) (valPlus d (x - d, y - 1) + 2 * d) := by
  have e : shiftP d (x, y) (-1) 0 = (x - d, y - 1) := by
    simp only [shiftP, Prod.mk.injEq]
    constructor <;> ring
  refine ⟨-1, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, ?_⟩
  · rw [e]
    left
    unfold IsFreeP
    right
    unfold IsVc
    simp only [Prod.mk.injEq]
    omega
  · rw [e]
    ring

theorem rankOfP_fifth (d : ℤ) : RankOfP d (d, 1) (valPlus d (0, 0) + 2 * d) := by
  have e : shiftP d (d, 1) (-1) 0 = (0, 0) := by
    simp only [shiftP, Prod.mk.injEq]
    constructor <;> ring
  refine ⟨-1, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, ?_⟩
  · rw [e]
    left
    unfold IsFreeP
    right
    unfold IsVc
    exact Or.inl rfl
  · rw [e]
    ring

theorem rankOfP_self (d : ℤ) (p : Pt) (hp : IsRepP d p) : RankOfP d p (valPlus d p) := by
  refine ⟨0, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, ?_⟩
  · simpa [shiftP] using hp
  · simp [shiftP]


/-- Interior values for `x ≤ 0`, off the line `x + y = 2`. -/
theorem valPlus_int_left (d x y : ℤ) (hf : ¬ IsFreeP d (x, y)) (hx : x ≤ 0) (h2 : x + y ≠ 2) :
    valPlus d (x, y) = 2 * x + 4 * d - 4 + (x + y) % 2 := by
  have h1 : ¬ IsHc d (x, y) := fun h => hf (Or.inl h)
  have h2' : ¬ IsVc d (x, y) := fun h => hf (Or.inr h)
  have h3 : ¬ (x ≤ 0 ∧ x + y = 2) := fun h => h2 h.2
  dsimp only [valPlus]
  rw [if_neg h1, if_neg h2', if_neg h3, if_pos hx]

/-- Interior values for `x ≤ 0` on the line `x + y = 2`. -/
theorem valPlus_int_left2 (d x y : ℤ) (hf : ¬ IsFreeP d (x, y)) (hx : x ≤ 0) (hs : x + y = 2) :
    valPlus d (x, y) = 2 * y := by
  have h1 : ¬ IsHc d (x, y) := fun h => hf (Or.inl h)
  have h2' : ¬ IsVc d (x, y) := fun h => hf (Or.inr h)
  dsimp only [valPlus]
  rw [if_neg h1, if_neg h2', if_pos ⟨hx, hs⟩]

/-- Interior values for `x ≥ 1`. -/
theorem valPlus_int_right (d x y : ℤ) (hf : ¬ IsFreeP d (x, y)) (hx : 1 ≤ x) :
    valPlus d (x, y) = 4 * d - 2 * x + (x + y) % 2 := by
  have h1 : ¬ IsHc d (x, y) := fun h => hf (Or.inl h)
  have h2' : ¬ IsVc d (x, y) := fun h => hf (Or.inr h)
  have h4 : ¬ x ≤ 0 := by omega
  unfold valPlus
  simp only [h1, h2', h4, false_and, ↓reduceIte]

set_option hygiene false in
/-- The target-side analysis of a plus gate. -/
macro "gateP_tac" : tactic => `(tactic| (
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  rcases rep_cases d _ hrep with hF | hR
  all_goals
    interval_cases i <;> interval_cases j <;>
    (dsimp only [valPlus]; simp only [shiftP, IsHc, IsVc, IsFreeP, NativeP, Prod.mk.injEq] at *; split_ifs <;> omega)))

theorem gateP_H_even_im2_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 ≤ x ∧ x ≤ d ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, 0) (-2) (-1))) :
    valPlus d (shiftP d (x - 1, 0) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_even_im2_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 ≤ x ∧ x ≤ d ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, 0) (-2) 0)) :
    valPlus d (shiftP d (x - 1, 0) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_even_im2_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 ≤ x ∧ x ≤ d ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, 0) (-2) 1)) :
    valPlus d (shiftP d (x - 1, 0) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_even_im1_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 ≤ x ∧ x ≤ d ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, 0) (-1) (-1))) :
    valPlus d (shiftP d (x - 1, 0) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_even_im1_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 ≤ x ∧ x ≤ d ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, 0) (-1) 0)) :
    valPlus d (shiftP d (x - 1, 0) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_even_im1_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 ≤ x ∧ x ≤ d ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, 0) (-1) 1)) :
    valPlus d (shiftP d (x - 1, 0) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_even_i0_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 ≤ x ∧ x ≤ d ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, 0) 0 (-1))) :
    valPlus d (shiftP d (x - 1, 0) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_even_i0_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 ≤ x ∧ x ≤ d ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, 0) 0 0)) :
    valPlus d (shiftP d (x - 1, 0) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_even_i0_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 ≤ x ∧ x ≤ d ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, 0) 0 1)) :
    valPlus d (shiftP d (x - 1, 0) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_even_i1_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 ≤ x ∧ x ≤ d ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, 0) 1 (-1))) :
    valPlus d (shiftP d (x - 1, 0) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_even_i1_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 ≤ x ∧ x ≤ d ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, 0) 1 0)) :
    valPlus d (shiftP d (x - 1, 0) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_even_i1_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 ≤ x ∧ x ≤ d ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, 0) 1 1)) :
    valPlus d (shiftP d (x - 1, 0) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_even_i2_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 ≤ x ∧ x ≤ d ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, 0) 2 (-1))) :
    valPlus d (shiftP d (x - 1, 0) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_even_i2_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 ≤ x ∧ x ≤ d ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, 0) 2 0)) :
    valPlus d (shiftP d (x - 1, 0) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_even_i2_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 ≤ x ∧ x ≤ d ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, 0) 2 1)) :
    valPlus d (shiftP d (x - 1, 0) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

set_option maxHeartbeats 400000 in
/-- Free even `(x, 0)`, `2 ≤ x`: its prescribed target `(x−1, 0)` has every plus rank below `2x − 4`. -/
theorem gateP_H_even (d x : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx2 : 2 ≤ x) (hxd : x ≤ d) (hev : x % 2 = 0) (r : ℤ) (hr : RankOfP d (x - 1, 0) r) :
    r < 2 * x - 4 := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_H_even_im2_jm1 d x ⟨hd, hdodd, hx2, hxd, hev⟩ hrep
  · exact gateP_H_even_im2_j0 d x ⟨hd, hdodd, hx2, hxd, hev⟩ hrep
  · exact gateP_H_even_im2_j1 d x ⟨hd, hdodd, hx2, hxd, hev⟩ hrep
  · exact gateP_H_even_im1_jm1 d x ⟨hd, hdodd, hx2, hxd, hev⟩ hrep
  · exact gateP_H_even_im1_j0 d x ⟨hd, hdodd, hx2, hxd, hev⟩ hrep
  · exact gateP_H_even_im1_j1 d x ⟨hd, hdodd, hx2, hxd, hev⟩ hrep
  · exact gateP_H_even_i0_jm1 d x ⟨hd, hdodd, hx2, hxd, hev⟩ hrep
  · exact gateP_H_even_i0_j0 d x ⟨hd, hdodd, hx2, hxd, hev⟩ hrep
  · exact gateP_H_even_i0_j1 d x ⟨hd, hdodd, hx2, hxd, hev⟩ hrep
  · exact gateP_H_even_i1_jm1 d x ⟨hd, hdodd, hx2, hxd, hev⟩ hrep
  · exact gateP_H_even_i1_j0 d x ⟨hd, hdodd, hx2, hxd, hev⟩ hrep
  · exact gateP_H_even_i1_j1 d x ⟨hd, hdodd, hx2, hxd, hev⟩ hrep
  · exact gateP_H_even_i2_jm1 d x ⟨hd, hdodd, hx2, hxd, hev⟩ hrep
  · exact gateP_H_even_i2_j0 d x ⟨hd, hdodd, hx2, hxd, hev⟩ hrep
  · exact gateP_H_even_i2_j1 d x ⟨hd, hdodd, hx2, hxd, hev⟩ hrep

theorem gateP_origin_im2_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, 0) (-2) (-1))) :
    valPlus d (shiftP d (1, 0) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 0 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_origin_im2_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, 0) (-2) 0)) :
    valPlus d (shiftP d (1, 0) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 0 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_origin_im2_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, 0) (-2) 1)) :
    valPlus d (shiftP d (1, 0) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 0 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_origin_im1_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, 0) (-1) (-1))) :
    valPlus d (shiftP d (1, 0) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 0 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_origin_im1_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, 0) (-1) 0)) :
    valPlus d (shiftP d (1, 0) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 0 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_origin_im1_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, 0) (-1) 1)) :
    valPlus d (shiftP d (1, 0) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 0 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_origin_i0_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, 0) 0 (-1))) :
    valPlus d (shiftP d (1, 0) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 0 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_origin_i0_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, 0) 0 0)) :
    valPlus d (shiftP d (1, 0) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 0 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_origin_i0_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, 0) 0 1)) :
    valPlus d (shiftP d (1, 0) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 0 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_origin_i1_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, 0) 1 (-1))) :
    valPlus d (shiftP d (1, 0) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 0 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_origin_i1_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, 0) 1 0)) :
    valPlus d (shiftP d (1, 0) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 0 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_origin_i1_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, 0) 1 1)) :
    valPlus d (shiftP d (1, 0) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 0 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_origin_i2_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, 0) 2 (-1))) :
    valPlus d (shiftP d (1, 0) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 0 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_origin_i2_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, 0) 2 0)) :
    valPlus d (shiftP d (1, 0) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 0 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_origin_i2_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, 0) 2 1)) :
    valPlus d (shiftP d (1, 0) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 0 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

set_option maxHeartbeats 400000 in
/-- The origin: its prescribed target `(1, 0)` has every plus rank below `0`. -/
theorem gateP_origin (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (r : ℤ) (hr : RankOfP d (1, 0) r) :
    r < 0 := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_origin_im2_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_origin_im2_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_origin_im2_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_origin_im1_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_origin_im1_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_origin_im1_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_origin_i0_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_origin_i0_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_origin_i0_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_origin_i1_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_origin_i1_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_origin_i1_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_origin_i2_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_origin_i2_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_origin_i2_j1 d ⟨hd, hdodd⟩ hrep

theorem gateP_Vlast_im2_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) (-2) (-1))) :
    valPlus d (shiftP d (1 - d, d) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_im2_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) (-2) 0)) :
    valPlus d (shiftP d (1 - d, d) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_im2_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) (-2) 1)) :
    valPlus d (shiftP d (1 - d, d) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_im1_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) (-1) (-1))) :
    valPlus d (shiftP d (1 - d, d) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_im1_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) (-1) 0)) :
    valPlus d (shiftP d (1 - d, d) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_im1_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) (-1) 1)) :
    valPlus d (shiftP d (1 - d, d) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_i0_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) 0 (-1))) :
    valPlus d (shiftP d (1 - d, d) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_i0_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) 0 0)) :
    valPlus d (shiftP d (1 - d, d) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_i0_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) 0 1)) :
    valPlus d (shiftP d (1 - d, d) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_i1_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) 1 (-1))) :
    valPlus d (shiftP d (1 - d, d) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_i1_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) 1 0)) :
    valPlus d (shiftP d (1 - d, d) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_i1_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) 1 1)) :
    valPlus d (shiftP d (1 - d, d) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_i2_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) 2 (-1))) :
    valPlus d (shiftP d (1 - d, d) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_i2_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) 2 0)) :
    valPlus d (shiftP d (1 - d, d) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_Vlast_i2_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1 - d, d) 2 1)) :
    valPlus d (shiftP d (1 - d, d) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

set_option maxHeartbeats 400000 in
/-- The point `(2−d, d)`: its prescribed target `(1−d, d)` has every plus rank below `2d`. -/
theorem gateP_Vlast (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (r : ℤ) (hr : RankOfP d (1 - d, d) r) :
    r < 2 * d := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_Vlast_im2_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_im2_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_im2_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_im1_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_im1_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_im1_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_i0_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_i0_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_i0_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_i1_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_i1_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_i1_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_i2_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_i2_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_Vlast_i2_j1 d ⟨hd, hdodd⟩ hrep

theorem gateP_H_odd_im2_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) (-2) (-1))) :
    valPlus d (shiftP d (x, -1) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_im2_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) (-2) 0)) :
    valPlus d (shiftP d (x, -1) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_im2_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) (-2) 1)) :
    valPlus d (shiftP d (x, -1) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_im1_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) (-1) (-1))) :
    valPlus d (shiftP d (x, -1) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_im1_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) (-1) 0)) :
    valPlus d (shiftP d (x, -1) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_im1_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) (-1) 1)) :
    valPlus d (shiftP d (x, -1) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem gateP_H_odd_i0_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) 0 (-1))) :
    valPlus d (shiftP d (x, -1) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_i0_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) 0 0)) :
    valPlus d (shiftP d (x, -1) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_i0_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) 0 1)) :
    valPlus d (shiftP d (x, -1) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_i1_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) 1 (-1))) :
    valPlus d (shiftP d (x, -1) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_i1_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) 1 0)) :
    valPlus d (shiftP d (x, -1) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_i1_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) 1 1)) :
    valPlus d (shiftP d (x, -1) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_i2_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) 2 (-1))) :
    valPlus d (shiftP d (x, -1) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_i2_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) 2 0)) :
    valPlus d (shiftP d (x, -1) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_H_odd_i2_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 1 ≤ x ∧ x ≤ d ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, -1) 2 1)) :
    valPlus d (shiftP d (x, -1) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

set_option maxHeartbeats 400000 in
/-- Free odd `(x, 0)`, `1 ≤ x ≤ d`: its prescribed target `(x, −1)` has every plus rank below `2x − 3`. -/
theorem gateP_H_odd (d x : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 1 ≤ x) (hxd : x ≤ d) (hod : x % 2 = 1) (r : ℤ) (hr : RankOfP d (x, -1) r) :
    r < 2 * x - 3 := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_H_odd_im2_jm1 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_im2_j0 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_im2_j1 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_im1_jm1 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_im1_j0 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_im1_j1 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_i0_jm1 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_i0_j0 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_i0_j1 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_i1_jm1 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_i1_j0 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_i1_j1 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_i2_jm1 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_i2_j0 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep
  · exact gateP_H_odd_i2_j1 d x ⟨hd, hdodd, hx1, hxd, hod⟩ hrep

theorem gateP_V_odd_im2_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) (-2) (-1))) :
    valPlus d (shiftP d (x, -x) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_im2_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) (-2) 0)) :
    valPlus d (shiftP d (x, -x) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_im2_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) (-2) 1)) :
    valPlus d (shiftP d (x, -x) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_im1_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) (-1) (-1))) :
    valPlus d (shiftP d (x, -x) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_im1_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) (-1) 0)) :
    valPlus d (shiftP d (x, -x) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_im1_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) (-1) 1)) :
    valPlus d (shiftP d (x, -x) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_i0_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) 0 (-1))) :
    valPlus d (shiftP d (x, -x) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_i0_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) 0 0)) :
    valPlus d (shiftP d (x, -x) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_i0_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) 0 1)) :
    valPlus d (shiftP d (x, -x) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_i1_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) 1 (-1))) :
    valPlus d (shiftP d (x, -x) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_i1_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) 1 0)) :
    valPlus d (shiftP d (x, -x) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_i1_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) 1 1)) :
    valPlus d (shiftP d (x, -x) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_i2_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) 2 (-1))) :
    valPlus d (shiftP d (x, -x) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_i2_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) 2 0)) :
    valPlus d (shiftP d (x, -x) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gateP_V_odd_i2_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0) (hrep : IsRepP d (shiftP d (x, -x) 2 1)) :
    valPlus d (shiftP d (x, -x) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

set_option maxHeartbeats 400000 in
/-- Free odd `(x, 1−x)`, `2−d ≤ x ≤ 0`: its prescribed target `(x, −x)` has every plus rank below `1 − 2x`. -/
theorem gateP_V_odd (d x : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 2 - d ≤ x) (hx0 : x ≤ 0) (r : ℤ) (hr : RankOfP d (x, -x) r) :
    r < 1 - 2 * x := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_V_odd_im2_jm1 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_im2_j0 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_im2_j1 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_im1_jm1 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_im1_j0 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_im1_j1 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_i0_jm1 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_i0_j0 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_i0_j1 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_i1_jm1 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_i1_j0 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_i1_j1 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_i2_jm1 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_i2_j0 d x ⟨hd, hdodd, hx1, hx0⟩ hrep
  · exact gateP_V_odd_i2_j1 d x ⟨hd, hdodd, hx1, hx0⟩ hrep


/-! ## The interior and boundary plus gates (step (ii), plus sources) -/

set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_im2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-2) (-1))) :
    valPlus d (shiftP d (x - 1, y) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_im2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-2) 0)) :
    valPlus d (shiftP d (x - 1, y) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_im2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-2) 1)) :
    valPlus d (shiftP d (x - 1, y) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_im1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-1) (-1))) :
    valPlus d (shiftP d (x - 1, y) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_im1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-1) 0)) :
    valPlus d (shiftP d (x - 1, y) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_im1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-1) 1)) :
    valPlus d (shiftP d (x - 1, y) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_i0_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 0 (-1))) :
    valPlus d (shiftP d (x - 1, y) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_i0_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 0 0)) :
    valPlus d (shiftP d (x - 1, y) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_i0_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 0 1)) :
    valPlus d (shiftP d (x - 1, y) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_i1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 1 (-1))) :
    valPlus d (shiftP d (x - 1, y) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_i1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 1 0)) :
    valPlus d (shiftP d (x - 1, y) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_i1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 1 1)) :
    valPlus d (shiftP d (x - 1, y) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_i2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 2 (-1))) :
    valPlus d (shiftP d (x - 1, y) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_i2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 2 0)) :
    valPlus d (shiftP d (x - 1, y) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even_i2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 0 ∧ x + y ≠ 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 2 1)) :
    valPlus d (shiftP d (x - 1, y) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_even (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (hx0 : x ≤ 0) (hpar : (x + y) % 2 = 0) (h2 : x + y ≠ 2) (r : ℤ) (hr : RankOfP d (x - 1, y) r) :
    r < valPlus d (x, y) := by
  rw [valPlus_int_left d x y hf hx0 h2]
  have hb : 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2 := by
    unfold NativeP at hn
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hn hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  clear hn hf
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_int_left_even_im2_jm1 d x y ⟨hd, hdodd, hy, hx0, hpar, h2, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_even_im2_j0 d x y ⟨hd, hdodd, hy, hx0, hpar, h2, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_even_im2_j1 d x y ⟨hd, hdodd, hy, hx0, hpar, h2, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_even_im1_jm1 d x y ⟨hd, hdodd, hy, hx0, hpar, h2, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_even_im1_j0 d x y ⟨hd, hdodd, hy, hx0, hpar, h2, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_even_im1_j1 d x y ⟨hd, hdodd, hy, hx0, hpar, h2, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_even_i0_jm1 d x y ⟨hd, hdodd, hy, hx0, hpar, h2, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_even_i0_j0 d x y ⟨hd, hdodd, hy, hx0, hpar, h2, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_even_i0_j1 d x y ⟨hd, hdodd, hy, hx0, hpar, h2, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_even_i1_jm1 d x y ⟨hd, hdodd, hy, hx0, hpar, h2, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_even_i1_j0 d x y ⟨hd, hdodd, hy, hx0, hpar, h2, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_even_i1_j1 d x y ⟨hd, hdodd, hy, hx0, hpar, h2, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_even_i2_jm1 d x y ⟨hd, hdodd, hy, hx0, hpar, h2, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_even_i2_j0 d x y ⟨hd, hdodd, hy, hx0, hpar, h2, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_even_i2_j1 d x y ⟨hd, hdodd, hy, hx0, hpar, h2, hb1, hb2, hb3, hb4, hb5⟩ hrep


set_option maxHeartbeats 400000 in
theorem gateP_int_left_diag_im2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ x + y = 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-2) (-1))) :
    valPlus d (shiftP d (x - 1, y) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * y := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_diag_im2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ x + y = 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-2) 0)) :
    valPlus d (shiftP d (x - 1, y) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 2 * y := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_diag_im2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ x + y = 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-2) 1)) :
    valPlus d (shiftP d (x - 1, y) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 2 * y := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_diag_im1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ x + y = 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-1) (-1))) :
    valPlus d (shiftP d (x - 1, y) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * y := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_diag_im1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ x + y = 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-1) 0)) :
    valPlus d (shiftP d (x - 1, y) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 2 * y := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_diag_im1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ x + y = 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-1) 1)) :
    valPlus d (shiftP d (x - 1, y) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 2 * y := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_diag_i0_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ x + y = 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 0 (-1))) :
    valPlus d (shiftP d (x - 1, y) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * y := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_diag_i0_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ x + y = 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 0 0)) :
    valPlus d (shiftP d (x - 1, y) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 2 * y := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_diag_i0_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ x + y = 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 0 1)) :
    valPlus d (shiftP d (x - 1, y) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 2 * y := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_diag_i1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ x + y = 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 1 (-1))) :
    valPlus d (shiftP d (x - 1, y) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * y := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_diag_i1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ x + y = 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 1 0)) :
    valPlus d (shiftP d (x - 1, y) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 2 * y := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_diag_i1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ x + y = 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 1 1)) :
    valPlus d (shiftP d (x - 1, y) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 2 * y := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_diag_i2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ x + y = 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 2 (-1))) :
    valPlus d (shiftP d (x - 1, y) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * y := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_diag_i2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ x + y = 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 2 0)) :
    valPlus d (shiftP d (x - 1, y) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 2 * y := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_diag_i2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ x + y = 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 2 1)) :
    valPlus d (shiftP d (x - 1, y) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 2 * y := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_left_diag (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (_hn : NativeP d (x, y)) (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (hx0 : x ≤ 0) (hs : x + y = 2) (r : ℤ) (hr : RankOfP d (x - 1, y) r) :
    r < valPlus d (x, y) := by
  rw [valPlus_int_left2 d x y hf hx0 hs]
  have hb : 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2 := by
    unfold NativeP at _hn
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at _hn hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  clear _hn hf
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_int_left_diag_im2_jm1 d x y ⟨hd, hdodd, hy, hx0, hs, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_diag_im2_j0 d x y ⟨hd, hdodd, hy, hx0, hs, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_diag_im2_j1 d x y ⟨hd, hdodd, hy, hx0, hs, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_diag_im1_jm1 d x y ⟨hd, hdodd, hy, hx0, hs, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_diag_im1_j0 d x y ⟨hd, hdodd, hy, hx0, hs, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_diag_im1_j1 d x y ⟨hd, hdodd, hy, hx0, hs, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_diag_i0_jm1 d x y ⟨hd, hdodd, hy, hx0, hs, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_diag_i0_j0 d x y ⟨hd, hdodd, hy, hx0, hs, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_diag_i0_j1 d x y ⟨hd, hdodd, hy, hx0, hs, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_diag_i1_jm1 d x y ⟨hd, hdodd, hy, hx0, hs, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_diag_i1_j0 d x y ⟨hd, hdodd, hy, hx0, hs, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_diag_i1_j1 d x y ⟨hd, hdodd, hy, hx0, hs, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_diag_i2_jm1 d x y ⟨hd, hdodd, hy, hx0, hs, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_diag_i2_j0 d x y ⟨hd, hdodd, hy, hx0, hs, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_left_diag_i2_j1 d x y ⟨hd, hdodd, hy, hx0, hs, hb1, hb2, hb3, hb4, hb5⟩ hrep


set_option maxHeartbeats 400000 in
theorem gateP_int_right_even_im2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) (-2) (-1))) :
    valPlus d (shiftP d (x + 1, y) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_right_even_im2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) (-2) 0)) :
    valPlus d (shiftP d (x + 1, y) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_right_even_im2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) (-2) 1)) :
    valPlus d (shiftP d (x + 1, y) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_right_even_im1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) (-1) (-1))) :
    valPlus d (shiftP d (x + 1, y) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_right_even_im1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) (-1) 0)) :
    valPlus d (shiftP d (x + 1, y) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_right_even_im1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) (-1) 1)) :
    valPlus d (shiftP d (x + 1, y) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_right_even_i0_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) 0 (-1))) :
    valPlus d (shiftP d (x + 1, y) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_right_even_i0_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) 0 0)) :
    valPlus d (shiftP d (x + 1, y) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_right_even_i0_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) 0 1)) :
    valPlus d (shiftP d (x + 1, y) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_right_even_i1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) 1 (-1))) :
    valPlus d (shiftP d (x + 1, y) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_right_even_i1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) 1 0)) :
    valPlus d (shiftP d (x + 1, y) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_right_even_i1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) 1 1)) :
    valPlus d (shiftP d (x + 1, y) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_right_even_i2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) 2 (-1))) :
    valPlus d (shiftP d (x + 1, y) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_right_even_i2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) 2 0)) :
    valPlus d (shiftP d (x + 1, y) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_right_even_i2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) 2 1)) :
    valPlus d (shiftP d (x + 1, y) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_right_even (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (hx1 : 1 ≤ x) (hpar : (x + y) % 2 = 0) (r : ℤ) (hr : RankOfP d (x + 1, y) r) :
    r < valPlus d (x, y) := by
  rw [valPlus_int_right d x y hf hx1]
  have hb : 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2 := by
    unfold NativeP at hn
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hn hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  clear hn hf
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_int_right_even_im2_jm1 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_right_even_im2_j0 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_right_even_im2_j1 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_right_even_im1_jm1 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_right_even_im1_j0 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_right_even_im1_j1 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_right_even_i0_jm1 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_right_even_i0_j0 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_right_even_i0_j1 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_right_even_i1_jm1 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_right_even_i1_j0 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_right_even_i1_j1 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_right_even_i2_jm1 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_right_even_i2_j0 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_right_even_i2_j1 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep


set_option maxHeartbeats 400000 in
theorem gateP_int_one_left_im2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x = 1 ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-2) (-1))) :
    valPlus d (shiftP d (x - 1, y) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_one_left_im2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x = 1 ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-2) 0)) :
    valPlus d (shiftP d (x - 1, y) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_one_left_im2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x = 1 ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-2) 1)) :
    valPlus d (shiftP d (x - 1, y) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_one_left_im1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x = 1 ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-1) (-1))) :
    valPlus d (shiftP d (x - 1, y) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_one_left_im1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x = 1 ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-1) 0)) :
    valPlus d (shiftP d (x - 1, y) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_one_left_im1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x = 1 ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) (-1) 1)) :
    valPlus d (shiftP d (x - 1, y) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_one_left_i0_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x = 1 ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 0 (-1))) :
    valPlus d (shiftP d (x - 1, y) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_one_left_i0_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x = 1 ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 0 0)) :
    valPlus d (shiftP d (x - 1, y) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_one_left_i0_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x = 1 ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 0 1)) :
    valPlus d (shiftP d (x - 1, y) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_one_left_i1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x = 1 ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 1 (-1))) :
    valPlus d (shiftP d (x - 1, y) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_one_left_i1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x = 1 ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 1 0)) :
    valPlus d (shiftP d (x - 1, y) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_one_left_i1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x = 1 ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 1 1)) :
    valPlus d (shiftP d (x - 1, y) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_one_left_i2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x = 1 ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 2 (-1))) :
    valPlus d (shiftP d (x - 1, y) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_one_left_i2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x = 1 ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 2 0)) :
    valPlus d (shiftP d (x - 1, y) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_one_left_i2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x = 1 ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x - 1, y) 2 1)) :
    valPlus d (shiftP d (x - 1, y) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_one_left (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (hx1 : x = 1) (hpar : (x + y) % 2 = 0) (r : ℤ) (hr : RankOfP d (x - 1, y) r) :
    r < valPlus d (x, y) := by
  rw [valPlus_int_right d x y hf (by omega)]
  have hb : 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2 := by
    unfold NativeP at hn
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hn hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  clear hn hf
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_int_one_left_im2_jm1 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_one_left_im2_j0 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_one_left_im2_j1 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_one_left_im1_jm1 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_one_left_im1_j0 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_one_left_im1_j1 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_one_left_i0_jm1 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_one_left_i0_j0 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_one_left_i0_j1 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_one_left_i1_jm1 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_one_left_i1_j0 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_one_left_i1_j1 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_one_left_i2_jm1 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_one_left_i2_j0 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_one_left_i2_j1 d x y ⟨hd, hdodd, hy, hx1, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_down_im2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-2) (-1))) :
    valPlus d (shiftP d (x, y - 1) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_down_im2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-2) 0)) :
    valPlus d (shiftP d (x, y - 1) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_down_im2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-2) 1)) :
    valPlus d (shiftP d (x, y - 1) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_down_im1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-1) (-1))) :
    valPlus d (shiftP d (x, y - 1) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_down_im1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-1) 0)) :
    valPlus d (shiftP d (x, y - 1) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_down_im1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-1) 1)) :
    valPlus d (shiftP d (x, y - 1) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_down_i0_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 0 (-1))) :
    valPlus d (shiftP d (x, y - 1) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_down_i0_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 0 0)) :
    valPlus d (shiftP d (x, y - 1) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_down_i0_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 0 1)) :
    valPlus d (shiftP d (x, y - 1) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_down_i1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 1 (-1))) :
    valPlus d (shiftP d (x, y - 1) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_down_i1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 1 0)) :
    valPlus d (shiftP d (x, y - 1) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_down_i1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 1 1)) :
    valPlus d (shiftP d (x, y - 1) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_down_i2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 2 (-1))) :
    valPlus d (shiftP d (x, y - 1) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_down_i2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 2 0)) :
    valPlus d (shiftP d (x, y - 1) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_down_i2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 2 1)) :
    valPlus d (shiftP d (x, y - 1) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_down (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (hx0 : x ≤ 0) (hodd : (x + y) % 2 = 1) (r : ℤ) (hr : RankOfP d (x, y - 1) r) :
    r < valPlus d (x, y) := by
  rw [valPlus_int_left d x y hf hx0 (by omega)]
  have hb : 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2 := by
    unfold NativeP at hn
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hn hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  have hnV : ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) := by
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hf
    omega
  clear hn hf
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_int_odd_left_down_im2_jm1 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_down_im2_j0 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_down_im2_j1 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_down_im1_jm1 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_down_im1_j0 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_down_im1_j1 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_down_i0_jm1 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_down_i0_j0 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_down_i0_j1 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_down_i1_jm1 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_down_i1_j0 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_down_i1_j1 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_down_i2_jm1 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_down_i2_j0 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_down_i2_j1 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_up_im2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-2) (-1))) :
    valPlus d (shiftP d (x, y + 1) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_up_im2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-2) 0)) :
    valPlus d (shiftP d (x, y + 1) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_up_im2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-2) 1)) :
    valPlus d (shiftP d (x, y + 1) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_up_im1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-1) (-1))) :
    valPlus d (shiftP d (x, y + 1) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_up_im1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-1) 0)) :
    valPlus d (shiftP d (x, y + 1) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_up_im1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-1) 1)) :
    valPlus d (shiftP d (x, y + 1) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_up_i0_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 0 (-1))) :
    valPlus d (shiftP d (x, y + 1) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_up_i0_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 0 0)) :
    valPlus d (shiftP d (x, y + 1) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_up_i0_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 0 1)) :
    valPlus d (shiftP d (x, y + 1) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_up_i1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 1 (-1))) :
    valPlus d (shiftP d (x, y + 1) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_up_i1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 1 0)) :
    valPlus d (shiftP d (x, y + 1) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_up_i1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 1 1)) :
    valPlus d (shiftP d (x, y + 1) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_up_i2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 2 (-1))) :
    valPlus d (shiftP d (x, y + 1) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_up_i2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 2 0)) :
    valPlus d (shiftP d (x, y + 1) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_up_i2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x ≤ 0 ∧ (x + y) % 2 = 1 ∧ ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 2 1)) :
    valPlus d (shiftP d (x, y + 1) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_left_up (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (hx0 : x ≤ 0) (hodd : (x + y) % 2 = 1) (r : ℤ) (hr : RankOfP d (x, y + 1) r) :
    r < valPlus d (x, y) := by
  rw [valPlus_int_left d x y hf hx0 (by omega)]
  have hb : 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2 := by
    unfold NativeP at hn
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hn hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  have hnV : ¬ (x + y = 1 ∧ 1 ≤ y ∧ y < d) := by
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hf
    omega
  clear hn hf
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_int_odd_left_up_im2_jm1 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_up_im2_j0 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_up_im2_j1 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_up_im1_jm1 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_up_im1_j0 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_up_im1_j1 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_up_i0_jm1 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_up_i0_j0 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_up_i0_j1 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_up_i1_jm1 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_up_i1_j0 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_up_i1_j1 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_up_i2_jm1 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_up_i2_j0 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_left_up_i2_j1 d x y ⟨hd, hdodd, hy, hx0, hodd, hnV, hb1, hb2, hb3, hb4, hb5⟩ hrep


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_im2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-2) (-1))) :
    valPlus d (shiftP d (x, y - 1) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_im2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-2) 0)) :
    valPlus d (shiftP d (x, y - 1) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_im2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-2) 1)) :
    valPlus d (shiftP d (x, y - 1) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_im1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-1) (-1))) :
    valPlus d (shiftP d (x, y - 1) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_im1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-1) 0)) :
    valPlus d (shiftP d (x, y - 1) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_im1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) (-1) 1)) :
    valPlus d (shiftP d (x, y - 1) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_i0_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 0 (-1))) :
    valPlus d (shiftP d (x, y - 1) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_i0_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 0 0)) :
    valPlus d (shiftP d (x, y - 1) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_i0_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 0 1)) :
    valPlus d (shiftP d (x, y - 1) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_i1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 1 (-1))) :
    valPlus d (shiftP d (x, y - 1) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_i1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 1 0)) :
    valPlus d (shiftP d (x, y - 1) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_i1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 1 1)) :
    valPlus d (shiftP d (x, y - 1) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_i2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 2 (-1))) :
    valPlus d (shiftP d (x, y - 1) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_i2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 2 0)) :
    valPlus d (shiftP d (x, y - 1) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down_i2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y - 1) 2 1)) :
    valPlus d (shiftP d (x, y - 1) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_down (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (h4 : x + y ≠ d + 2) (hx1 : 1 ≤ x) (hodd : (x + y) % 2 = 1) (r : ℤ) (hr : RankOfP d (x, y - 1) r) :
    r < valPlus d (x, y) := by
  rw [valPlus_int_right d x y hf hx1]
  have hb : 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2 := by
    unfold NativeP at hn
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hn hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  clear hn hf
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_int_odd_right_down_im2_jm1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_im2_j0 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_im2_j1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_im1_jm1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_im1_j0 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_im1_j1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_i0_jm1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_i0_j0 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_i0_j1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_i1_jm1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_i1_j0 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_i1_j1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_i2_jm1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_i2_j0 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_down_i2_j1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_im2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-2) (-1))) :
    valPlus d (shiftP d (x, y + 1) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_im2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-2) 0)) :
    valPlus d (shiftP d (x, y + 1) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_im2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-2) 1)) :
    valPlus d (shiftP d (x, y + 1) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_im1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-1) (-1))) :
    valPlus d (shiftP d (x, y + 1) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_im1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-1) 0)) :
    valPlus d (shiftP d (x, y + 1) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_im1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) (-1) 1)) :
    valPlus d (shiftP d (x, y + 1) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_i0_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 0 (-1))) :
    valPlus d (shiftP d (x, y + 1) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_i0_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 0 0)) :
    valPlus d (shiftP d (x, y + 1) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_i0_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 0 1)) :
    valPlus d (shiftP d (x, y + 1) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_i1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 1 (-1))) :
    valPlus d (shiftP d (x, y + 1) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_i1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 1 0)) :
    valPlus d (shiftP d (x, y + 1) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_i1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 1 1)) :
    valPlus d (shiftP d (x, y + 1) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_i2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 2 (-1))) :
    valPlus d (shiftP d (x, y + 1) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_i2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 2 0)) :
    valPlus d (shiftP d (x, y + 1) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up_i2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ 1 ≤ x ∧ (x + y) % 2 = 1 ∧ x + y ≠ d + 2 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x, y + 1) 2 1)) :
    valPlus d (shiftP d (x, y + 1) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_int_odd_right_up (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (h4 : x + y ≠ d + 2) (hx1 : 1 ≤ x) (hodd : (x + y) % 2 = 1) (r : ℤ) (hr : RankOfP d (x, y + 1) r) :
    r < valPlus d (x, y) := by
  rw [valPlus_int_right d x y hf hx1]
  have hb : 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2 := by
    unfold NativeP at hn
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hn hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  clear hn hf
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_int_odd_right_up_im2_jm1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_im2_j0 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_im2_j1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_im1_jm1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_im1_j0 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_im1_j1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_i0_jm1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_i0_j0 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_i0_j1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_i1_jm1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_i1_j0 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_i1_j1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_i2_jm1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_i2_j0 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gateP_int_odd_right_up_i2_j1 d x y ⟨hd, hdodd, hy, hx1, hodd, h4, hb1, hb2, hb3, hb4, hb5⟩ hrep


set_option maxHeartbeats 400000 in
theorem gateP_top_even_im2_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) (-2) (-1))) :
    valPlus d (shiftP d (x - 1, d + 1) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_im2_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) (-2) 0)) :
    valPlus d (shiftP d (x - 1, d + 1) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_im2_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) (-2) 1)) :
    valPlus d (shiftP d (x - 1, d + 1) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_im1_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) (-1) (-1))) :
    valPlus d (shiftP d (x - 1, d + 1) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_im1_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) (-1) 0)) :
    valPlus d (shiftP d (x - 1, d + 1) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_im1_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) (-1) 1)) :
    valPlus d (shiftP d (x - 1, d + 1) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_i0_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) 0 (-1))) :
    valPlus d (shiftP d (x - 1, d + 1) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_i0_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) 0 0)) :
    valPlus d (shiftP d (x - 1, d + 1) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_i0_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) 0 1)) :
    valPlus d (shiftP d (x - 1, d + 1) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_i1_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) 1 (-1))) :
    valPlus d (shiftP d (x - 1, d + 1) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_i1_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) 1 0)) :
    valPlus d (shiftP d (x - 1, d + 1) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_i1_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) 1 1)) :
    valPlus d (shiftP d (x - 1, d + 1) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_i2_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) 2 (-1))) :
    valPlus d (shiftP d (x - 1, d + 1) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_i2_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) 2 0)) :
    valPlus d (shiftP d (x - 1, d + 1) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even_i2_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 0) (hrep : IsRepP d (shiftP d (x - 1, d + 1) 2 1)) :
    valPlus d (shiftP d (x - 1, d + 1) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 4 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_even (d x : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 0) (hev : x % 2 = 0) (r : ℤ) (hr : RankOfP d (x - 1, d + 1) r) :
    r < 2 * x + 4 * d - 4 := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_top_even_im2_jm1 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_im2_j0 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_im2_j1 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_im1_jm1 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_im1_j0 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_im1_j1 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_i0_jm1 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_i0_j0 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_i0_j1 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_i1_jm1 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_i1_j0 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_i1_j1 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_i2_jm1 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_i2_j0 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep
  · exact gateP_top_even_i2_j1 d x ⟨hd, hdodd, hx1, hx2, hev⟩ hrep


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_im2_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) (-2) (-1))) :
    valPlus d (shiftP d (x, d) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_im2_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) (-2) 0)) :
    valPlus d (shiftP d (x, d) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_im2_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) (-2) 1)) :
    valPlus d (shiftP d (x, d) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_im1_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) (-1) (-1))) :
    valPlus d (shiftP d (x, d) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_im1_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) (-1) 0)) :
    valPlus d (shiftP d (x, d) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_im1_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) (-1) 1)) :
    valPlus d (shiftP d (x, d) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_i0_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) 0 (-1))) :
    valPlus d (shiftP d (x, d) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_i0_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) 0 0)) :
    valPlus d (shiftP d (x, d) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_i0_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) 0 1)) :
    valPlus d (shiftP d (x, d) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_i1_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) 1 (-1))) :
    valPlus d (shiftP d (x, d) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_i1_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) 1 0)) :
    valPlus d (shiftP d (x, d) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_i1_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) 1 1)) :
    valPlus d (shiftP d (x, d) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_i2_jm1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) 2 (-1))) :
    valPlus d (shiftP d (x, d) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_i2_j0 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) 2 0)) :
    valPlus d (shiftP d (x, d) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd_i2_j1 (d x : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ 2 - d ≤ x ∧ x ≤ 0 ∧ x % 2 = 1) (hrep : IsRepP d (shiftP d (x, d) 2 1)) :
    valPlus d (shiftP d (x, d) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 2 * x + 4 * d - 3 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_odd (d x : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 0) (hod : x % 2 = 1) (r : ℤ) (hr : RankOfP d (x, d) r) :
    r < 2 * x + 4 * d - 3 := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_top_odd_im2_jm1 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_im2_j0 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_im2_j1 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_im1_jm1 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_im1_j0 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_im1_j1 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_i0_jm1 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_i0_j0 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_i0_j1 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_i1_jm1 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_i1_j0 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_i1_j1 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_i2_jm1 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_i2_j0 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep
  · exact gateP_top_odd_i2_j1 d x ⟨hd, hdodd, hx1, hx2, hod⟩ hrep


set_option maxHeartbeats 400000 in
theorem gateP_top_one_im2_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) (-2) (-1))) :
    valPlus d (shiftP d (1, d) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_im2_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) (-2) 0)) :
    valPlus d (shiftP d (1, d) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_im2_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) (-2) 1)) :
    valPlus d (shiftP d (1, d) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_im1_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) (-1) (-1))) :
    valPlus d (shiftP d (1, d) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_im1_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) (-1) 0)) :
    valPlus d (shiftP d (1, d) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_im1_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) (-1) 1)) :
    valPlus d (shiftP d (1, d) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_i0_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) 0 (-1))) :
    valPlus d (shiftP d (1, d) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_i0_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) 0 0)) :
    valPlus d (shiftP d (1, d) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_i0_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) 0 1)) :
    valPlus d (shiftP d (1, d) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_i1_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) 1 (-1))) :
    valPlus d (shiftP d (1, d) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_i1_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) 1 0)) :
    valPlus d (shiftP d (1, d) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_i1_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) 1 1)) :
    valPlus d (shiftP d (1, d) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_i2_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) 2 (-1))) :
    valPlus d (shiftP d (1, d) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_i2_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) 2 0)) :
    valPlus d (shiftP d (1, d) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one_i2_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d) 2 1)) :
    valPlus d (shiftP d (1, d) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d - 1 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_top_one (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (r : ℤ) (hr : RankOfP d (1, d) r) :
    r < 4 * d - 1 := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_top_one_im2_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_im2_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_im2_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_im1_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_im1_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_im1_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_i0_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_i0_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_i0_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_i1_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_i1_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_i1_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_i2_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_i2_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_top_one_i2_j1 d ⟨hd, hdodd⟩ hrep


set_option maxHeartbeats 400000 in
theorem gateP_corner_im2_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) (-2) (-1))) :
    valPlus d (shiftP d (1, d + 1) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_im2_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) (-2) 0)) :
    valPlus d (shiftP d (1, d + 1) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_im2_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) (-2) 1)) :
    valPlus d (shiftP d (1, d + 1) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_im1_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) (-1) (-1))) :
    valPlus d (shiftP d (1, d + 1) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_im1_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) (-1) 0)) :
    valPlus d (shiftP d (1, d + 1) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_im1_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) (-1) 1)) :
    valPlus d (shiftP d (1, d + 1) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_i0_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) 0 (-1))) :
    valPlus d (shiftP d (1, d + 1) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_i0_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) 0 0)) :
    valPlus d (shiftP d (1, d + 1) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_i0_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) 0 1)) :
    valPlus d (shiftP d (1, d + 1) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_i1_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) 1 (-1))) :
    valPlus d (shiftP d (1, d + 1) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_i1_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) 1 0)) :
    valPlus d (shiftP d (1, d + 1) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_i1_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) 1 1)) :
    valPlus d (shiftP d (1, d + 1) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_i2_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) 2 (-1))) :
    valPlus d (shiftP d (1, d + 1) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_i2_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) 2 0)) :
    valPlus d (shiftP d (1, d + 1) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner_i2_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (1, d + 1) 2 1)) :
    valPlus d (shiftP d (1, d + 1) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_corner (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (r : ℤ) (hr : RankOfP d (1, d + 1) r) :
    r < 4 * d := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_corner_im2_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_im2_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_im2_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_im1_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_im1_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_im1_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_i0_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_i0_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_i0_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_i1_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_i1_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_i1_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_i2_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_i2_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_corner_i2_j1 d ⟨hd, hdodd⟩ hrep


set_option maxHeartbeats 400000 in
theorem gateP_anti_im2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) (-2) (-1))) :
    valPlus d (shiftP d (x, y - 1) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_im2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) (-2) 0)) :
    valPlus d (shiftP d (x, y - 1) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_im2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) (-2) 1)) :
    valPlus d (shiftP d (x, y - 1) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_im1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) (-1) (-1))) :
    valPlus d (shiftP d (x, y - 1) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_im1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) (-1) 0)) :
    valPlus d (shiftP d (x, y - 1) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_im1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) (-1) 1)) :
    valPlus d (shiftP d (x, y - 1) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_i0_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) 0 (-1))) :
    valPlus d (shiftP d (x, y - 1) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_i0_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) 0 0)) :
    valPlus d (shiftP d (x, y - 1) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_i0_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) 0 1)) :
    valPlus d (shiftP d (x, y - 1) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_i1_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) 1 (-1))) :
    valPlus d (shiftP d (x, y - 1) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_i1_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) 1 0)) :
    valPlus d (shiftP d (x, y - 1) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_i1_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) 1 1)) :
    valPlus d (shiftP d (x, y - 1) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_i2_jm1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) 2 (-1))) :
    valPlus d (shiftP d (x, y - 1) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_i2_j0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) 2 0)) :
    valPlus d (shiftP d (x, y - 1) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti_i2_j1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d ∧ y ≤ d) (hrep : IsRepP d (shiftP d (x, y - 1) 2 1)) :
    valPlus d (shiftP d (x, y - 1) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 4 * d + 1 - 2 * x := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_anti (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hs : x + y = d + 2) (hx2 : 2 ≤ x) (hxd : x ≤ d) (hyd : y ≤ d) (r : ℤ) (hr : RankOfP d (x, y - 1) r) :
    r < 4 * d + 1 - 2 * x := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_anti_im2_jm1 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_im2_j0 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_im2_j1 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_im1_jm1 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_im1_j0 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_im1_j1 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_i0_jm1 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_i0_j0 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_i0_j1 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_i1_jm1 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_i1_j0 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_i1_j1 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_i2_jm1 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_i2_j0 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep
  · exact gateP_anti_i2_j1 d x y ⟨hd, hdodd, hs, hx2, hxd, hyd⟩ hrep


set_option maxHeartbeats 400000 in
theorem gateP_fifth_im2_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) (-2) (-1))) :
    valPlus d (shiftP d (d + 1, 1) (-2) (-1)) - (-2) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_im2_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) (-2) 0)) :
    valPlus d (shiftP d (d + 1, 1) (-2) 0) - (-2) * (2 * d) - 0 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_im2_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) (-2) 1)) :
    valPlus d (shiftP d (d + 1, 1) (-2) 1) - (-2) * (2 * d) - 1 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_im1_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) (-1) (-1))) :
    valPlus d (shiftP d (d + 1, 1) (-1) (-1)) - (-1) * (2 * d) - (-1) * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_im1_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) (-1) 0)) :
    valPlus d (shiftP d (d + 1, 1) (-1) 0) - (-1) * (2 * d) - 0 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_im1_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) (-1) 1)) :
    valPlus d (shiftP d (d + 1, 1) (-1) 1) - (-1) * (2 * d) - 1 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_i0_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) 0 (-1))) :
    valPlus d (shiftP d (d + 1, 1) 0 (-1)) - 0 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_i0_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) 0 0)) :
    valPlus d (shiftP d (d + 1, 1) 0 0) - 0 * (2 * d) - 0 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_i0_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) 0 1)) :
    valPlus d (shiftP d (d + 1, 1) 0 1) - 0 * (2 * d) - 1 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_i1_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) 1 (-1))) :
    valPlus d (shiftP d (d + 1, 1) 1 (-1)) - 1 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_i1_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) 1 0)) :
    valPlus d (shiftP d (d + 1, 1) 1 0) - 1 * (2 * d) - 0 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_i1_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) 1 1)) :
    valPlus d (shiftP d (d + 1, 1) 1 1) - 1 * (2 * d) - 1 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_i2_jm1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) 2 (-1))) :
    valPlus d (shiftP d (d + 1, 1) 2 (-1)) - 2 * (2 * d) - (-1) * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_i2_j0 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) 2 0)) :
    valPlus d (shiftP d (d + 1, 1) 2 0) - 2 * (2 * d) - 0 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth_i2_j1 (d : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1) (hrep : IsRepP d (shiftP d (d + 1, 1) 2 1)) :
    valPlus d (shiftP d (d + 1, 1) 2 1) - 2 * (2 * d) - 1 * (2 * (d + 1)) < 2 * d := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valPlus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega


set_option maxHeartbeats 400000 in
theorem gateP_fifth (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (r : ℤ) (hr : RankOfP d (d + 1, 1) r) :
    r < 2 * d := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gateP_fifth_im2_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_im2_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_im2_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_im1_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_im1_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_im1_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_i0_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_i0_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_i0_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_i1_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_i1_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_i1_j1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_i2_jm1 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_i2_j0 d ⟨hd, hdodd⟩ hrep
  · exact gateP_fifth_i2_j1 d ⟨hd, hdodd⟩ hrep


end FLatticePaper.PureRank
