import FLatticePaper.Plane.Induction.EPolicyFields
import FLatticePaper.Construction.PureRankPlusWhite

/-!
# The Retained side of the reflection of the signed policy (task 118, W1 base; bridge (1), part one)

For the reflected point `Rc - p`, `Rc = (2, d+1)`, this file proves the classification of the white aliases
(`hasWhite (Rc - p) ↔ WhiteN p` at native `p`, one direction for each case) and the witnesses of the retained edges:

* `white_retained_plus` / `white_retained_minus`: at a native white `p`, the input selected by the sign-`η` rule
  (`selDisp`) is a retained edge (`Retained`, `RetainedP`) at the reflected point, for `η = +1`, `η = -1`;
* `retained_black` / `retainedP_black`: at a native black `p`, both parity-correct displacements are retained at `Rc - p`.

The corner classification uses the reduced correction Laplacian `lapV_even_native`; all cases are finite alias
enumerations closed by `interval_cases` and `omega`.
-/

namespace FLatticePaper.ReflectWitness

open FLatticePaper.PureRank FLatticePaper.EPolicy


/-- Free aliases of the reflected point lie on the white side of the reciprocal policy. -/
theorem free_alias_whiteN (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (i j : ℤ)
    (hij : IsAlias i j) (hf : IsFreeP d (shiftP d (2 - x, d + 1 - y) i j)) : WhiteN d (x, y) := by
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hij
  unfold NativeP at hn
  unfold IsFreeP IsHc IsVc shiftP at hf
  unfold WhiteN FLatticePaper.EvenSite
  simp only [Prod.mk.injEq] at hn hf ⊢
  interval_cases i <;> interval_cases j <;> omega

/-- On an even point whose horizontal neighbours are native, the correction Laplacian is `−1` at `x = 1` and `0` otherwise. -/
theorem lapV_even_native (d X Y : ℤ) (_hd : 3 ≤ d) (hdodd : d % 2 = 1) (hev : (X + Y) % 2 = 0)
    (_h0 : NativeP d (X, Y)) (h1 : NativeP d (X - 1, Y)) (h2 : NativeP d (X + 1, Y)) :
    lapV d X Y = if X = 1 then -1 else 0 := by
  have hc1 : ¬ ((X - 1 = 0 ∧ Y = 0) ∨ (X - 1 = 2 ∧ Y = d + 1)) := by
    omega
  have hc2 : ¬ ((X + 1 = 0 ∧ Y = 0) ∨ (X + 1 = 2 ∧ Y = d + 1)) := by
    omega
  have hc0 : ¬ ((X = 0 ∧ Y = 0) ∨ (X = 2 ∧ Y = d + 1)) := by
    unfold NativeP at h1 h2
    simp only [Prod.mk.injEq] at h1 h2
    omega
  unfold lapV corrV
  rw [if_pos hev, if_neg hc1, if_neg hc2, if_neg hc0]
  unfold NativeP at h1 h2
  simp only [Prod.mk.injEq] at h1 h2
  split_ifs <;> omega

/-- A corner-white alias of a reflected native point forces the source to be white. -/
theorem cg_alias_whiteN (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (i j : ℤ)
    (hij : IsAlias i j) (hc : cgAt d (2 - x) (d + 1 - y) (shiftP d (2 - x, d + 1 - y) i j)) : WhiteN d (x, y) := by
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hij
  obtain ⟨hstar, hlap, hev, hside, -⟩ := hc
  unfold starV at hstar
  obtain ⟨hN0, hcase⟩ := hstar
  rcases hcase with ⟨-, hN1, hN2⟩ | ⟨hodd, -, -⟩
  · rw [lapV_even_native d _ _ hd hdodd hev hN0 hN1 hN2] at hlap
    have hq1 : (shiftP d (2 - x, d + 1 - y) i j).1 ≠ 1 := by
      intro h
      rw [if_pos h] at hlap
      norm_num at hlap
    unfold WhiteN FLatticePaper.EvenSite
    unfold NativeP at hn hN0 hN1 hN2
    unfold shiftP at hq1 hev hside hN0 hN1 hN2
    dsimp only
    simp only [Prod.mk.injEq] at hn hq1 hev hside hN0 hN1 hN2
    interval_cases i <;> interval_cases j <;> omega
  · exact absurd hodd (by omega)

theorem prescribedFree_even (d : ℤ) (s : Pt) (h : (s.1 + s.2) % 2 = 0) : prescribedFree d s = (-1, 0) := by
  unfold prescribedFree
  rw [if_pos h]

theorem prescribedFree_odd_H_ne (d : ℤ) (s : Pt) (h : (s.1 + s.2) % 2 ≠ 0) (hH : IsHc d s) (hne : s.1 ≠ d) :
    prescribedFree d s = (0, -1) := by
  unfold prescribedFree
  rw [if_neg h, if_pos hH, if_neg hne]

theorem prescribedFree_odd_H_eq (d : ℤ) (s : Pt) (h : (s.1 + s.2) % 2 ≠ 0) (hH : IsHc d s) (heq : s.1 = d) :
    prescribedFree d s = (0, 1) := by
  unfold prescribedFree
  rw [if_neg h, if_pos hH, if_pos heq]

theorem prescribedFree_odd_V (d : ℤ) (s : Pt) (h : (s.1 + s.2) % 2 ≠ 0) (hH : ¬ IsHc d s) :
    prescribedFree d s = (0, 1) := by
  unfold prescribedFree
  rw [if_neg h, if_neg hH]

/-- Free witness at the source itself (alias `(0,0)`). -/
theorem freeHit_self (d X Y dx dy : ℤ) (hf : IsFreeP d (X, Y)) (hp : prescribedFree d (X, Y) = (dx, dy)) :
    freeHit d X Y dx dy :=
  ⟨0, 0, by norm_num [IsAlias], by rw [shiftP_zero_zero]; exact hf, by rw [shiftP_zero_zero]; exact hp⟩

theorem noFree_interior_even (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hN : NativeP d (x, y))
    (hev : (x + y) % 2 = 0) (_hx1 : x ≠ 1)
    (hnH : ¬ (y = 0 ∧ 2 ≤ x)) (hn0 : ¬ (x = 0 ∧ y = 0)) (hnd : ¬ (x = d ∧ y = 1))
    (hnT : ¬ (y = d + 1 ∧ 3 - d ≤ x ∧ x ≤ 0)) (hnS : ¬ ((x = 2 - d ∧ y = d) ∨ (x = 2 ∧ y = d + 1))) :
    noFree d (2 - x) (d + 1 - y) := by
  intro i j hij hf
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hij
  unfold NativeP at hN
  unfold IsFreeP IsHc IsVc shiftP at hf
  simp only [Prod.mk.injEq] at hN hf hnH hn0 hnd hnT hnS
  interval_cases i <;> interval_cases j <;> omega
theorem nativeP_refl (d x y : ℤ) : NativeP d (2 - x, d + 1 - y) ↔ NativeP d (x, y) := by
  unfold NativeP
  simp only [Prod.mk.injEq]
  constructor <;> intro h <;> omega

theorem cg_refl_self (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hN : NativeP d (x, y))
    (hev : (x + y) % 2 = 0) (_hx1 : x ≠ 1) (hnb1 : NativeP d (x - 1, y)) (hnb2 : NativeP d (x + 1, y))
    (hnf : noFree d (2 - x) (d + 1 - y)) : cgAt d (2 - x) (d + 1 - y) (shiftP d (2 - x, d + 1 - y) 0 0) := by
  rw [shiftP_zero_zero]
  have hs0 : NativeP d (2 - x, d + 1 - y) := (nativeP_refl d x y).mpr hN
  have hs1 : NativeP d (2 - x - 1, d + 1 - y) := by
    have := (nativeP_refl d (x + 1) y).mpr hnb2
    convert this using 2
    ring
  have hs2 : NativeP d (2 - x + 1, d + 1 - y) := by
    have := (nativeP_refl d (x - 1) y).mpr hnb1
    convert this using 2
    ring
  refine ⟨?_, ?_, ?_, ?_, hnf⟩
  · unfold starV
    refine ⟨hs0, Or.inl ⟨by omega, hs1, hs2⟩⟩
  · rw [lapV_even_native d (2 - x) (d + 1 - y) hd hdodd (by omega) hs0 hs1 hs2]
    rw [if_neg (by omega)]
  · show ((2 - x) + (d + 1 - y)) % 2 = 0
    omega
  · show (2 - x ≤ 0 ∨ 2 ≤ 2 - x)
    omega

macro "free_tac" : tactic => `(tactic| (unfold IsFreeP IsHc IsVc; (try unfold shiftP); dsimp only; simp only [Prod.mk.injEq]; omega))
macro "pres_tac" : tactic => `(tactic| (unfold prescribedFree IsHc; (try unfold shiftP); dsimp only; split_ifs <;> first | (simp only [Prod.mk.injEq]; norm_num; done) | (exfalso; omega) | skip))

theorem nb_native_even (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hN : NativeP d (x, y))
    (hev : (x + y) % 2 = 0) (_hx1 : x ≠ 1) (h1 : ¬ ((x, y) = (2 - d, d))) (h2 : ¬ ((x, y) = (2, d + 1)))
    (h3 : ¬ ((x, y) = (d, 1))) (h4 : ¬ ((x, y) = (0, 0))) :
    NativeP d (x - 1, y) ∧ NativeP d (x + 1, y) := by
  have h1' : ¬ (x = 2 - d ∧ y = d) := fun h => h1 (Prod.ext h.1 h.2)
  have h2' : ¬ (x = 2 ∧ y = d + 1) := fun h => h2 (Prod.ext h.1 h.2)
  have h3' : ¬ (x = d ∧ y = 1) := fun h => h3 (Prod.ext h.1 h.2)
  have h4' : ¬ (x = 0 ∧ y = 0) := fun h => h4 (Prod.ext h.1 h.2)
  unfold NativeP at hN ⊢
  simp only [Prod.mk.injEq] at hN ⊢
  clear h1 h2 h3 h4
  omega

set_option maxHeartbeats 400000 in
theorem white_retained_one_even (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hN : NativeP d (x, y))
    (hev : (x + y) % 2 = 0) (hx1 : x ≠ 1) :
    Retained d (2 - x) (d + 1 - y) (-(selDisp d 1 (x, y)).1) (-(selDisp d 1 (x, y)).2) := by
  have hN' := hN
  have hNb := hN
  unfold NativeP at hNb
  simp only [Prod.mk.injEq] at hNb
  unfold selDisp
  rw [if_pos (show FLatticePaper.EvenSite (x, y) from hev)]
  have hpar : ((2 - x) + (d + 1 - y)) % 2 = 0 := by omega
  split_ifs with hA hB hC
  · refine ⟨Or.inl ⟨hpar, rfl⟩, Or.inr (Or.inl ?_)⟩
    simp only [Prod.mk.injEq] at hA
    rcases hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨-1, 0, by norm_num [IsAlias], by free_tac, by pres_tac⟩
    · exact freeHit_self d _ _ _ _ (by free_tac) (by pres_tac)
  · refine ⟨Or.inl ⟨hpar, rfl⟩, Or.inr (Or.inl ?_)⟩
    simp only [Prod.mk.injEq] at hB
    rcases hB with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact ⟨0, -1, by norm_num [IsAlias], by free_tac, by pres_tac⟩
    · exact ⟨-1, 0, by norm_num [IsAlias], by free_tac, by pres_tac⟩
    · exact freeHit_self d _ _ _ _ (by free_tac) (by pres_tac)
    · exact freeHit_self d _ _ _ _ (by free_tac) (by pres_tac)
  · have hC' : x ≤ 0 := hC
    obtain ⟨hnb1, hnb2⟩ := nb_native_even d x y hd hdodd hN' hev hx1 (fun h => hA (Or.inl h)) (fun h => hA (Or.inr h))
      (fun h => hB (Or.inr (Or.inr (Or.inl h)))) (fun h => hB (Or.inr (Or.inl h)))
    have hnf := noFree_interior_even d x y hd hdodd hN' hev hx1
      (fun h => hB (Or.inl h)) (fun h => hB (Or.inr (Or.inl (Prod.ext h.1 h.2))))
      (fun h => hB (Or.inr (Or.inr (Or.inl (Prod.ext h.1 h.2)))))
      (fun h => hB (Or.inr (Or.inr (Or.inr h))))
      (fun h => hA (Or.elim h (fun h' => Or.inl (Prod.ext h'.1 h'.2)) (fun h' => Or.inr (Prod.ext h'.1 h'.2))))
    refine ⟨Or.inl ⟨hpar, rfl⟩, Or.inr (Or.inr ?_)⟩
    refine ⟨0, 0, by norm_num [IsAlias], cg_refl_self d x y hd hdodd hN' hev hx1 hnb1 hnb2 hnf, ?_⟩
    rw [shiftP_zero_zero]
    exact Or.inr ⟨by dsimp only; linarith, rfl, rfl⟩
  · have hC' : 2 ≤ x := by
      have : ¬ x ≤ 0 := hC
      omega
    obtain ⟨hnb1, hnb2⟩ := nb_native_even d x y hd hdodd hN' hev hx1 (fun h => hA (Or.inl h)) (fun h => hA (Or.inr h))
      (fun h => hB (Or.inr (Or.inr (Or.inl h)))) (fun h => hB (Or.inr (Or.inl h)))
    have hnf := noFree_interior_even d x y hd hdodd hN' hev hx1
      (fun h => hB (Or.inl h)) (fun h => hB (Or.inr (Or.inl (Prod.ext h.1 h.2))))
      (fun h => hB (Or.inr (Or.inr (Or.inl (Prod.ext h.1 h.2)))))
      (fun h => hB (Or.inr (Or.inr (Or.inr h))))
      (fun h => hA (Or.elim h (fun h' => Or.inl (Prod.ext h'.1 h'.2)) (fun h' => Or.inr (Prod.ext h'.1 h'.2))))
    refine ⟨Or.inl ⟨hpar, rfl⟩, Or.inr (Or.inr ?_)⟩
    refine ⟨0, 0, by norm_num [IsAlias], cg_refl_self d x y hd hdodd hN' hev hx1 hnb1 hnb2 hnf, ?_⟩
    rw [shiftP_zero_zero]
    exact Or.inl ⟨by dsimp only; linarith, rfl, rfl⟩

set_option maxHeartbeats 400000 in
theorem white_retained_one_odd (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hN : NativeP d (x, y))
    (hod : (x + y) % 2 ≠ 0) (hW : WhiteN d (x, y)) :
    Retained d (2 - x) (d + 1 - y) (-(selDisp d 1 (x, y)).1) (-(selDisp d 1 (x, y)).2) := by
  have hNb := hN
  unfold NativeP at hNb
  simp only [Prod.mk.injEq] at hNb
  unfold selDisp
  rw [if_neg (show ¬ FLatticePaper.EvenSite (x, y) from hod)]
  have hpar : ((2 - x) + (d + 1 - y)) % 2 ≠ 0 := by omega
  split_ifs with hR
  · refine ⟨Or.inr ⟨hpar, rfl⟩, Or.inr (Or.inl ?_)⟩
    dsimp only at hR
    rcases hR with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · exact ⟨0, -1, by norm_num [IsAlias], by free_tac, by pres_tac⟩
    · exact ⟨-1, 0, by norm_num [IsAlias], by free_tac, by pres_tac⟩
    · exact freeHit_self d _ _ _ _ (by free_tac) (by pres_tac)
    · exact freeHit_self d _ _ _ _ (by free_tac) (by pres_tac)
  · refine ⟨Or.inr ⟨hpar, rfl⟩, Or.inr (Or.inl ?_)⟩
    dsimp only at hR
    simp only [not_or] at hR
    unfold WhiteN at hW
    have hy : y = 0 ∨ y = d + 1 := by
      rcases hW with ⟨hev', -⟩ | ⟨-, hW'⟩
      · exact absurd hev' hod
      · omega
    rcases hy with hy0 | hy1
    · exact ⟨0, -1, by norm_num [IsAlias], by free_tac, by pres_tac⟩
    · exact freeHit_self d _ _ _ _ (by free_tac) (by pres_tac)

theorem freeHitP_self (d X Y dx dy : ℤ) (hf : IsFreeP d (X, Y)) (hp : prescribedPlus d (X, Y) = (dx, dy)) :
    freeHitP d X Y dx dy :=
  ⟨0, 0, by norm_num [IsAlias], by rw [shiftP_zero_zero]; exact hf, by rw [shiftP_zero_zero]; exact hp⟩

macro "presP_tac" : tactic => `(tactic| (unfold prescribedPlus IsHc; (try (unfold shiftP)); dsimp only; split_ifs <;> (first | (simp only [Prod.mk.injEq] at *; norm_num; done) | (simp only [Prod.mk.injEq] at *; exfalso; omega) | skip)))

set_option maxHeartbeats 400000 in
theorem white_retainedP_odd (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hN : NativeP d (x, y))
    (hod : (x + y) % 2 ≠ 0) (hW : WhiteN d (x, y)) :
    RetainedP d (2 - x) (d + 1 - y) (-(selDisp d (-1) (x, y)).1) (-(selDisp d (-1) (x, y)).2) := by
  have hNb := hN
  unfold NativeP at hNb
  simp only [Prod.mk.injEq] at hNb
  unfold selDisp
  rw [if_neg (show ¬ FLatticePaper.EvenSite (x, y) from hod)]
  have hpar : ((2 - x) + (d + 1 - y)) % 2 ≠ 0 := by omega
  split_ifs with hR
  · refine ⟨Or.inr ⟨hpar, rfl⟩, Or.inr (Or.inl ?_)⟩
    dsimp only at hR
    rcases hR with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · exact ⟨0, -1, by norm_num [IsAlias], by free_tac, by presP_tac⟩
    · exact ⟨-1, 0, by norm_num [IsAlias], by free_tac, by presP_tac⟩
    · exact freeHitP_self d _ _ _ _ (by free_tac) (by presP_tac)
    · exact freeHitP_self d _ _ _ _ (by free_tac) (by presP_tac)
  · refine ⟨Or.inr ⟨hpar, rfl⟩, Or.inr (Or.inl ?_)⟩
    dsimp only at hR
    simp only [not_or] at hR
    unfold WhiteN at hW
    have hy : y = 0 ∨ y = d + 1 := by
      rcases hW with ⟨hev', -⟩ | ⟨-, hW'⟩
      · exact absurd hev' hod
      · omega
    rcases hy with hy0 | hy1
    · exact ⟨0, -1, by norm_num [IsAlias], by free_tac, by presP_tac⟩
    · exact freeHitP_self d _ _ _ _ (by free_tac) (by presP_tac)

set_option maxHeartbeats 400000 in
theorem white_retainedP_even (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hN : NativeP d (x, y))
    (hev : (x + y) % 2 = 0) (hx1 : x ≠ 1) :
    RetainedP d (2 - x) (d + 1 - y) (-(selDisp d (-1) (x, y)).1) (-(selDisp d (-1) (x, y)).2) := by
  have hN' := hN
  have hNb := hN
  unfold NativeP at hNb
  simp only [Prod.mk.injEq] at hNb
  unfold selDisp
  rw [if_pos (show FLatticePaper.EvenSite (x, y) from hev)]
  have hpar : ((2 - x) + (d + 1 - y)) % 2 = 0 := by omega
  split_ifs with hA hB hC
  · refine ⟨Or.inl ⟨hpar, rfl⟩, Or.inr (Or.inl ?_)⟩
    simp only [Prod.mk.injEq] at hA
    rcases hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨-1, 0, by norm_num [IsAlias], by free_tac, by presP_tac⟩
    · exact freeHitP_self d _ _ _ _ (by free_tac) (by presP_tac)
  · refine ⟨Or.inl ⟨hpar, rfl⟩, Or.inr (Or.inl ?_)⟩
    simp only [Prod.mk.injEq] at hB
    rcases hB with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact ⟨0, -1, by norm_num [IsAlias], by free_tac, by presP_tac⟩
    · exact ⟨-1, 0, by norm_num [IsAlias], by free_tac, by presP_tac⟩
    · exact freeHitP_self d _ _ _ _ (by free_tac) (by presP_tac)
    · exact freeHitP_self d _ _ _ _ (by free_tac) (by presP_tac)
  · have hC' : x ≤ 0 := hC
    obtain ⟨hnb1, hnb2⟩ := nb_native_even d x y hd hdodd hN' hev hx1 (fun h => hA (Or.inl h)) (fun h => hA (Or.inr h))
      (fun h => hB (Or.inr (Or.inr (Or.inl h)))) (fun h => hB (Or.inr (Or.inl h)))
    have hnf := noFree_interior_even d x y hd hdodd hN' hev hx1
      (fun h => hB (Or.inl h)) (fun h => hB (Or.inr (Or.inl (Prod.ext h.1 h.2))))
      (fun h => hB (Or.inr (Or.inr (Or.inl (Prod.ext h.1 h.2)))))
      (fun h => hB (Or.inr (Or.inr (Or.inr h))))
      (fun h => hA (Or.elim h (fun h' => Or.inl (Prod.ext h'.1 h'.2)) (fun h' => Or.inr (Prod.ext h'.1 h'.2))))
    refine ⟨Or.inl ⟨hpar, rfl⟩, Or.inr (Or.inr ?_)⟩
    refine ⟨0, 0, by norm_num [IsAlias], cg_refl_self d x y hd hdodd hN' hev hx1 hnb1 hnb2 hnf, ?_⟩
    rw [shiftP_zero_zero]
    exact Or.inr ⟨by dsimp only; linarith, rfl, rfl⟩
  · have hC' : 2 ≤ x := by
      have : ¬ x ≤ 0 := hC
      omega
    obtain ⟨hnb1, hnb2⟩ := nb_native_even d x y hd hdodd hN' hev hx1 (fun h => hA (Or.inl h)) (fun h => hA (Or.inr h))
      (fun h => hB (Or.inr (Or.inr (Or.inl h)))) (fun h => hB (Or.inr (Or.inl h)))
    have hnf := noFree_interior_even d x y hd hdodd hN' hev hx1
      (fun h => hB (Or.inl h)) (fun h => hB (Or.inr (Or.inl (Prod.ext h.1 h.2))))
      (fun h => hB (Or.inr (Or.inr (Or.inl (Prod.ext h.1 h.2)))))
      (fun h => hB (Or.inr (Or.inr (Or.inr h))))
      (fun h => hA (Or.elim h (fun h' => Or.inl (Prod.ext h'.1 h'.2)) (fun h' => Or.inr (Prod.ext h'.1 h'.2))))
    refine ⟨Or.inl ⟨hpar, rfl⟩, Or.inr (Or.inr ?_)⟩
    refine ⟨0, 0, by norm_num [IsAlias], cg_refl_self d x y hd hdodd hN' hev hx1 hnb1 hnb2 hnf, ?_⟩
    rw [shiftP_zero_zero]
    exact Or.inl ⟨by dsimp only; linarith, rfl, rfl⟩


theorem hasWhite_refl_whiteN (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hN : NativeP d (x, y))
    (h : hasWhite d (2 - x) (d + 1 - y)) : WhiteN d (x, y) := by
  obtain ⟨i, j, hij, h'⟩ := h
  rcases h' with hf | hc
  · exact free_alias_whiteN d x y hd hdodd hN i j hij hf
  · exact cg_alias_whiteN d x y hd hdodd hN i j hij hc

theorem retained_black (d x y dx dy : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hN : NativeP d (x, y))
    (hB : ¬ WhiteN d (x, y))
    (hpar : ((x + y) % 2 = 0 ∧ dy = 0) ∨ ((x + y) % 2 ≠ 0 ∧ dx = 0)) :
    Retained d (2 - x) (d + 1 - y) dx dy := by
  refine ⟨?_, Or.inl ?_⟩
  · rcases hpar with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by omega, h2⟩
    · exact Or.inr ⟨by omega, h2⟩
  · intro h
    exact hB (hasWhite_refl_whiteN d x y hd hdodd hN h)

theorem retainedP_black (d x y dx dy : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hN : NativeP d (x, y))
    (hB : ¬ WhiteN d (x, y))
    (hpar : ((x + y) % 2 = 0 ∧ dy = 0) ∨ ((x + y) % 2 ≠ 0 ∧ dx = 0)) :
    RetainedP d (2 - x) (d + 1 - y) dx dy := by
  refine ⟨?_, Or.inl ?_⟩
  · rcases hpar with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by omega, h2⟩
    · exact Or.inr ⟨by omega, h2⟩
  · intro h
    exact hB (hasWhite_refl_whiteN d x y hd hdodd hN h)

theorem white_retained_plus (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hN : NativeP d (x, y))
    (hW : WhiteN d (x, y)) :
    Retained d (2 - x) (d + 1 - y) (-(selDisp d 1 (x, y)).1) (-(selDisp d 1 (x, y)).2) := by
  by_cases hev : (x + y) % 2 = 0
  · have hx1 : x ≠ 1 := by
      unfold WhiteN at hW
      rcases hW with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd hev h
    exact white_retained_one_even d x y hd hdodd hN hev hx1
  · exact white_retained_one_odd d x y hd hdodd hN hev hW

theorem white_retained_minus (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hN : NativeP d (x, y))
    (hW : WhiteN d (x, y)) :
    RetainedP d (2 - x) (d + 1 - y) (-(selDisp d (-1) (x, y)).1) (-(selDisp d (-1) (x, y)).2) := by
  by_cases hev : (x + y) % 2 = 0
  · have hx1 : x ≠ 1 := by
      unfold WhiteN at hW
      rcases hW with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd hev h
    exact white_retainedP_even d x y hd hdodd hN hev hx1
  · exact white_retainedP_odd d x y hd hdodd hN hev hW

end FLatticePaper.ReflectWitness
