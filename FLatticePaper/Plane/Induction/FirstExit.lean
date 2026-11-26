import FLatticePaper.Plane.Induction.BoundarySpectrum
import FLatticePaper.Plane.Induction.W4White
import FLatticePaper.Plane.Induction.FreeCutPred

/-! # The first exit of the open rectangle is free modulo the span

An input `u` of a strict (open-rectangle) site `z`, with `u` not strict, is closed and has a 4-neighbour outside the closed
rectangle; the boundary spectrum then places `u` on one of the four free arcs, up to the span vectors `K = (d, n)` and
`V = (n − d, n + d)`. -/

namespace FLatticePaper.FirstExit

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1

/-- A neighbour of `u` is one of its four unit neighbours, when `u` is an input of `z`. -/
theorem edge_nbr (u z : Site) (h : u = incomingNeg z ∨ u = incomingPos z) :
    z = (u.1 + 1, u.2) ∨ z = (u.1 - 1, u.2) ∨ z = (u.1, u.2 + 1) ∨ z = (u.1, u.2 - 1) := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨z1, z2⟩ := z
  unfold incomingNeg incomingPos at h
  by_cases he : EvenSite (z1, z2)
  · simp only [he, if_true, Prod.mk.injEq] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; simp only [Prod.mk.injEq]; omega
    · right; left; simp only [Prod.mk.injEq]; omega
  · simp only [he, if_false, Prod.mk.injEq] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; right; left; simp only [Prod.mk.injEq]; omega
    · right; right; right; simp only [Prod.mk.injEq]; omega

/-- The closed rectangle at an even site, in the grades of `BoundarySpectrum`. -/
theorem closedRect_even_iff (n d : Int) (z : Site) (h : EvenSite z) :
    closedRect n d z ↔ BoundarySpectrum.EvenRect n d (w1T n d) (w1t n d z) (w1s n d z) := by
  unfold closedRect BoundarySpectrum.EvenRect
  rw [if_pos h]

/-- The closed rectangle at an odd site. -/
theorem closedRect_odd_iff (n d : Int) (z : Site) (h : ¬ EvenSite z) :
    closedRect n d z ↔ BoundarySpectrum.OddRect n d (w1T n d) (w1t n d z) (w1s n d z) := by
  unfold closedRect BoundarySpectrum.OddRect
  rw [if_neg h]

/-- The grade `s` of a site is even when `d + n` and `d − n` are even. -/
theorem sGrade_even_of (frame : ChildFrame) (z : Site) : frame.sGrade z % 2 = 0 := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hnodd : frame.child.num % 2 = 1 := frame.child_num_odd
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have h1 : (frame.child.den + frame.child.num) % 2 = 0 := by omega
  have h2 : (frame.child.den - frame.child.num) % 2 = 0 := by omega
  unfold ChildFrame.sGrade
  rw [Int.add_emod, Int.mul_emod, Int.mul_emod (frame.child.den - frame.child.num), h1, h2]
  simp

/-- **The exit lemma at an even site.** If the even site `z` is closed and not strict, and one of its four neighbours is strict,
then one of its four neighbours lies outside the closed rectangle. -/
theorem exit_hex_even (frame : ChildFrame) {x y : Int} (he : EvenSite (x, y))
    (hnot : ¬ StrictInterior frame.child.num frame.child.den (x, y))
    (hs : StrictInterior frame.child.num frame.child.den (x - 1, y) ∨
      StrictInterior frame.child.num frame.child.den (x + 1, y) ∨
      StrictInterior frame.child.num frame.child.den (x, y - 1) ∨
      StrictInterior frame.child.num frame.child.den (x, y + 1)) :
    ¬ closedRect frame.child.num frame.child.den (x - 1, y) ∨
      ¬ closedRect frame.child.num frame.child.den (x + 1, y) ∨
      ¬ closedRect frame.child.num frame.child.den (x, y - 1) ∨
      ¬ closedRect frame.child.num frame.child.den (x, y + 1) := by
  have he' : (x + y) % 2 = 0 := he
  have o1 : ¬ EvenSite (x - 1, y) := by unfold EvenSite; show ¬ ((x - 1 + y) % 2 = 0); omega
  have o2 : ¬ EvenSite (x + 1, y) := by unfold EvenSite; show ¬ ((x + 1 + y) % 2 = 0); omega
  have o3 : ¬ EvenSite (x, y - 1) := by unfold EvenSite; show ¬ ((x + (y - 1)) % 2 = 0); omega
  have o4 : ¬ EvenSite (x, y + 1) := by unfold EvenSite; show ¬ ((x + (y + 1)) % 2 = 0); omega
  by_contra hall
  simp only [not_or, not_not] at hall
  obtain ⟨h1, h2, h3, h4⟩ := hall
  rw [closedRect_odd_iff _ _ _ o1] at h1
  rw [closedRect_odd_iff _ _ _ o2] at h2
  rw [closedRect_odd_iff _ _ _ o3] at h3
  rw [closedRect_odd_iff _ _ _ o4] at h4
  unfold StrictInterior at hnot hs
  simp only [w1a, w1b, w1c, w1h, if_pos he, if_neg o1, if_neg o2, if_neg o3, if_neg o4] at hnot hs
  unfold BoundarySpectrum.OddRect at h1 h2 h3 h4
  simp only [FreeCutPred.w1t_predX, FreeCutPred.w1s_predX, FreeCutPred.w1t_succX, FreeCutPred.w1s_succX,
    FreeCutPred.w1t_predY, FreeCutPred.w1s_predY, FreeCutPred.w1t_succY, FreeCutPred.w1s_succY] at h1 h2 h3 h4 hs
  generalize w1t frame.child.num frame.child.den (x, y) = t at *
  generalize w1s frame.child.num frame.child.den (x, y) = s at *
  generalize w1T frame.child.num frame.child.den = T at *
  omega

/-- **The exit lemma at an odd site** (the neighbours are even). -/
theorem exit_hex_odd (frame : ChildFrame) {x y : Int} (ho : ¬ EvenSite (x, y))
    (hnot : ¬ StrictInterior frame.child.num frame.child.den (x, y))
    (hs : StrictInterior frame.child.num frame.child.den (x - 1, y) ∨
      StrictInterior frame.child.num frame.child.den (x + 1, y) ∨
      StrictInterior frame.child.num frame.child.den (x, y - 1) ∨
      StrictInterior frame.child.num frame.child.den (x, y + 1)) :
    ¬ closedRect frame.child.num frame.child.den (x - 1, y) ∨
      ¬ closedRect frame.child.num frame.child.den (x + 1, y) ∨
      ¬ closedRect frame.child.num frame.child.den (x, y - 1) ∨
      ¬ closedRect frame.child.num frame.child.den (x, y + 1) := by
  have ho' : ¬ ((x + y) % 2 = 0) := ho
  have e1 : EvenSite (x - 1, y) := by unfold EvenSite; show (x - 1 + y) % 2 = 0; omega
  have e2 : EvenSite (x + 1, y) := by unfold EvenSite; show (x + 1 + y) % 2 = 0; omega
  have e3 : EvenSite (x, y - 1) := by unfold EvenSite; show (x + (y - 1)) % 2 = 0; omega
  have e4 : EvenSite (x, y + 1) := by unfold EvenSite; show (x + (y + 1)) % 2 = 0; omega
  by_contra hall
  simp only [not_or, not_not] at hall
  obtain ⟨h1, h2, h3, h4⟩ := hall
  rw [closedRect_even_iff _ _ _ e1] at h1
  rw [closedRect_even_iff _ _ _ e2] at h2
  rw [closedRect_even_iff _ _ _ e3] at h3
  rw [closedRect_even_iff _ _ _ e4] at h4
  unfold StrictInterior at hnot hs
  simp only [w1a, w1b, w1c, w1h, if_neg ho, if_pos e1, if_pos e2, if_pos e3, if_pos e4] at hnot hs
  unfold BoundarySpectrum.EvenRect at h1 h2 h3 h4
  simp only [FreeCutPred.w1t_predX, FreeCutPred.w1s_predX, FreeCutPred.w1t_succX, FreeCutPred.w1s_succX,
    FreeCutPred.w1t_predY, FreeCutPred.w1s_predY, FreeCutPred.w1t_succY, FreeCutPred.w1s_succY] at h1 h2 h3 h4 hs
  generalize w1t frame.child.num frame.child.den (x, y) = t at *
  generalize w1s frame.child.num frame.child.den (x, y) = s at *
  generalize w1T frame.child.num frame.child.den = T at *
  omega

/-- The grade `t` of a site in the child frame. -/
theorem tGrade_eq_w1t (frame : ChildFrame) (z : Site) :
    frame.tGrade z = w1t frame.child.num frame.child.den z := rfl

/-- The grade `s` of a site in the child frame. -/
theorem sGrade_eq_w1s (frame : ChildFrame) (z : Site) :
    frame.sGrade z = w1s frame.child.num frame.child.den z := rfl

/-- The grade `s` of the south neighbour: `s(x, y − 1) = s − (d − n)`. -/
theorem w1s_predY' (n d x y : Int) : w1s n d (x, y - 1) = w1s n d (x, y) - (d - n) := by
  unfold w1s; ring

/-- The span shift by `-K`, `K = (d, n)`: the grade `t` is fixed and `s` drops by `T`. -/
theorem w1t_sub_K (n d x y : Int) : w1t n d (x - d, y - n) = w1t n d (x, y) := by
  unfold w1t; ring
theorem w1s_sub_K (n d x y : Int) : w1s n d (x - d, y - n) = w1s n d (x, y) - w1T n d := by
  unfold w1s w1T; ring

/-- The span shift by `-V`, `V = (n − d, n + d)`: the grade `t` rises by `T` and `s` is fixed. -/
theorem w1t_sub_V (n d x y : Int) : w1t n d (x - (n - d), y - (n + d)) = w1t n d (x, y) + w1T n d := by
  unfold w1t w1T; ring
theorem w1s_sub_V (n d x y : Int) : w1s n d (x - (n - d), y - (n + d)) = w1s n d (x, y) := by
  unfold w1s; ring

/-- **Free modulo the span**: a site `u` is `v + k K + l V` for a free H or free V site `v`. -/
def FreeMod (frame : ChildFrame) (u : Site) : Prop :=
  ∃ k l : Int,
    (u.1 - k * frame.child.den - l * (frame.child.num - frame.child.den),
        u.2 - k * frame.child.num - l * (frame.child.num + frame.child.den)) ∈ frame.freeH ∨
    (u.1 - k * frame.child.den - l * (frame.child.num - frame.child.den),
        u.2 - k * frame.child.num - l * (frame.child.num + frame.child.den)) ∈ frame.freeV

/-- **A closed even boundary site is free modulo the span.** -/
theorem free_of_even (frame : ChildFrame) {x y : Int} (he : EvenSite (x, y))
    (hcl : closedRect frame.child.num frame.child.den (x, y))
    (hex : ¬ closedRect frame.child.num frame.child.den (x - 1, y) ∨
      ¬ closedRect frame.child.num frame.child.den (x + 1, y) ∨
      ¬ closedRect frame.child.num frame.child.den (x, y - 1) ∨
      ¬ closedRect frame.child.num frame.child.den (x, y + 1)) : FreeMod frame (x, y) := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hnodd : frame.child.num % 2 = 1 := frame.child_num_odd
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hdodd : frame.child.den % 2 = 1 := by omega
  have he' : (x + y) % 2 = 0 := he
  have o1 : ¬ EvenSite (x - 1, y) := by unfold EvenSite; show ¬ ((x - 1 + y) % 2 = 0); omega
  have o2 : ¬ EvenSite (x + 1, y) := by unfold EvenSite; show ¬ ((x + 1 + y) % 2 = 0); omega
  have o3 : ¬ EvenSite (x, y - 1) := by unfold EvenSite; show ¬ ((x + (y - 1)) % 2 = 0); omega
  have o4 : ¬ EvenSite (x, y + 1) := by unfold EvenSite; show ¬ ((x + (y + 1)) % 2 = 0); omega
  have hT2 : frame.child.periodDenominator % 2 = 0 := FreeVCutExist.periodDenominator_even frame
  have hTe : w1T frame.child.num frame.child.den % 2 = 0 := by
    rw [← frame_periodDenominator_eq]; exact hT2
  have hT : 2 * (frame.child.den + frame.child.num) < w1T frame.child.num frame.child.den := by
    unfold w1T; nlinarith
  have ht : w1t frame.child.num frame.child.den (x, y) % 2 = 0 := by
    have h := FanInputs.tGrade_mod_two frame (x, y)
    rw [tGrade_eq_w1t] at h
    rw [h]; exact he'
  have hs : w1s frame.child.num frame.child.den (x, y) % 2 = 0 := by
    have h := sGrade_even_of frame (x, y)
    rw [sGrade_eq_w1s] at h
    exact h
  have hE : BoundarySpectrum.EvenRect frame.child.num frame.child.den (w1T frame.child.num frame.child.den)
      (w1t frame.child.num frame.child.den (x, y)) (w1s frame.child.num frame.child.den (x, y)) :=
    (closedRect_even_iff _ _ _ he).mp hcl
  have hex' : ¬ BoundarySpectrum.OddRect frame.child.num frame.child.den (w1T frame.child.num frame.child.den)
        (w1t frame.child.num frame.child.den (x, y) - frame.child.num)
        (w1s frame.child.num frame.child.den (x, y) - (frame.child.den + frame.child.num)) ∨
      ¬ BoundarySpectrum.OddRect frame.child.num frame.child.den (w1T frame.child.num frame.child.den)
        (w1t frame.child.num frame.child.den (x, y) + frame.child.num)
        (w1s frame.child.num frame.child.den (x, y) + (frame.child.den + frame.child.num)) ∨
      ¬ BoundarySpectrum.OddRect frame.child.num frame.child.den (w1T frame.child.num frame.child.den)
        (w1t frame.child.num frame.child.den (x, y) + frame.child.den)
        (w1s frame.child.num frame.child.den (x, y) - (frame.child.den - frame.child.num)) ∨
      ¬ BoundarySpectrum.OddRect frame.child.num frame.child.den (w1T frame.child.num frame.child.den)
        (w1t frame.child.num frame.child.den (x, y) - frame.child.den)
        (w1s frame.child.num frame.child.den (x, y) + (frame.child.den - frame.child.num)) := by
    rcases hex with h | h | h | h
    · left; rw [closedRect_odd_iff _ _ _ o1, FreeCutPred.w1t_predX, FreeCutPred.w1s_predX] at h; exact h
    · right; left; rw [closedRect_odd_iff _ _ _ o2, FreeCutPred.w1t_succX, FreeCutPred.w1s_succX] at h; exact h
    · right; right; left
      rw [closedRect_odd_iff _ _ _ o3, FreeCutPred.w1t_predY, w1s_predY'] at h; exact h
    · right; right; right; rw [closedRect_odd_iff _ _ _ o4, FreeCutPred.w1t_succY, FreeCutPred.w1s_succY] at h; exact h
  have hres := BoundarySpectrum.spectrum_even frame.child.num frame.child.den (w1T frame.child.num frame.child.den)
    (w1t frame.child.num frame.child.den (x, y)) (w1s frame.child.num frame.child.den (x, y))
    (by omega) (by omega) hnodd hdodd hT hTe ht hs hE hex'
  rcases hres with ⟨hH, hSo⟩ | ⟨hV, hSw⟩ | ⟨hE3, hV3, hS3⟩ | ⟨hE4, hH4, hS4⟩
  · -- the free H arc at the site itself
    have hH' : 2 ≤ w1t frame.child.num frame.child.den (x, y) ∧
        w1t frame.child.num frame.child.den (x, y) ≤ frame.child.den + frame.child.num - 2 := hH
    have hSouth : ¬ closedRect frame.child.num frame.child.den (x, y - 1) := by
      rw [closedRect_odd_iff _ _ _ o3, FreeCutPred.w1t_predY, w1s_predY']; exact hSo
    have hspec : frame.hSpectrum (frame.tGrade (x, y)) := by
      rw [tGrade_eq_w1t]; unfold ChildFrame.hSpectrum; left; exact ⟨by omega, hH'.1, hH'.2⟩
    have hmem : (x, y) ∈ frame.freeH := (FreeCutSucc.mem_freeH_iff frame (x, y)).mpr ⟨hcl, hSouth, hspec⟩
    exact ⟨0, 0, Or.inl (by simpa using hmem)⟩
  · -- the free V arc at the site itself
    have hWest : ¬ closedRect frame.child.num frame.child.den (x - 1, y) := by
      rw [closedRect_odd_iff _ _ _ o1, FreeCutPred.w1t_predX, FreeCutPred.w1s_predX]; exact hSw
    have hvspec : frame.vSpectrum (frame.sGrade (x, y)) := by
      rw [sGrade_eq_w1s]; unfold ChildFrame.vSpectrum; exact ⟨hs, hV⟩
    have hmem : (x, y) ∈ frame.freeV := (FreeCutSucc.mem_freeV_iff frame (x, y)).mpr ⟨hcl, hWest, hvspec⟩
    exact ⟨0, 0, Or.inr (by simpa using hmem)⟩
  · -- the free V arc at `z - K`, with `K = (d, n)` shifting `s` by `T`
    have hwE : EvenSite (x - frame.child.den, y - frame.child.num) := by
      unfold EvenSite; show (x - frame.child.den + (y - frame.child.num)) % 2 = 0; omega
    have hwO : ¬ EvenSite (x - frame.child.den - 1, y - frame.child.num) := by
      unfold EvenSite; show ¬ ((x - frame.child.den - 1 + (y - frame.child.num)) % 2 = 0); omega
    have hwCl : closedRect frame.child.num frame.child.den (x - frame.child.den, y - frame.child.num) :=
      (closedRect_even_iff _ _ _ hwE).mpr (by rw [w1t_sub_K, w1s_sub_K]; exact hE3)
    have hwWest : ¬ closedRect frame.child.num frame.child.den (x - frame.child.den - 1, y - frame.child.num) := by
      rw [closedRect_odd_iff _ _ _ hwO, FreeCutPred.w1t_predX, FreeCutPred.w1s_predX, w1t_sub_K, w1s_sub_K]
      exact hS3
    have hwSpec : frame.vSpectrum (frame.sGrade (x - frame.child.den, y - frame.child.num)) := by
      rw [sGrade_eq_w1s, w1s_sub_K]; unfold ChildFrame.vSpectrum; exact ⟨by omega, hV3⟩
    have hmem : (x - frame.child.den, y - frame.child.num) ∈ frame.freeV :=
      (FreeCutSucc.mem_freeV_iff frame _).mpr ⟨hwCl, hwWest, hwSpec⟩
    exact ⟨1, 0, Or.inr (by simpa using hmem)⟩
  · -- the free H arc at `z - V`, with `V = (n − d, n + d)` shifting `t` by `T`
    have hwE : EvenSite (x - (frame.child.num - frame.child.den), y - (frame.child.num + frame.child.den)) := by
      unfold EvenSite
      show (x - (frame.child.num - frame.child.den) + (y - (frame.child.num + frame.child.den))) % 2 = 0
      omega
    have hwSO : ¬ EvenSite (x - (frame.child.num - frame.child.den), y - (frame.child.num + frame.child.den) - 1) := by
      unfold EvenSite
      show ¬ ((x - (frame.child.num - frame.child.den) + (y - (frame.child.num + frame.child.den) - 1)) % 2 = 0)
      omega
    have hwCl : closedRect frame.child.num frame.child.den
        (x - (frame.child.num - frame.child.den), y - (frame.child.num + frame.child.den)) :=
      (closedRect_even_iff _ _ _ hwE).mpr (by rw [w1t_sub_V, w1s_sub_V]; exact hE4)
    have hwSouth : ¬ closedRect frame.child.num frame.child.den
        (x - (frame.child.num - frame.child.den), y - (frame.child.num + frame.child.den) - 1) := by
      rw [closedRect_odd_iff _ _ _ hwSO, FreeCutPred.w1t_predY, w1s_predY', w1t_sub_V, w1s_sub_V]
      exact hS4
    have hwSpec : frame.hSpectrum (frame.tGrade
        (x - (frame.child.num - frame.child.den), y - (frame.child.num + frame.child.den))) := by
      rw [tGrade_eq_w1t, w1t_sub_V]; unfold ChildFrame.hSpectrum; left
      exact ⟨by omega, by unfold BoundarySpectrum.HSpE at hH4; omega, by unfold BoundarySpectrum.HSpE at hH4; omega⟩
    have hmem : (x - (frame.child.num - frame.child.den), y - (frame.child.num + frame.child.den)) ∈ frame.freeH :=
      (FreeCutSucc.mem_freeH_iff frame _).mpr ⟨hwCl, hwSouth, hwSpec⟩
    exact ⟨0, 1, Or.inl (by simpa using hmem)⟩

/-- **A closed odd boundary site is free modulo the span.** -/
theorem free_of_odd (frame : ChildFrame) {x y : Int} (ho : ¬ EvenSite (x, y))
    (hcl : closedRect frame.child.num frame.child.den (x, y))
    (hex : ¬ closedRect frame.child.num frame.child.den (x - 1, y) ∨
      ¬ closedRect frame.child.num frame.child.den (x + 1, y) ∨
      ¬ closedRect frame.child.num frame.child.den (x, y - 1) ∨
      ¬ closedRect frame.child.num frame.child.den (x, y + 1)) : FreeMod frame (x, y) := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hnodd : frame.child.num % 2 = 1 := frame.child_num_odd
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hdodd : frame.child.den % 2 = 1 := by omega
  have ho' : ¬ ((x + y) % 2 = 0) := ho
  have e1 : EvenSite (x - 1, y) := by unfold EvenSite; show (x - 1 + y) % 2 = 0; omega
  have e2 : EvenSite (x + 1, y) := by unfold EvenSite; show (x + 1 + y) % 2 = 0; omega
  have e3 : EvenSite (x, y - 1) := by unfold EvenSite; show (x + (y - 1)) % 2 = 0; omega
  have e4 : EvenSite (x, y + 1) := by unfold EvenSite; show (x + (y + 1)) % 2 = 0; omega
  have hT2 : frame.child.periodDenominator % 2 = 0 := FreeVCutExist.periodDenominator_even frame
  have hTe : w1T frame.child.num frame.child.den % 2 = 0 := by
    rw [← frame_periodDenominator_eq]; exact hT2
  have hT : 2 * (frame.child.den + frame.child.num) < w1T frame.child.num frame.child.den := by
    unfold w1T; nlinarith
  have ht : w1t frame.child.num frame.child.den (x, y) % 2 = 1 := by
    have h := FanInputs.tGrade_mod_two frame (x, y)
    rw [tGrade_eq_w1t] at h
    rw [h]; omega
  have hs : w1s frame.child.num frame.child.den (x, y) % 2 = 0 := by
    have h := sGrade_even_of frame (x, y)
    rw [sGrade_eq_w1s] at h
    exact h
  have hO : BoundarySpectrum.OddRect frame.child.num frame.child.den (w1T frame.child.num frame.child.den)
      (w1t frame.child.num frame.child.den (x, y)) (w1s frame.child.num frame.child.den (x, y)) :=
    (closedRect_odd_iff _ _ _ ho).mp hcl
  have hex' : ¬ BoundarySpectrum.EvenRect frame.child.num frame.child.den (w1T frame.child.num frame.child.den)
        (w1t frame.child.num frame.child.den (x, y) - frame.child.num)
        (w1s frame.child.num frame.child.den (x, y) - (frame.child.den + frame.child.num)) ∨
      ¬ BoundarySpectrum.EvenRect frame.child.num frame.child.den (w1T frame.child.num frame.child.den)
        (w1t frame.child.num frame.child.den (x, y) + frame.child.num)
        (w1s frame.child.num frame.child.den (x, y) + (frame.child.den + frame.child.num)) ∨
      ¬ BoundarySpectrum.EvenRect frame.child.num frame.child.den (w1T frame.child.num frame.child.den)
        (w1t frame.child.num frame.child.den (x, y) + frame.child.den)
        (w1s frame.child.num frame.child.den (x, y) - (frame.child.den - frame.child.num)) ∨
      ¬ BoundarySpectrum.EvenRect frame.child.num frame.child.den (w1T frame.child.num frame.child.den)
        (w1t frame.child.num frame.child.den (x, y) - frame.child.den)
        (w1s frame.child.num frame.child.den (x, y) + (frame.child.den - frame.child.num)) := by
    rcases hex with h | h | h | h
    · left; rw [closedRect_even_iff _ _ _ e1, FreeCutPred.w1t_predX, FreeCutPred.w1s_predX] at h; exact h
    · right; left; rw [closedRect_even_iff _ _ _ e2, FreeCutPred.w1t_succX, FreeCutPred.w1s_succX] at h; exact h
    · right; right; left
      rw [closedRect_even_iff _ _ _ e3, FreeCutPred.w1t_predY, w1s_predY'] at h; exact h
    · right; right; right
      rw [closedRect_even_iff _ _ _ e4, FreeCutPred.w1t_succY, FreeCutPred.w1s_succY] at h; exact h
  have hres := BoundarySpectrum.spectrum_odd frame.child.num frame.child.den (w1T frame.child.num frame.child.den)
    (w1t frame.child.num frame.child.den (x, y)) (w1s frame.child.num frame.child.den (x, y))
    (by omega) (by omega) hnodd hdodd hT hTe ht hs hO hex'
  rcases hres with ⟨hH, hSo⟩ | ⟨hV, hSw⟩ | ⟨hO3, hV3, hS3⟩ | ⟨hO4, hH4, hS4⟩
  · -- the free H arc at the site itself
    have hH' : frame.child.num ≤ w1t frame.child.num frame.child.den (x, y) ∧
        w1t frame.child.num frame.child.den (x, y) ≤ frame.child.den := hH
    have hSouth : ¬ closedRect frame.child.num frame.child.den (x, y - 1) := by
      rw [closedRect_even_iff _ _ _ e3, FreeCutPred.w1t_predY, w1s_predY']; exact hSo
    have hspec : frame.hSpectrum (frame.tGrade (x, y)) := by
      rw [tGrade_eq_w1t]; unfold ChildFrame.hSpectrum; right; exact ⟨by omega, hH'.1, hH'.2⟩
    have hmem : (x, y) ∈ frame.freeH := (FreeCutSucc.mem_freeH_iff frame (x, y)).mpr ⟨hcl, hSouth, hspec⟩
    exact ⟨0, 0, Or.inl (by simpa using hmem)⟩
  · -- the free V arc at the site itself
    have hWest : ¬ closedRect frame.child.num frame.child.den (x - 1, y) := by
      rw [closedRect_even_iff _ _ _ e1, FreeCutPred.w1t_predX, FreeCutPred.w1s_predX]; exact hSw
    have hvspec : frame.vSpectrum (frame.sGrade (x, y)) := by
      rw [sGrade_eq_w1s]; unfold ChildFrame.vSpectrum; exact ⟨hs, hV⟩
    have hmem : (x, y) ∈ frame.freeV := (FreeCutSucc.mem_freeV_iff frame (x, y)).mpr ⟨hcl, hWest, hvspec⟩
    exact ⟨0, 0, Or.inr (by simpa using hmem)⟩
  · -- the free V arc at `z - K`
    have hwO : ¬ EvenSite (x - frame.child.den, y - frame.child.num) := by
      unfold EvenSite; show ¬ ((x - frame.child.den + (y - frame.child.num)) % 2 = 0); omega
    have hwWE : EvenSite (x - frame.child.den - 1, y - frame.child.num) := by
      unfold EvenSite; show (x - frame.child.den - 1 + (y - frame.child.num)) % 2 = 0; omega
    have hwCl : closedRect frame.child.num frame.child.den (x - frame.child.den, y - frame.child.num) :=
      (closedRect_odd_iff _ _ _ hwO).mpr (by rw [w1t_sub_K, w1s_sub_K]; exact hO3)
    have hwWest : ¬ closedRect frame.child.num frame.child.den (x - frame.child.den - 1, y - frame.child.num) := by
      rw [closedRect_even_iff _ _ _ hwWE, FreeCutPred.w1t_predX, FreeCutPred.w1s_predX, w1t_sub_K, w1s_sub_K]
      exact hS3
    have hwSpec : frame.vSpectrum (frame.sGrade (x - frame.child.den, y - frame.child.num)) := by
      rw [sGrade_eq_w1s, w1s_sub_K]; unfold ChildFrame.vSpectrum; exact ⟨by omega, hV3⟩
    have hmem : (x - frame.child.den, y - frame.child.num) ∈ frame.freeV :=
      (FreeCutSucc.mem_freeV_iff frame _).mpr ⟨hwCl, hwWest, hwSpec⟩
    exact ⟨1, 0, Or.inr (by simpa using hmem)⟩
  · -- the free H arc at `z - V`
    have hwO : ¬ EvenSite (x - (frame.child.num - frame.child.den), y - (frame.child.num + frame.child.den)) := by
      unfold EvenSite
      show ¬ ((x - (frame.child.num - frame.child.den) + (y - (frame.child.num + frame.child.den))) % 2 = 0)
      omega
    have hwSE : EvenSite (x - (frame.child.num - frame.child.den), y - (frame.child.num + frame.child.den) - 1) := by
      unfold EvenSite
      show (x - (frame.child.num - frame.child.den) + (y - (frame.child.num + frame.child.den) - 1)) % 2 = 0
      omega
    have hwCl : closedRect frame.child.num frame.child.den
        (x - (frame.child.num - frame.child.den), y - (frame.child.num + frame.child.den)) :=
      (closedRect_odd_iff _ _ _ hwO).mpr (by rw [w1t_sub_V, w1s_sub_V]; exact hO4)
    have hwSouth : ¬ closedRect frame.child.num frame.child.den
        (x - (frame.child.num - frame.child.den), y - (frame.child.num + frame.child.den) - 1) := by
      rw [closedRect_even_iff _ _ _ hwSE, FreeCutPred.w1t_predY, w1s_predY', w1t_sub_V, w1s_sub_V]
      exact hS4
    have hwSpec : frame.hSpectrum (frame.tGrade
        (x - (frame.child.num - frame.child.den), y - (frame.child.num + frame.child.den))) := by
      rw [tGrade_eq_w1t, w1t_sub_V]; unfold ChildFrame.hSpectrum; right
      exact ⟨by omega, by unfold BoundarySpectrum.HSpO at hH4; omega, by unfold BoundarySpectrum.HSpO at hH4; omega⟩
    have hmem : (x - (frame.child.num - frame.child.den), y - (frame.child.num + frame.child.den)) ∈ frame.freeH :=
      (FreeCutSucc.mem_freeH_iff frame _).mpr ⟨hwCl, hwSouth, hwSpec⟩
    exact ⟨0, 1, Or.inl (by simpa using hmem)⟩

/-- **The first exit is free modulo the span.** If `u` is an input of a strict site `z` and `u` is not strict, then `u` is
free modulo the span `K = (d, n)`, `V = (n − d, n + d)`. -/
theorem first_exit_free (frame : ChildFrame) {z u : Site}
    (hz : StrictInterior frame.child.num frame.child.den z) (hE : Edge u z)
    (hnot : ¬ StrictInterior frame.child.num frame.child.den u) : FreeMod frame u := by
  have hm := FLatticePaper.W4White.strict_neighbours_mem frame hz
  rw [FLatticePaper.W1.closedPolygon_eq_closedRect] at hm
  simp only [Set.mem_setOf_eq] at hm
  have hcl : closedRect frame.child.num frame.child.den u := by
    unfold Edge at hE
    rcases hE with h | h
    · rw [h]; exact hm.1
    · rw [h]; exact hm.2
  have hE' : u = incomingNeg z ∨ u = incomingPos z := hE
  obtain ⟨x, y⟩ := u
  have hs : StrictInterior frame.child.num frame.child.den (x - 1, y) ∨
      StrictInterior frame.child.num frame.child.den (x + 1, y) ∨
      StrictInterior frame.child.num frame.child.den (x, y - 1) ∨
      StrictInterior frame.child.num frame.child.den (x, y + 1) := by
    rcases edge_nbr (x, y) z hE' with h | h | h | h
    · right; left; rw [h] at hz; exact hz
    · left; rw [h] at hz; exact hz
    · right; right; right; rw [h] at hz; exact hz
    · right; right; left; rw [h] at hz; exact hz
  by_cases he : EvenSite (x, y)
  · have hex := exit_hex_even frame he hnot hs
    exact free_of_even frame he hcl hex
  · have hex := exit_hex_odd frame he hnot hs
    exact free_of_odd frame he hcl hex

end FLatticePaper.FirstExit
