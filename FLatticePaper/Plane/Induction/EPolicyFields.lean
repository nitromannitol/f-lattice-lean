import FLatticePaper.Plane.Induction.EPolicyLap
import FLatticePaper.Plane.Induction.S3FreeBoundary
import FLatticePaper.Plane.Induction.SignedPolicy
import FLatticePaper.Tiles.BottomEdges

/-!
# The white structure of the signed policy e(-1, eta) on the reciprocal field (task 118, W1 base)

At a native white `p` the rule of `EPolicy.RetNat` keeps exactly one input, given by the explicit displacement `selDisp`:
an even white keeps `(eta, 0)` at its free V_last and corner points, `(1, 0)` at its other free-aliased points, and the x-rule
otherwise; an odd white keeps `(0, -eta)` when its free alias is the H_1 point or a V-odd point, and `(0, 1)` otherwise.

The free aliases of a native point are only: the point itself, the H point `(p.1 + d - 1, 0)` of a top-row point (shift
`(0,-1)`), and the V point `(p.1 - d, p.2 - 1)` of an anti-diagonal point, or the V points `(0,0)`, `(2-d, d)` of `(d,1)`,
`(2, d+1)` (shift `(-1,0)`). `freeAlias_cases` is this classification, by enumerating the alias window.
-/

namespace FLatticePaper.EPolicy

open Classical FLatticePaper FLatticePaper.PureRank FLatticePaper.Construction FLatticePaper.Farey
open FLatticePaper.Induction

/-- The retained displacement of the sign-`η` policy at a native white `p` (the explicit form of the rule). -/
noncomputable def selDisp (d η : ℤ) (p : Pt) : Pt :=
  if EvenSite p then
    (if p = (2 - d, d) ∨ p = (2, d + 1) then (η, 0)
     else if (p.2 = 0 ∧ 2 ≤ p.1) ∨ p = (0, 0) ∨ p = (d, 1) ∨ (p.2 = d + 1 ∧ 3 - d ≤ p.1 ∧ p.1 ≤ 0) then (1, 0)
     else if p.1 ≤ 0 then (-1, 0) else (1, 0))
  else
    (if (p.2 = 0 ∧ p.1 = 1) ∨ (p.1 + p.2 = 1 ∧ 1 ≤ p.2 ∧ p.2 ≤ d - 1) ∨ (p.1 + p.2 = d + 2 ∧ 2 ≤ p.1 ∧ p.1 ≤ d) ∨
        (p.2 = d + 1 ∧ p.1 = 2 - d)
     then (0, -η) else (0, 1))

set_option maxHeartbeats 400000 in
/-- The free aliases of a native point: the point itself, the top-row H point, or the anti-diagonal V point. -/
theorem freeAlias_cases {d : ℤ} (hd : 3 ≤ d) (hdodd : d % 2 = 1) {p q : Pt} (hN : NativeP d p)
    (hA : FreeAliasAt d p q) :
    (q.1 = p.1 ∧ q.2 = p.2) ∨
    (q.2 = 0 ∧ q.1 = p.1 + d - 1 ∧ p.2 = d + 1 ∧ 2 - d ≤ p.1 ∧ p.1 ≤ 1) ∨
    (q.1 = p.1 - d ∧ q.2 = p.2 - 1 ∧
      ((p.1 + p.2 = d + 2 ∧ 2 ≤ p.1 ∧ p.1 ≤ d) ∨ (p.1 = 2 ∧ p.2 = d + 1) ∨ (p.1 = d ∧ p.2 = 1))) := by
  obtain ⟨x, y⟩ := p
  obtain ⟨i, j, hij, hq, hN', hF⟩ := hA
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hij
  subst hq
  unfold IsFreeP IsHc IsVc at hF
  unfold NativeP at hN hN'
  simp only [shiftP, Prod.mk.injEq] at hF hN hN' ⊢
  interval_cases i <;> interval_cases j <;> rcases hN with hN | hN | hN <;>
    rcases hN' with hN' | hN' | hN' <;> rcases hF with hF | hF | hF | hF <;> omega

/-- The even native points with a free alias: the special even points of the rule. -/
def SpecialE (d x y : ℤ) : Prop :=
  (x = 2 - d ∧ y = d) ∨ (x = 2 ∧ y = d + 1) ∨ (y = 0 ∧ 2 ≤ x) ∨ (x = 0 ∧ y = 0) ∨ (x = d ∧ y = 1) ∨
    (y = d + 1 ∧ 3 - d ≤ x ∧ x ≤ 0)

/-- The odd native white points whose retained displacement is `(0, -eta)`. -/
def OddDown (d x y : ℤ) : Prop :=
  (y = 0 ∧ x = 1) ∨ (x + y = 1 ∧ 1 ≤ y ∧ y ≤ d - 1) ∨ (x + y = d + 2 ∧ 2 ≤ x ∧ x ≤ d) ∨ (y = d + 1 ∧ x = 2 - d)

theorem selDisp_odd {d η : ℤ} {x y : ℤ} (h : ¬ EvenSite (x, y)) :
    selDisp d η (x, y) = if OddDown d x y then (0, -η) else (0, 1) := by
  unfold selDisp
  rw [if_neg h]
  unfold OddDown
  split_ifs <;> simp_all

theorem freeAlias_isFree {d : ℤ} {p q : Pt} (h : FreeAliasAt d p q) : IsFreeP d q := by
  obtain ⟨i, j, -, -, -, hF⟩ := h
  exact hF

/-- The box bounds of a native point. -/
theorem nativeP_box {d : ℤ} (hd : 3 ≤ d) {x y : ℤ} (h : NativeP d (x, y)) :
    2 - d ≤ x ∧ x ≤ d ∧ 0 ≤ y ∧ y ≤ d + 1 := by
  unfold NativeP at h
  rcases h with ⟨h1, h2, h3, h4, -, -⟩ | h | h
  · exact ⟨h1, h2, h3, h4⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    omega
  · simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    omega

set_option maxHeartbeats 400000 in
/-- A native even point has a free alias exactly on the special even set. -/
theorem even_alias_iff {d : ℤ} (hd : 3 ≤ d) (hdodd : d % 2 = 1) {x y : ℤ} (hN : NativeP d (x, y))
    (hev : EvenSite (x, y)) : (∃ q, FreeAliasAt d (x, y) q) ↔ SpecialE d x y := by
  constructor
  · rintro ⟨q, hq⟩
    have hF := freeAlias_isFree hq
    rcases freeAlias_cases hd hdodd hN hq with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3⟩
    · have hqe : q = (x, y) := Prod.ext h1 h2
      rw [hqe] at hF
      unfold IsFreeP IsHc IsVc at hF
      unfold EvenSite at hev
      unfold SpecialE
      simp only [Prod.mk.injEq] at hF
      omega
    · unfold EvenSite at hev
      unfold SpecialE
      dsimp only at h1 h2 h3 h4 h5
      omega
    · unfold EvenSite at hev
      unfold SpecialE
      dsimp only at h1 h2 h3
      rcases h3 with ⟨h31, h32, h33⟩ | ⟨h31, h32⟩ | ⟨h31, h32⟩
      · exfalso
        omega
      · right; left; exact ⟨h31, h32⟩
      · right; right; right; right; left; exact ⟨h31, h32⟩
  · intro hS
    obtain ⟨hb1, hb2, hb3, hb4⟩ := nativeP_box hd hN
    unfold SpecialE at hS
    rcases hS with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨(x, y), 0, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, hN, ?_⟩
      · simp [shiftP]
      · simp [IsFreeP, IsHc, IsVc, h1, h2]
    · refine ⟨(2 - d, d), -1, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, ?_, ?_⟩
      · simp only [shiftP, Prod.mk.injEq, h1, h2]
        constructor <;> ring
      · unfold NativeP
        left
        dsimp only
        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
      · simp [IsFreeP, IsHc, IsVc]
    · refine ⟨(x, y), 0, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, hN, ?_⟩
      · simp [shiftP]
      · unfold IsFreeP IsHc
        left
        dsimp only
        exact ⟨h1, by omega, by omega⟩
    · refine ⟨(x, y), 0, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, hN, ?_⟩
      · simp [shiftP]
      · simp [IsFreeP, IsHc, IsVc, h1, h2]
    · refine ⟨(0, 0), -1, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, ?_, ?_⟩
      · simp only [shiftP, Prod.mk.injEq, h1, h2]
        constructor <;> ring
      · unfold NativeP
        right
        left
        rfl
      · simp [IsFreeP, IsHc, IsVc]
    · refine ⟨(x + d - 1, 0), 0, -1, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, ?_, ?_⟩
      · simp only [shiftP, Prod.mk.injEq, h1]
        constructor <;> ring
      · unfold NativeP
        left
        dsimp only
        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
      · unfold IsFreeP IsHc
        left
        dsimp only
        exact ⟨rfl, by omega, by omega⟩

theorem selDisp_even_val {d η : ℤ} {x y : ℤ} (hev : EvenSite (x, y)) :
    selDisp d η (x, y) =
      if SpecialE d x y then (if (x = 2 - d ∧ y = d) ∨ (x = 2 ∧ y = d + 1) then (η, 0) else (1, 0))
      else (if x ≤ 0 then (-1, 0) else (1, 0)) := by
  unfold selDisp
  rw [if_pos hev]
  unfold SpecialE
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all <;> omega

theorem freeEdge_H {d η : ℤ} {q e : Pt} (h : IsHc d q) :
    freeEdge d η q e ↔ (if q.1 = 1 then e = (0, -η) else e.1 + e.2 = 1) := by
  unfold freeEdge
  rw [if_pos h]

theorem freeEdge_V {d η : ℤ} {q e : Pt} (hH : ¬ IsHc d q) (hV : IsVc d q) (hq : q ≠ (0, 0)) :
    freeEdge d η q e ↔ (e.1 = η ∧ e.2 = 0) ∨ (e.1 = 0 ∧ e.2 = -η) := by
  unfold freeEdge
  rw [if_neg hH, if_pos hV, if_neg hq]

theorem freeEdge_V0 {d η : ℤ} {e : Pt} (_hd : 3 ≤ d) : freeEdge d η (0, 0) e ↔ e.1 = 1 := by
  have hH : ¬ IsHc d (0, 0) := by
    unfold IsHc
    simp
  unfold freeEdge
  rw [if_neg hH, if_pos (show IsVc d (0, 0) from Or.inl rfl), if_pos rfl]

theorem incomingNeg_even {x y : ℤ} (h : EvenSite (x, y)) : incomingNeg (x, y) = (x - 1, y) := by
  unfold incomingNeg
  rw [if_pos h]

theorem incomingPos_even {x y : ℤ} (h : EvenSite (x, y)) : incomingPos (x, y) = (x + 1, y) := by
  unfold incomingPos
  rw [if_pos h]

theorem incomingNeg_odd {x y : ℤ} (h : ¬ EvenSite (x, y)) : incomingNeg (x, y) = (x, y - 1) := by
  unfold incomingNeg
  rw [if_neg h]

theorem incomingPos_odd {x y : ℤ} (h : ¬ EvenSite (x, y)) : incomingPos (x, y) = (x, y + 1) := by
  unfold incomingPos
  rw [if_neg h]

/-- The direction of a free alias of a native even point: `(1, 0)`, or `(eta, 0)` at its V_last and corner points. -/
theorem even_alias_dir {d η : ℤ} (hd : 3 ≤ d) (hdodd : d % 2 = 1) {x y : ℤ} (hN : NativeP d (x, y))
    (hev : EvenSite (x, y)) (hx1 : x ≠ 1) {e1 e2 : ℤ} (hax : (e1 = -1 ∧ e2 = 0) ∨ (e1 = 1 ∧ e2 = 0))
    {q : Pt} (hq : FreeAliasAt d (x, y) q) (hfe : freeEdge d η q (e1, e2)) :
    (e1, e2) = if (x = 2 - d ∧ y = d) ∨ (x = 2 ∧ y = d + 1) then (η, 0) else (1, 0) := by
  have hev' : (x + y) % 2 = 0 := hev
  obtain ⟨hb1, hb2, hb3, hb4⟩ := nativeP_box hd hN
  obtain ⟨q1, q2⟩ := q
  rcases freeAlias_cases hd hdodd hN hq with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3⟩
  · dsimp only at h1 h2
    have hqe : ((q1, q2) : Pt) = (x, y) := Prod.ext h1 h2
    rw [hqe] at hfe
    by_cases hH : IsHc d (x, y)
    · rw [freeEdge_H hH] at hfe
      have hy0 : y = 0 := hH.1
      have hnV : ¬ ((x = 2 - d ∧ y = d) ∨ (x = 2 ∧ y = d + 1)) := by
        rintro (⟨-, h⟩ | ⟨-, h⟩) <;> omega
      rw [if_neg hnV]
      rw [if_neg (show ¬ (x, y).1 = 1 from hx1)] at hfe
      simp only [Prod.mk.injEq] at hfe ⊢
      omega
    · unfold freeEdge at hfe
      rw [if_neg hH] at hfe
      by_cases h00 : (x, y) = (0, 0)
      · rw [if_pos (show IsVc d (x, y) from Or.inl h00), if_pos h00] at hfe
        have hnV : ¬ ((x = 2 - d ∧ y = d) ∨ (x = 2 ∧ y = d + 1)) := by
          simp only [Prod.mk.injEq] at h00
          omega
        rw [if_neg hnV]
        simp only [Prod.mk.injEq] at hfe h00 ⊢
        omega
      · by_cases hV : IsVc d (x, y)
        · rw [if_pos hV, if_neg h00] at hfe
          have hVd : x = 2 - d ∧ y = d := by
            unfold IsVc at hV
            rcases hV with h | h | h
            · exact absurd h h00
            · dsimp only at h
              omega
            · exact Prod.mk.inj h
          rw [if_pos (Or.inl hVd)]
          dsimp only at hfe
          rcases hfe with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
          · exact Prod.ext h1' h2'
          · exfalso
            omega
        · rw [if_neg hV] at hfe
          exact hfe.elim
  · dsimp only at h1 h2 h3 h4 h5
    have hH : IsHc d (q1, q2) := ⟨h1, by dsimp only; omega, by dsimp only; omega⟩
    rw [freeEdge_H hH] at hfe
    dsimp only at hfe
    have hq1 : q1 ≠ 1 := by omega
    rw [if_neg hq1] at hfe
    have hnV : ¬ ((x = 2 - d ∧ y = d) ∨ (x = 2 ∧ y = d + 1)) := by
      rintro (⟨-, h⟩ | ⟨h, -⟩) <;> omega
    rw [if_neg hnV]
    simp only [Prod.mk.injEq] at hfe ⊢
    omega
  · dsimp only at h1 h2 h3
    rcases h3 with ⟨h31, h32, h33⟩ | ⟨h31, h32⟩ | ⟨h31, h32⟩
    · exfalso
      omega
    · have hqe : ((q1, q2) : Pt) = (2 - d, d) := Prod.ext (by dsimp only; omega) (by dsimp only; omega)
      rw [hqe] at hfe
      have hHn : ¬ IsHc d (2 - d, d) := fun h => by
        have h0 : d = 0 := h.1
        omega
      have hne : ((2 - d, d) : Pt) ≠ (0, 0) := fun h => by
        simp only [Prod.mk.injEq] at h
        omega
      rw [freeEdge_V hHn (Or.inr (Or.inr rfl)) hne] at hfe
      rw [if_pos (Or.inr ⟨h31, h32⟩)]
      dsimp only at hfe
      rcases hfe with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · exact Prod.ext h1' h2'
      · exfalso
        omega
    · have hqe : ((q1, q2) : Pt) = (0, 0) := Prod.ext (by dsimp only; omega) (by dsimp only; omega)
      rw [hqe, freeEdge_V0 hd] at hfe
      dsimp only at hfe
      have hnV : ¬ ((x = 2 - d ∧ y = d) ∨ (x = 2 ∧ y = d + 1)) := by
        rintro (⟨-, h⟩ | ⟨h, -⟩) <;> omega
      rw [if_neg hnV]
      simp only [Prod.mk.injEq] at hfe ⊢
      omega

/-- A special even point keeps its displacement through a free alias. -/
theorem even_special_exists {d η : ℤ} (hd : 3 ≤ d) (hdodd : d % 2 = 1) {x y : ℤ} (hN : NativeP d (x, y))
    (hev : EvenSite (x, y)) {e1 e2 : ℤ} (hS : SpecialE d x y)
    (he : (e1, e2) = if (x = 2 - d ∧ y = d) ∨ (x = 2 ∧ y = d + 1) then (η, 0) else (1, 0)) :
    ∃ q, FreeAliasAt d (x, y) q ∧ freeEdge d η q (e1, e2) := by
  have hev' : (x + y) % 2 = 0 := hev
  obtain ⟨hb1, hb2, hb3, hb4⟩ := nativeP_box hd hN
  unfold SpecialE at hS
  rcases hS with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hV : (x = 2 - d ∧ y = d) ∨ (x = 2 ∧ y = d + 1) := Or.inl ⟨h1, h2⟩
    rw [if_pos hV] at he
    simp only [Prod.mk.injEq] at he
    have hH : ¬ IsHc d (x, y) := fun h => by
      have h0 : y = 0 := h.1
      omega
    have hVc : IsVc d (x, y) := by
      unfold IsVc
      right; right
      simp [h1, h2]
    have hne : ((x, y) : Pt) ≠ (0, 0) := fun h => by
      simp only [Prod.mk.injEq] at h
      omega
    have hFree : IsFreeP d (x, y) := Or.inr hVc
    have hfe : freeEdge d η (x, y) (e1, e2) := by
      rw [freeEdge_V hH hVc hne]
      omega
    exact ⟨(x, y), ⟨0, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, by simp [shiftP], hN, hFree⟩, hfe⟩
  · have hV : (x = 2 - d ∧ y = d) ∨ (x = 2 ∧ y = d + 1) := Or.inr ⟨h1, h2⟩
    rw [if_pos hV] at he
    simp only [Prod.mk.injEq] at he
    have hq : ((x, y) : Pt) = (x, y) := rfl
    have hsh : shiftP d (x, y) (-1) 0 = (2 - d, d) := by
      simp only [shiftP, h1, h2, Prod.mk.injEq]
      constructor <;> ring
    have hN' : NativeP d (2 - d, d) := by
      unfold NativeP
      left
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    have hH : ¬ IsHc d (2 - d, d) := fun h => by
      have h0 : d = 0 := h.1
      omega
    have hVc : IsVc d (2 - d, d) := Or.inr (Or.inr rfl)
    have hne : ((2 - d, d) : Pt) ≠ (0, 0) := fun h => by
      simp only [Prod.mk.injEq] at h
      omega
    have hFree : IsFreeP d (2 - d, d) := Or.inr hVc
    have hfe : freeEdge d η (2 - d, d) (e1, e2) := by
      rw [freeEdge_V hH hVc hne]
      dsimp only
      omega
    exact ⟨(2 - d, d), ⟨-1, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, hsh.symm, hN', hFree⟩, hfe⟩
  · have hV : ¬ ((x = 2 - d ∧ y = d) ∨ (x = 2 ∧ y = d + 1)) := by
      rintro (⟨-, h⟩ | ⟨-, h⟩) <;> omega
    rw [if_neg hV] at he
    simp only [Prod.mk.injEq] at he
    have hH : IsHc d (x, y) := ⟨h1, by omega, by omega⟩
    have hx1 : ¬ (x, y).1 = 1 := by
      dsimp only
      omega
    have hfe : freeEdge d η (x, y) (e1, e2) := by
      rw [freeEdge_H hH, if_neg hx1]
      dsimp only
      omega
    exact ⟨(x, y), ⟨0, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, by simp [shiftP], hN, Or.inl hH⟩, hfe⟩
  · have hpt : ((x, y) : Pt) = (0, 0) := Prod.ext h1 h2
    have hV : ¬ ((x = 2 - d ∧ y = d) ∨ (x = 2 ∧ y = d + 1)) := by
      rintro (⟨-, h⟩ | ⟨-, h⟩) <;> omega
    rw [if_neg hV] at he
    simp only [Prod.mk.injEq] at he
    have hVc : IsVc d (x, y) := by
      rw [hpt]
      exact Or.inl rfl
    have hfe : freeEdge d η (x, y) (e1, e2) := by
      rw [hpt, freeEdge_V0 hd]
      dsimp only
      omega
    exact ⟨(x, y), ⟨0, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, by simp [shiftP], hN, Or.inr hVc⟩, hfe⟩
  · have hV : ¬ ((x = 2 - d ∧ y = d) ∨ (x = 2 ∧ y = d + 1)) := by
      rintro (⟨-, h⟩ | ⟨h, -⟩) <;> omega
    rw [if_neg hV] at he
    simp only [Prod.mk.injEq] at he
    have hsh : shiftP d (x, y) (-1) 0 = (0, 0) := by
      simp only [shiftP, h1, h2, Prod.mk.injEq]
      constructor <;> ring
    have hfe : freeEdge d η (0, 0) (e1, e2) := by
      rw [freeEdge_V0 hd]
      dsimp only
      omega
    have hN' : NativeP d (0, 0) := by
      unfold NativeP
      right; left; rfl
    exact ⟨(0, 0), ⟨-1, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, hsh.symm, hN', Or.inr (Or.inl rfl)⟩, hfe⟩
  · have hV : ¬ ((x = 2 - d ∧ y = d) ∨ (x = 2 ∧ y = d + 1)) := by
      rintro (⟨-, h⟩ | ⟨h, -⟩) <;> omega
    rw [if_neg hV] at he
    simp only [Prod.mk.injEq] at he
    have hsh : shiftP d (x, y) 0 (-1) = (x + d - 1, 0) := by
      simp only [shiftP, h1, Prod.mk.injEq]
      constructor <;> ring
    have hN' : NativeP d (x + d - 1, 0) := by
      unfold NativeP
      left
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    have hH : IsHc d (x + d - 1, 0) := ⟨rfl, by omega, by omega⟩
    have hfe : freeEdge d η (x + d - 1, 0) (e1, e2) := by
      rw [freeEdge_H hH]
      have hx1 : ¬ (x + d - 1, 0).1 = 1 := by
        dsimp only
        omega
      rw [if_neg hx1]
      dsimp only
      omega
    exact ⟨(x + d - 1, 0), ⟨0, -1, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, hsh.symm, hN', Or.inl hH⟩, hfe⟩

/-- The displacement of an incoming neighbour: `(±1, 0)` at even centres, `(0, ±1)` at odd centres. -/
theorem axis_iff (x y e1 e2 : ℤ) :
    ((x, y) + (e1, e2) = incomingNeg (x, y) ∨ (x, y) + (e1, e2) = incomingPos (x, y)) ↔
      (EvenSite (x, y) ∧ ((e1 = -1 ∧ e2 = 0) ∨ (e1 = 1 ∧ e2 = 0))) ∨
        (¬ EvenSite (x, y) ∧ ((e1 = 0 ∧ e2 = -1) ∨ (e1 = 0 ∧ e2 = 1))) := by
  by_cases h : EvenSite (x, y)
  · rw [incomingNeg_even h, incomingPos_even h]
    simp only [Prod.mk_add_mk, Prod.mk.injEq]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨h, Or.inl ⟨by omega, by omega⟩⟩
      · exact Or.inl ⟨h, Or.inr ⟨by omega, by omega⟩⟩
    · rintro (⟨-, h1⟩ | ⟨hn, -⟩)
      · rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by omega, by omega⟩
        · exact Or.inr ⟨by omega, by omega⟩
      · exact absurd h hn
  · rw [incomingNeg_odd h, incomingPos_odd h]
    simp only [Prod.mk_add_mk, Prod.mk.injEq]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inr ⟨h, Or.inl ⟨by omega, by omega⟩⟩
      · exact Or.inr ⟨h, Or.inr ⟨by omega, by omega⟩⟩
    · rintro (⟨he, -⟩ | ⟨-, h1⟩)
      · exact absurd he h
      · rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by omega, by omega⟩
        · exact Or.inr ⟨by omega, by omega⟩

/-- At a native even white `(x, y)` with `x ≠ 1`, the rule keeps exactly the displacement `selDisp`. -/
theorem retNat_white_even {d η : ℤ} (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hη : η = 1 ∨ η = -1) {x y : ℤ}
    (hN : NativeP d (x, y)) (hev : EvenSite (x, y)) (hx1 : x ≠ 1) (e1 e2 : ℤ) :
    RetNat d η False (x, y) ((x, y) + (e1, e2)) ↔ (e1, e2) = selDisp d η (x, y) := by
  have hev' : (x + y) % 2 = 0 := hev
  rw [selDisp_even_val hev]
  unfold RetNat
  simp only [add_sub_cancel_left]
  rw [axis_iff x y e1 e2]
  constructor
  · rintro ⟨hax, hret⟩
    have he : (e1 = -1 ∧ e2 = 0) ∨ (e1 = 1 ∧ e2 = 0) := by
      rcases hax with ⟨-, h⟩ | ⟨hne, -⟩
      · exact h
      · exact absurd hev hne
    rcases hret with hF | ⟨-, hnoal, hxr⟩ | ⟨q, hq, hfe⟩
    · exact hF.elim
    · have hns : ¬ SpecialE d x y := fun hs => hnoal ((even_alias_iff hd hdodd hN hev).2 hs)
      rw [incomingNeg_even hev, incomingPos_even hev] at hxr
      rw [if_neg hns]
      rcases hxr with ⟨hx0, h⟩ | ⟨hx2, h⟩
      · rw [if_pos hx0]
        simp only [Prod.mk_add_mk, Prod.mk.injEq] at h ⊢
        omega
      · rw [if_neg (show ¬ x ≤ 0 by omega)]
        simp only [Prod.mk_add_mk, Prod.mk.injEq] at h ⊢
        omega
    · have hS : SpecialE d x y := (even_alias_iff hd hdodd hN hev).1 ⟨q, hq⟩
      rw [if_pos hS]
      exact even_alias_dir hd hdodd hN hev hx1 he hq hfe
  · intro he
    by_cases hS : SpecialE d x y
    · rw [if_pos hS] at he
      have hAx : (e1 = -1 ∧ e2 = 0) ∨ (e1 = 1 ∧ e2 = 0) := by
        by_cases hV : (x = 2 - d ∧ y = d) ∨ (x = 2 ∧ y = d + 1)
        · rw [if_pos hV] at he
          simp only [Prod.mk.injEq] at he
          omega
        · rw [if_neg hV] at he
          simp only [Prod.mk.injEq] at he
          omega
      refine ⟨Or.inl ⟨hev, hAx⟩, Or.inr (Or.inr ?_)⟩
      exact even_special_exists hd hdodd hN hev hS he
    · rw [if_neg hS] at he
      have hAx : (e1 = -1 ∧ e2 = 0) ∨ (e1 = 1 ∧ e2 = 0) := by
        by_cases hx0 : x ≤ 0
        · rw [if_pos hx0] at he
          simp only [Prod.mk.injEq] at he
          omega
        · rw [if_neg hx0] at he
          simp only [Prod.mk.injEq] at he
          omega
      refine ⟨Or.inl ⟨hev, hAx⟩, Or.inr (Or.inl ⟨hev, ?_, ?_⟩)⟩
      · rintro ⟨q, hq⟩
        exact hS ((even_alias_iff hd hdodd hN hev).1 ⟨q, hq⟩)
      · by_cases hx0 : x ≤ 0
        · left
          rw [if_pos hx0] at he
          simp only [Prod.mk.injEq] at he
          refine ⟨hx0, ?_⟩
          rw [incomingNeg_even hev]
          simp only [Prod.mk_add_mk, Prod.mk.injEq]
          omega
        · right
          rw [if_neg hx0] at he
          simp only [Prod.mk.injEq] at he
          refine ⟨by omega, ?_⟩
          rw [incomingPos_even hev]
          simp only [Prod.mk_add_mk, Prod.mk.injEq]
          omega

/-- The direction of a free alias of a native odd point: `(0, -eta)` on the H_1 point, the V_odd and the anti-diagonal
points, and `(0, 1)` on the other H-type and top-row points. -/
theorem odd_alias_dir {d η : ℤ} (hd : 3 ≤ d) (hdodd : d % 2 = 1) {x y : ℤ} (hN : NativeP d (x, y))
    (hodd : ¬ EvenSite (x, y)) {e1 e2 : ℤ} (hv : e1 = 0 ∧ (e2 = -1 ∨ e2 = 1))
    {q : Pt} (hq : FreeAliasAt d (x, y) q) (hfe : freeEdge d η q (e1, e2)) :
    (e1, e2) = if OddDown d x y then (0, -η) else (0, 1) := by
  have hodd' : (x + y) % 2 = 1 := by
    unfold EvenSite at hodd
    omega
  obtain ⟨hb1, hb2, hb3, hb4⟩ := nativeP_box hd hN
  obtain ⟨q1, q2⟩ := q
  rcases freeAlias_cases hd hdodd hN hq with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3⟩
  · dsimp only at h1 h2
    have hqe : ((q1, q2) : Pt) = (x, y) := Prod.ext h1 h2
    rw [hqe] at hfe
    by_cases hH : IsHc d (x, y)
    · rw [freeEdge_H hH] at hfe
      have hy0 : y = 0 := hH.1
      by_cases hx1 : x = 1
      · rw [if_pos (show (x, y).1 = 1 from hx1)] at hfe
        have hD : OddDown d x y := Or.inl ⟨hy0, hx1⟩
        rw [if_pos hD]
        simp only [Prod.mk.injEq] at hfe ⊢
        exact ⟨hfe.1, hfe.2⟩
      · rw [if_neg (show ¬ (x, y).1 = 1 from hx1)] at hfe
        have hnD : ¬ OddDown d x y := by
          unfold OddDown
          rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> omega
        rw [if_neg hnD]
        simp only [Prod.mk.injEq] at hfe ⊢
        omega
    · unfold freeEdge at hfe
      rw [if_neg hH] at hfe
      by_cases h00 : (x, y) = (0, 0)
      · exfalso
        simp only [Prod.mk.injEq] at h00
        omega
      · by_cases hV : IsVc d (x, y)
        · rw [if_pos hV, if_neg h00] at hfe
          have hsum : x + y = 1 ∧ 1 ≤ y ∧ y < d := by
            unfold IsVc at hV
            rcases hV with h | h | h
            · exact absurd h h00
            · dsimp only at h
              exact h
            · exfalso
              simp only [Prod.mk.injEq] at h
              omega
          have hD : OddDown d x y := Or.inr (Or.inl ⟨hsum.1, hsum.2.1, by omega⟩)
          rw [if_pos hD]
          dsimp only at hfe
          simp only [Prod.mk.injEq] at hfe ⊢
          omega
        · rw [if_neg hV] at hfe
          exact hfe.elim
  · dsimp only at h1 h2 h3 h4 h5
    have hH : IsHc d (q1, q2) := ⟨h1, by dsimp only; omega, by dsimp only; omega⟩
    rw [freeEdge_H hH] at hfe
    dsimp only at hfe
    by_cases hq1 : q1 = 1
    · rw [if_pos hq1] at hfe
      have hD : OddDown d x y := Or.inr (Or.inr (Or.inr ⟨h3, by omega⟩))
      rw [if_pos hD]
      simp only [Prod.mk.injEq] at hfe ⊢
      omega
    · rw [if_neg hq1] at hfe
      have hnD : ¬ OddDown d x y := by
        unfold OddDown
        rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, h2, -⟩ | ⟨h, h'⟩) <;> omega
      rw [if_neg hnD]
      simp only [Prod.mk.injEq] at hfe ⊢
      omega
  · dsimp only at h1 h2 h3
    rcases h3 with ⟨h31, h32, h33⟩ | ⟨h31, h32⟩ | ⟨h31, h32⟩
    · have hVq : IsVc d (q1, q2) := Or.inr (Or.inl ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩)
      have hHq : ¬ IsHc d (q1, q2) := fun h => by
        have h0 : q2 = 0 := h.1
        omega
      have hne : ((q1, q2) : Pt) ≠ (0, 0) := fun h => by
        simp only [Prod.mk.injEq] at h
        omega
      rw [freeEdge_V hHq hVq hne] at hfe
      have hD : OddDown d x y := Or.inr (Or.inr (Or.inl ⟨h31, h32, h33⟩))
      rw [if_pos hD]
      simp only [Prod.mk.injEq] at hfe ⊢
      omega
    · exfalso
      omega
    · exfalso
      omega

/-- A native odd point has coordinate sum in `[1, d+2]`. -/
theorem nativeP_sum_odd {d : ℤ} (hdodd : d % 2 = 1) {x y : ℤ} (h : NativeP d (x, y))
    (hodd : ¬ EvenSite (x, y)) : 1 ≤ x + y ∧ x + y ≤ d + 2 := by
  unfold NativeP at h
  rcases h with ⟨-, -, -, -, h5, h6⟩ | h | h
  · exact ⟨h5, h6⟩
  · exfalso
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    apply hodd
    unfold EvenSite
    show (x + y) % 2 = 0
    omega
  · exfalso
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    apply hodd
    unfold EvenSite
    show (x + y) % 2 = 0
    omega

/-- At a native odd white `(x, y)` the rule keeps exactly the displacement `selDisp`. -/
theorem retNat_white_odd {d η : ℤ} (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hη : η = 1 ∨ η = -1) {x y : ℤ}
    (hN : NativeP d (x, y)) (hodd : ¬ EvenSite (x, y))
    (hw : ¬ (0 < y ∧ y < d + 1 ∧ 1 < x + y ∧ x + y < d + 2)) (e1 e2 : ℤ) :
    RetNat d η False (x, y) ((x, y) + (e1, e2)) ↔ (e1, e2) = selDisp d η (x, y) := by
  obtain ⟨hb1, hb2, hb3, hb4⟩ := nativeP_box hd hN
  obtain ⟨hs1, hs2⟩ := nativeP_sum_odd hdodd hN hodd
  have hodd' : (x + y) % 2 = 1 := by
    unfold EvenSite at hodd
    omega
  rw [selDisp_odd hodd]
  unfold RetNat
  simp only [add_sub_cancel_left]
  rw [axis_iff x y e1 e2]
  constructor
  · rintro ⟨hax, hret⟩
    have hv : e1 = 0 ∧ (e2 = -1 ∨ e2 = 1) := by
      rcases hax with ⟨he, -⟩ | ⟨-, h⟩
      · exact absurd he hodd
      · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1, Or.inl h2⟩
        · exact ⟨h1, Or.inr h2⟩
    rcases hret with hF | ⟨hev', -, -⟩ | ⟨q, hq, hfe⟩
    · exact hF.elim
    · exact absurd hev' hodd
    · exact odd_alias_dir hd hdodd hN hodd hv hq hfe
  · intro he
    have hwd : y = 0 ∨ y = d + 1 ∨ x + y = 1 ∨ x + y = d + 2 := by
      omega
    by_cases hD : OddDown d x y
    · rw [if_pos hD] at he
      simp only [Prod.mk.injEq] at he
      have hAx : (e1 = 0 ∧ e2 = -1) ∨ (e1 = 0 ∧ e2 = 1) := by
        rcases hη with h | h <;> omega
      refine ⟨Or.inr ⟨hodd, hAx⟩, Or.inr (Or.inr ?_)⟩
      unfold OddDown at hD
      rcases hD with ⟨hy0, hx1⟩ | ⟨hs, hy1, hy2⟩ | ⟨hs, hx2, hx3⟩ | ⟨hy, hx⟩
      · have hH : IsHc d (x, y) := ⟨hy0, by omega, by omega⟩
        refine ⟨(x, y), ⟨0, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, by simp [shiftP], hN, Or.inl hH⟩, ?_⟩
        rw [freeEdge_H hH, if_pos (show (x, y).1 = 1 from hx1)]
        simp only [Prod.mk.injEq]
        omega
      · have hVc : IsVc d (x, y) := Or.inr (Or.inl ⟨hs, hy1, by omega⟩)
        have hH : ¬ IsHc d (x, y) := fun h => by
          have h0 : y = 0 := h.1
          omega
        have hne : ((x, y) : Pt) ≠ (0, 0) := fun h => by
          simp only [Prod.mk.injEq] at h
          omega
        refine ⟨(x, y), ⟨0, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, by simp [shiftP], hN, Or.inr hVc⟩, ?_⟩
        rw [freeEdge_V hH hVc hne]
        omega
      · have hsh : shiftP d (x, y) (-1) 0 = (x - d, y - 1) := by
          simp only [shiftP, Prod.mk.injEq]
          constructor <;> ring
        have hN' : NativeP d (x - d, y - 1) := by
          unfold NativeP
          left
          dsimp only
          refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
        have hVc : IsVc d (x - d, y - 1) := Or.inr (Or.inl ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩)
        have hH : ¬ IsHc d (x - d, y - 1) := fun h => by
          have h0 : y - 1 = 0 := h.1
          omega
        have hne : ((x - d, y - 1) : Pt) ≠ (0, 0) := fun h => by
          simp only [Prod.mk.injEq] at h
          omega
        refine ⟨(x - d, y - 1), ⟨-1, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, hsh.symm, hN', Or.inr hVc⟩, ?_⟩
        rw [freeEdge_V hH hVc hne]
        omega
      · have hsh : shiftP d (x, y) 0 (-1) = (x + d - 1, 0) := by
          simp only [shiftP, Prod.mk.injEq, hy]
          constructor <;> ring
        have hN' : NativeP d (x + d - 1, 0) := by
          unfold NativeP
          left
          dsimp only
          refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
        have hH : IsHc d (x + d - 1, 0) := ⟨rfl, by dsimp only; omega, by dsimp only; omega⟩
        refine ⟨(x + d - 1, 0), ⟨0, -1, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, hsh.symm, hN', Or.inl hH⟩, ?_⟩
        rw [freeEdge_H hH]
        have hq1 : (x + d - 1, 0).1 = 1 := by
          dsimp only
          omega
        rw [if_pos hq1]
        simp only [Prod.mk.injEq]
        omega
    · rw [if_neg hD] at he
      simp only [Prod.mk.injEq] at he
      have hAx : (e1 = 0 ∧ e2 = -1) ∨ (e1 = 0 ∧ e2 = 1) := by
        omega
      refine ⟨Or.inr ⟨hodd, hAx⟩, Or.inr (Or.inr ?_)⟩
      unfold OddDown at hD
      have hlines : y = 0 ∨ y = d + 1 := by
        rcases hwd with h | h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exfalso
          rcases (show y = 0 ∨ 1 ≤ y by omega) with hy0 | hy1'
          · exact hD (Or.inl ⟨hy0, by omega⟩)
          · exact hD (Or.inr (Or.inl ⟨h, hy1', by omega⟩))
        · by_cases hy' : y = d + 1
          · exact Or.inr hy'
          · exfalso
            exact hD (Or.inr (Or.inr (Or.inl ⟨h, by omega, by omega⟩)))
      rcases hlines with hy0 | hy1
      · have hH : IsHc d (x, y) := ⟨hy0, by omega, by omega⟩
        refine ⟨(x, y), ⟨0, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, by simp [shiftP], hN, Or.inl hH⟩, ?_⟩
        have hx1' : ¬ (x, y).1 = 1 := by
          dsimp only
          exact fun h => hD (Or.inl ⟨hy0, h⟩)
        rw [freeEdge_H hH, if_neg hx1']
        dsimp only
        omega
      · have hsh : shiftP d (x, y) 0 (-1) = (x + d - 1, 0) := by
          simp only [shiftP, Prod.mk.injEq, hy1]
          constructor <;> ring
        have hN' : NativeP d (x + d - 1, 0) := by
          unfold NativeP
          left
          dsimp only
          refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
        have hH : IsHc d (x + d - 1, 0) := ⟨rfl, by dsimp only; omega, by dsimp only; omega⟩
        refine ⟨(x + d - 1, 0), ⟨0, -1, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, hsh.symm, hN', Or.inl hH⟩, ?_⟩
        rw [freeEdge_H hH]
        have hq1 : ¬ (x + d - 1, 0).1 = 1 := by
          dsimp only
          intro h
          exact hD (Or.inr (Or.inr (Or.inr ⟨hy1, by omega⟩)))
        rw [if_neg hq1]
        dsimp only
        omega

/-- The white native points: the reciprocal laplacian is zero there (even points off `x = 1`, odd points off the open band). -/
def WhiteN (d : ℤ) (p : Pt) : Prop :=
  (EvenSite p ∧ p.1 ≠ 1) ∨ (¬ EvenSite p ∧ ¬ (0 < p.2 ∧ p.2 < d + 1 ∧ 1 < p.1 + p.2 ∧ p.1 + p.2 < d + 2))

/-- At a native white, the rule keeps exactly the displacement `selDisp` (for points given as pairs). -/
theorem retNat_white_pt {d η : ℤ} (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hη : η = 1 ∨ η = -1) {p : Pt}
    (hN : NativeP d p) (hW : WhiteN d p) (e : Pt) :
    RetNat d η False p (p + e) ↔ e = selDisp d η p := by
  obtain ⟨x, y⟩ := p
  obtain ⟨e1, e2⟩ := e
  rcases hW with ⟨hev, hx1⟩ | ⟨hodd, hw⟩
  · exact retNat_white_even hd hdodd hη hN hev hx1 e1 e2
  · exact retNat_white_odd hd hdodd hη hN hodd hw e1 e2

/-- A black-or-white condition on the black clause: a false black condition does not change the rule. -/
theorem retNat_black_false {d η : ℤ} {P : Prop} (hP : ¬ P) (p i : Pt) :
    RetNat d η P p i ↔ RetNat d η False p i := by
  unfold RetNat
  simp only [hP, false_or]

/-- The reciprocal laplacian is zero at a native point exactly on the white set. -/
theorem whiteN_of_lap_zero (k : ℕ) {p : Pt} (hN : NativeP (2 * (k : ℤ) + 3) p)
    (h : laplacian (reciprocalField k) p = 0) : WhiteN (2 * (k : ℤ) + 3) p := by
  rw [laplacian_reciprocal_native k hN] at h
  obtain ⟨x, y⟩ := p
  unfold WhiteN
  by_cases hev : EvenSite (x, y)
  · rw [if_pos hev] at h
    left
    refine ⟨hev, ?_⟩
    intro hx1
    have hx1' : (x, y).1 = 1 := hx1
    rw [if_pos hx1'] at h
    norm_num at h
  · rw [if_neg hev] at h
    right
    refine ⟨hev, ?_⟩
    intro hc
    have hc' : 0 < (x, y).2 ∧ (x, y).2 < (2 * (k : ℤ) + 3) + 1 ∧ 1 < (x, y).1 + (x, y).2 ∧
        (x, y).1 + (x, y).2 < (2 * (k : ℤ) + 3) + 2 := hc
    rw [if_pos hc'] at h
    norm_num at h

/-- The policy at a native representative, through the white rule: a white centre keeps exactly `selDisp` of its representative. -/
theorem ePolicy_white (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (c i : Pt)
    (hc : laplacian (reciprocalField k) c = 0) :
    ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) c i ↔
      i - c = selDisp (2 * (k : ℤ) + 3) η (nativeRep (2 * (k : ℤ) + 3) c) := by
  obtain ⟨hyN, -⟩ := nativeRep_spec (stairEven_valid_reciprocal k) c
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have hdodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hb : ¬ (laplacian (reciprocalField k) c = -1) := by
    rw [hc]
    norm_num
  have hy0 : laplacian (reciprocalField k) (nativeRep (2 * (k : ℤ) + 3) c) = 0 := by
    rw [← laplacian_reciprocal_rep]
    exact hc
  have hW : WhiteN (2 * (k : ℤ) + 3) (nativeRep (2 * (k : ℤ) + 3) c) :=
    whiteN_of_lap_zero k hyN hy0
  unfold ePolicy
  rw [retNat_black_false hb]
  exact retNat_white_pt hd3 hdodd hη hyN hW (i - c)

/-- Two native points differ by a small deck vector: the coefficient `b` is `-1`, `0` or `1`, and the coefficient `a` is
then forced (the only native duplicates are the H/top, V/anti-diagonal and the two corner pairs). -/
theorem native_pair_cases {d : ℤ} (hd : 3 ≤ d) {p q : Pt} (hp : NativeP d p) (hq : NativeP d q) {a b : ℤ}
    (h1 : q.1 = p.1 + a * d + b * (1 - d)) (h2 : q.2 = p.2 + a + b * (d + 1)) :
    (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  obtain ⟨hp1, hp2, hp3, hp4⟩ := nativeP_box hd hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := nativeP_box hd hq
  dsimp only at h1 h2 hp1 hp2 hp3 hp4 hq1 hq2 hq3 hq4
  have key : b * (d * d + 2 * d - 1) = (q2 - p2) * d - (q1 - p1) := by
    rw [h1, h2]
    ring
  have hD : 0 < d * d + 2 * d - 1 := by nlinarith
  have hu2 : (q2 - p2) * d ≤ (d + 1) * d := by nlinarith
  have hu2' : -((d + 1) * d) ≤ (q2 - p2) * d := by nlinarith
  have hb1 : b ≤ 1 := by
    by_contra hc
    simp only [not_le] at hc
    nlinarith
  have hb2 : -1 ≤ b := by
    by_contra hc
    simp only [not_le] at hc
    nlinarith
  rcases (show b = -1 ∨ b = 0 ∨ b = 1 by omega) with rfl | rfl | rfl
  · have ha1 : a ≤ 0 := by nlinarith
    have ha2 : -2 ≤ a := by nlinarith
    rcases (show a = -2 ∨ a = -1 ∨ a = 0 by omega) with rfl | rfl | rfl
    · nlinarith
    · nlinarith
    · right; right; right; right; exact ⟨rfl, rfl⟩
  · have ha1 : a ≤ 1 := by nlinarith
    have ha2 : -1 ≤ a := by nlinarith
    rcases (show a = -1 ∨ a = 0 ∨ a = 1 by omega) with rfl | rfl | rfl
    · right; right; left; exact ⟨rfl, rfl⟩
    · left; exact ⟨rfl, rfl⟩
    · right; left; exact ⟨rfl, rfl⟩
  · have ha1 : a ≤ 2 := by nlinarith
    have ha2 : 0 ≤ a := by nlinarith
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl
    · right; right; right; left; exact ⟨rfl, rfl⟩
    · nlinarith
    · nlinarith

set_option maxHeartbeats 400000 in
/-- The selection along the deck vector `(d, 1)`: the native pairs `p`, `p + (d, 1)`. -/
theorem selDisp_dup_U {d η : ℤ} (hd : 3 ≤ d) (hdodd : d % 2 = 1) (_hη : η = 1 ∨ η = -1) {p q : Pt}
    (hp : NativeP d p) (hq : NativeP d q) (h1 : q.1 = p.1 + d) (h2 : q.2 = p.2 + 1) :
    selDisp d η p = selDisp d η q := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  dsimp only at h1 h2
  have hp' := hp
  have hq' := hq
  unfold NativeP at hp' hq'
  simp only [Prod.mk.injEq] at hp' hq'
  rcases hp' with ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ | ⟨hp7, hp8⟩ | ⟨hp7, hp8⟩ <;>
    rcases hq' with ⟨hq1, hq2, hq3, hq4, hq5, hq6⟩ | ⟨hq7, hq8⟩ | ⟨hq7, hq8⟩ <;>
    (by_cases hev : EvenSite (p1, p2)
     · have hpar : (p1 + p2) % 2 = 0 := hev
       have hev' : EvenSite (q1, q2) := by
         unfold EvenSite
         dsimp only
         omega
       rw [selDisp_even_val hev, selDisp_even_val hev']
       unfold SpecialE
       split_ifs <;> simp only [Prod.mk.injEq] <;> omega
     · have hpar : (p1 + p2) % 2 = 1 := by
         unfold EvenSite at hev
         dsimp only at hev
         omega
       have hodd' : ¬ EvenSite (q1, q2) := by
         unfold EvenSite
         dsimp only
         omega
       rw [selDisp_odd hev, selDisp_odd hodd']
       unfold OddDown
       split_ifs <;> simp only [Prod.mk.injEq] <;> omega)

set_option maxHeartbeats 400000 in
/-- The selection along the deck vector `(1 - d, d + 1)`: the native pairs `p`, `p + (1 - d, d + 1)`. -/
theorem selDisp_dup_V {d η : ℤ} (hd : 3 ≤ d) (hdodd : d % 2 = 1) (_hη : η = 1 ∨ η = -1) {p q : Pt}
    (hp : NativeP d p) (hq : NativeP d q) (h1 : q.1 = p.1 + (1 - d)) (h2 : q.2 = p.2 + (d + 1)) :
    selDisp d η p = selDisp d η q := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  dsimp only at h1 h2
  have hp' := hp
  have hq' := hq
  unfold NativeP at hp' hq'
  simp only [Prod.mk.injEq] at hp' hq'
  rcases hp' with ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ | ⟨hp7, hp8⟩ | ⟨hp7, hp8⟩ <;>
    rcases hq' with ⟨hq1, hq2, hq3, hq4, hq5, hq6⟩ | ⟨hq7, hq8⟩ | ⟨hq7, hq8⟩ <;>
    (by_cases hev : EvenSite (p1, p2)
     · have hpar : (p1 + p2) % 2 = 0 := hev
       have hev' : EvenSite (q1, q2) := by
         unfold EvenSite
         dsimp only
         omega
       rw [selDisp_even_val hev, selDisp_even_val hev']
       unfold SpecialE
       split_ifs <;> simp only [Prod.mk.injEq] <;> omega
     · have hpar : (p1 + p2) % 2 = 1 := by
         unfold EvenSite at hev
         dsimp only at hev
         omega
       have hodd' : ¬ EvenSite (q1, q2) := by
         unfold EvenSite
         dsimp only
         omega
       rw [selDisp_odd hev, selDisp_odd hodd']
       unfold OddDown
       split_ifs <;> simp only [Prod.mk.injEq] <;> omega)

/-- The selection is invariant under the deck identifications of the native domain. -/
theorem selDisp_dup {d η : ℤ} (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hη : η = 1 ∨ η = -1) {p q : Pt}
    (hp : NativeP d p) (hq : NativeP d q) {a b : ℤ}
    (h1 : q.1 = p.1 + a * d + b * (1 - d)) (h2 : q.2 = p.2 + a + b * (d + 1)) :
    selDisp d η p = selDisp d η q := by
  rcases native_pair_cases hd hp hq h1 h2 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · subst ha
    subst hb
    have e1 : q.1 = p.1 := by simpa using h1
    have e2 : q.2 = p.2 := by simpa using h2
    rw [Prod.ext e1 e2]
  · subst ha
    subst hb
    exact selDisp_dup_U hd hdodd hη hp hq (by linarith) (by linarith)
  · subst ha
    subst hb
    exact (selDisp_dup_U hd hdodd hη hq hp (by linarith) (by linarith)).symm
  · subst ha
    subst hb
    exact selDisp_dup_V hd hdodd hη hp hq (by linarith) (by linarith)
  · subst ha
    subst hb
    exact (selDisp_dup_V hd hdodd hη hq hp (by linarith) (by linarith)).symm

/-- The displacement of `selDisp` at a native point is an incoming displacement. -/
theorem selDisp_axis {d η : ℤ} (_hd : 3 ≤ d) (_hdodd : d % 2 = 1) (hη : η = 1 ∨ η = -1) {p : Pt}
    (hN : NativeP d p) : selDisp d η p = incomingNeg p - p ∨ selDisp d η p = incomingPos p - p := by
  obtain ⟨x, y⟩ := p
  by_cases hev : EvenSite (x, y)
  · have hn : incomingNeg (x, y) - (x, y) = (-1, 0) := by
      rw [incomingNeg_even hev]
      ext <;> (simp; try ring)
    have hp : incomingPos (x, y) - (x, y) = (1, 0) := by
      rw [incomingPos_even hev]
      ext <;> (simp; try ring)
    rw [selDisp_even_val hev, hn, hp]
    split_ifs <;> rcases hη with rfl | rfl <;> simp
  · have hn : incomingNeg (x, y) - (x, y) = (0, -1) := by
      rw [incomingNeg_odd hev]
      ext <;> (simp; try ring)
    have hp : incomingPos (x, y) - (x, y) = (0, 1) := by
      rw [incomingPos_odd hev]
      ext <;> (simp; try ring)
    rw [selDisp_odd hev, hn, hp]
    split_ifs <;> rcases hη with rfl | rfl <;> simp

/-- An incoming displacement of the representative is an incoming displacement of the translated centre. -/
theorem selAxis_translate {y c l : Pt} (hl : (l.1 + l.2) % 2 = 0) (hc : c = y + l) {e : Pt}
    (he : e = incomingNeg y - y ∨ e = incomingPos y - y) :
    c + e = incomingNeg c ∨ c + e = incomingPos c := by
  subst hc
  rw [incomingNeg_add hl, incomingPos_add hl]
  rcases he with rfl | rfl
  · left
    abel
  · right
    abel

/-- The selected input of the signed policy `e(-1, eta)` at `c` (the `sel` of the canonical signed policy). -/
noncomputable def selF (k : ℕ) (η : ℤ) (c : Pt) : Pt :=
  c + selDisp (2 * (k : ℤ) + 3) η (nativeRep (2 * (k : ℤ) + 3) c)

theorem selF_input (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (c : Pt) :
    selF k η c = incomingNeg c ∨ selF k η c = incomingPos c := by
  obtain ⟨hyN, i, j, hc⟩ := nativeRep_spec (stairEven_valid_reciprocal k) c
  unfold selF
  exact selAxis_translate (combine_sum_even (by omega) i j) hc
    (selDisp_axis (by omega) (by omega) hη hyN)

/-- At a white centre the policy keeps exactly the selected input. -/
theorem ePolicy_iff_sel (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (c i : Pt)
    (hc : laplacian (reciprocalField k) c = 0) :
    ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) c i ↔ i = selF k η c := by
  rw [ePolicy_white k η hη c i hc]
  unfold selF
  constructor
  · intro h
    rw [← h]
    abel
  · intro h
    rw [h]
    abel

/-- The quota of the signed policy `e(-1, eta)` on the reciprocal field. -/
theorem retainQuota_e (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) :
    RetainQuota (reciprocalField k) (ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k))) := by
  refine ⟨fun c hb => ePolicy_black (by omega) (stairEven_valid_reciprocal k) η _ c hb, fun c hw => ?_⟩
  rcases selF_input k η hη c with h | h
  · exact Or.inl ((ePolicy_iff_sel k η hη c _ hw).2 h.symm)
  · exact Or.inr ((ePolicy_iff_sel k η hη c _ hw).2 h.symm)

/-- The free whites of the signed policy keep one input: the selected one. -/
theorem freePrescribed_e (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (c : Pt)
    (hw : laplacian (reciprocalField k) c = 0) :
    ∃ i, (i = incomingNeg c ∨ i = incomingPos c) ∧
      ∀ j, ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) c j ↔ j = i :=
  ⟨selF k η c, selF_input k η hη c, fun j => ePolicy_iff_sel k η hη c j hw⟩

/-- On the H trace of the reciprocal frame the explicit prescription is the selected displacement. -/
theorem prescribedH_reciprocal (k : ℕ) (η : ℤ) (_hη : η = 1 ∨ η = -1) (x : ℤ) (hx1 : 1 ≤ x)
    (hxd : x ≤ 2 * (k : ℤ) + 3) :
    selDisp (2 * (k : ℤ) + 3) η (x, 0) = (reciprocalFrame k).prescribedH η (x, 0) := by
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have hdodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  unfold ChildFrame.prescribedH ChildFrame.hLast
  rw [reciprocal_child_den, reciprocal_child_num]
  by_cases h1 : x = 1
  · subst h1
    have hO : ¬ EvenSite ((1 : ℤ), (0 : ℤ)) := by
      unfold EvenSite
      norm_num
    rw [selDisp_odd hO]
    have hD : OddDown (2 * (k : ℤ) + 3) 1 0 := Or.inl ⟨rfl, rfl⟩
    rw [if_pos hD]
    unfold hFirst
    simp
  · by_cases hdx : x = 2 * (k : ℤ) + 3
    · subst hdx
      have hO : ¬ EvenSite (2 * (k : ℤ) + 3, (0 : ℤ)) := by
        unfold EvenSite
        dsimp only
        omega
      rw [selDisp_odd hO]
      have hnD : ¬ OddDown (2 * (k : ℤ) + 3) (2 * (k : ℤ) + 3) 0 := by
        unfold OddDown
        rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> omega
      rw [if_neg hnD]
      have hne1 : ((2 * (k : ℤ) + 3, (0 : ℤ)) : Pt) ≠ hFirst := by
        unfold hFirst
        intro h
        simp only [Prod.mk.injEq] at h
        omega
      have h1' : (2 * (k : ℤ) + 3) ≠ 1 := by omega
      simp [hne1]
    · by_cases hev : EvenSite (x, (0 : ℤ))
      · have hx2 : 2 ≤ x := by
          unfold EvenSite at hev
          dsimp only at hev
          omega
        rw [selDisp_even_val hev]
        have hS : SpecialE (2 * (k : ℤ) + 3) x 0 := Or.inr (Or.inr (Or.inl ⟨rfl, hx2⟩))
        have hV : ¬ ((x = 2 - (2 * (k : ℤ) + 3) ∧ (0 : ℤ) = 2 * (k : ℤ) + 3) ∨
            (x = 2 ∧ (0 : ℤ) = 2 * (k : ℤ) + 3 + 1)) := by
          rintro (⟨-, h⟩ | ⟨-, h⟩) <;> omega
        rw [if_pos hS, if_neg hV]
        have hne1 : ((x, (0 : ℤ)) : Pt) ≠ hFirst := by
          unfold hFirst
          intro h
          simp only [Prod.mk.injEq] at h
          omega
        have hneL : ((x, (0 : ℤ)) : Pt) ≠ (2 * (k : ℤ) + 3, 0) := by
          intro h
          simp only [Prod.mk.injEq] at h
          omega
        have hEv : EvenSite (x, (0 : ℤ)) := hev
        simp [hne1, hneL, hEv]
      · have hO : ¬ EvenSite (x, (0 : ℤ)) := hev
        rw [selDisp_odd hO]
        have hnD : ¬ OddDown (2 * (k : ℤ) + 3) x 0 := by
          unfold OddDown
          rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> omega
        rw [if_neg hnD]
        have hne1 : ((x, (0 : ℤ)) : Pt) ≠ hFirst := by
          unfold hFirst
          intro h
          simp only [Prod.mk.injEq] at h
          omega
        have hneL : ((x, (0 : ℤ)) : Pt) ≠ (2 * (k : ℤ) + 3, 0) := by
          intro h
          simp only [Prod.mk.injEq] at h
          omega
        simp [hne1, hneL, hO]

/-- The sign of the reciprocal frame: `eps = -1` at `3^k`, so the exceptional west input of the canonical policy is vacuous. -/
theorem reciprocal_eps (k : ℕ) : (reciprocalFrame k).eps = -1 := by
  unfold ChildFrame.eps
  have h := FLatticePaper.Tiles.parentsAt_replicate_three k
  show Fraction.det (parentsAt (List.replicate k Digit.three)).odd (parentsAt (List.replicate k Digit.three)).even = -1
  rw [h]
  unfold Fraction.det
  ring

end FLatticePaper.EPolicy
