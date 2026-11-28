import FLatticePaper.Tiles.MixedCompatWalks
import FLatticePaper.Tiles.H3Data
import FLatticePaper.Tiles.StringCover

/-! The height on the part of a forward string that can meet the opposite register. -/

namespace FLatticePaper.Tiles.MixedStringGrade

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open SiteInduction SiteStrings SurgicalWeak JointFamily Standard StandardClause
open HorizontalStepOne ClosedPathTriangle SiteFwdCover

private theorem local_zero (t : ZTile) (n d : ℤ) (hn : 0 < n) (hd : n < d)
    (b : Site) (hb : b ∈ tileShape t) (hg : -d < n*b.1 - d*b.2) : zTileOdo t b = 0 := by
  cases t <;> simp only [tileShape, List.mem_cons, List.not_mem_nil, or_false] at hb
  all_goals repeat' rcases hb with hb | hb
  all_goals first | decide | simp at hg <;> omega

/-- A point of the forward string above the grade threshold has the height of the first tile. -/
theorem forward_value (o : PartialOdometer) (w : BinaryWord) (n d β : ℤ)
    (hn : 0 < n) (hd : n < d) (hq : w.head? = some .q) (hc : CursorB w n d)
    (hr : RespectsTiles .horizontal false (hStringAt w 0) o.val)
    (hβ : FirstTileNormal o 0 β) (z : Site) (hz : z ∈ stringSites false false w)
    (hgrade : -n < n*z.1-d*z.2) : o.val z = β := by
  obtain ⟨t, rfl⟩ : ∃ t : BinaryWord, w = .q :: t := by
    cases w with
    | nil => simp at hq
    | cons l ls => exact ⟨ls, by simpa using congrArg (fun a => a.toList ++ ls) hq⟩
  let ts := hStringAt (.q :: t) 0
  obtain ⟨α,K,h⟩ := horizontal_formula (.q :: t) 0 o.val hr
  have at0 : ts.getD 0 (ZTile.zero, 0) = (ZTile.one, 0) := by
    dsimp [ts]; rw [hStringAt_eq, hAuxG_head]; rfl
  have pos : 0 < ts.length := by dsimp [ts]; rw [ClosedPathCorners.hStringAt_length']; simp
  have hN : FirstTileNormal o α K := by
    intro x hx
    have v := h 0 pos x (by rw [mem_dom_iff, famOf_tile, at0]; simpa using hx)
    rw [at0] at v
    exact ⟨(hβ x hx).1, by dsimp [dotS, ptDot, normed] at v ⊢; simp only [sub_zero] at v; linarith⟩
  obtain ⟨rfl,rfl⟩ := WeakStepAssembly.normal_unique _ _ _ _ _ hN hβ
  obtain ⟨k,hk,v⟩ := (StringCover.covers_iff_stringSites _ _).2 hz
  change z ∈ (tileShape (ts.getD k (ZTile.zero,0)).1).map (· + (ts.getD k (ZTile.zero,0)).2) at v
  have hk' : k < (Letter.q :: t).length := by rwa [ClosedPathCorners.hStringAt_length'] at hk
  obtain ⟨b,hb,hbz⟩ := List.mem_map.1 v
  have hmem : z - (ts.getD k (ZTile.zero,0)).2 ∈ tileShape (ts.getD k (ZTile.zero,0)).1 := by
    rw [← hbz, add_sub_cancel_right]; exact hb
  have hzv := h k hk z (by rw [mem_dom_iff, famOf_tile]; exact hmem)
  have eb := (eps_bounds (.q :: t) n d hc (k+1) (by omega)).1
  have ht := congrArg Prod.snd (fwd_tile t k hk')
  change (ts.getD k (ZTile.zero,0)).2 = _ at ht
  have hgz : n*b.1-d*b.2 > -d := by
    rw [← hbz, ht] at hgrade
    simp only [Prod.fst_add, Prod.snd_add] at hgrade
    push_cast at eb
    nlinarith only [hgrade, eb]
  have loc := local_zero _ n d hn hd b hb hgz
  change o.val z = zTileOdo (ts.getD k (ZTile.zero,0)).1 (z-(ts.getD k (ZTile.zero,0)).2) + ptDot 0 z + _ at hzv
  have hzoff : z-(ts.getD k (ZTile.zero,0)).2 = b := by rw [← hbz, add_sub_cancel_right]
  rw [hzoff, loc] at hzv
  simpa [ptDot] using hzv

/-- The two displacements of a horizontal mixed contact, in coordinates based at the bottom
of each copy. The second copy has been turned by a half turn. -/
def contactSum (w : Word) (z : Site) : Prop :=
  let A := texV1Odd (parentsAt w).odd
  let U := texV1Even (parentsAt w).even
  if phase w = 1 then z = A + (1,-1) ∨ z = A - U + (1,-1)
  else z = U + (1,-1) ∨ z = U + U + (1,-1)

private theorem grade_neg (n d m e j p q x y : ℤ) (hn : 0 < n) (hd : n < d)
    (hm : 0 < m) (he : m < e) (he3 : 3 ≤ e) (hbig : 2 ≤ n ∨ 2 ≤ m)
    (hj : j = 1 ∨ j = 2) (hdet : n*e-m*d = -1)
    (hx : n-d+1 ≤ x ∧ x ≤ 2*d) (hy : m-e+1 ≤ y ∧ y ≤ e)
    (hxys : x+y = j*e+1) (hp : p ≤ max d (2*n)) (hq : q ≤ max e (2*m))
    (h₁ : e*(p+n) + d*q = e*(d+2*n-j)+y)
    (h₂ : d*(q+m) + e*p = d*(e+2*m)-x) : -n < p ∧ -m < q := by
  have hd0 : 0 ≤ d := by omega
  have he0 : 0 ≤ e := by omega
  have smallP (hs : n = 1) : 2*d-1 ≤ e := by
    have h : 2 ≤ m := by omega
    subst n
    nlinarith only [hdet, mul_nonneg (sub_nonneg.mpr h) hd0]
  have smallQ (hs : m = 1) : 2*e+1 ≤ d := by
    have h : 2 ≤ n := by omega
    subst m
    nlinarith only [hdet, mul_nonneg (sub_nonneg.mpr h) he0]
  constructor
  · by_contra! h
    have h0 := mul_nonpos_of_nonneg_of_nonpos he0 (show p+n ≤ 0 by omega)
    rcases le_total (2*m) e with hlow | hhigh
    · rw [max_eq_left hlow] at hq
      have hneg : e*(2*n-j)+y ≤ 0 := by
        nlinarith only [h₁,h0,mul_le_mul_of_nonneg_left hq hd0]
      by_cases h : 1 ≤ 2*n-j
      · have := mul_le_mul_of_nonneg_left h he0
        omega
      · have h' : n = 1 := by omega
        have := smallP h'
        have h'' : j = 2 := by omega
        subst n; subst j
        simp at hneg
        omega
    · rw [max_eq_right hhigh] at hq
      have hneg : e*(d-j)+y ≤ 2 := by
        nlinarith only [h₁,h0,hdet,mul_le_mul_of_nonneg_left hq hd0]
      by_cases h : 3 ≤ d
      · have h' : 1 ≤ d-j := by omega
        have := mul_le_mul_of_nonneg_left h' he0
        have h'' : 2 ≤ m := by omega
        omega
      · have h' : d = 2 := by omega
        subst d
        rcases hj with rfl | rfl <;> simp at hxys hneg <;> omega
  · by_contra! h
    have h0 := mul_nonpos_of_nonneg_of_nonpos hd0 (show q+m ≤ 0 by omega)
    rcases le_total (2*n) d with hlow | hhigh
    · rw [max_eq_left hlow] at hp
      have hneg : d*(2*m) ≤ x := by
        nlinarith only [h₂,h0,mul_le_mul_of_nonneg_left hp he0]
      by_cases h : 2 ≤ m
      · have := mul_le_mul_of_nonneg_left (show 4 ≤ 2*m by omega) hd0
        omega
      · have h' : m = 1 := by omega
        have := smallQ h'
        subst m
        rcases hj with rfl | rfl <;> simp at hxys hneg <;> omega
    · rw [max_eq_right hhigh] at hp
      have hneg : d*e+2 ≤ x := by
        nlinarith only [h₂,h0,hdet,mul_le_mul_of_nonneg_left hp he0]
      have := mul_le_mul_of_nonneg_left he3 hd0
      omega

private theorem grade_pos (n d m e j p q x y : ℤ) (hn : 0 < n) (hd : n < d)
    (hm : 0 < m) (he : m < e) (he3 : 3 ≤ e) (hbig : 2 ≤ n ∨ 2 ≤ m)
    (hj : j = 0 ∨ j = 1) (hdet : n*e-m*d = 1)
    (hx : n-d+1 ≤ x ∧ x ≤ 2*d) (hy : m-e+1 ≤ y ∧ y ≤ e)
    (hxys : x+y = 2*d-j*e+1) (hp : p ≤ max d (2*n)) (hq : q ≤ max e (2*m))
    (h₁ : e*(p+n) + d*q = e*(d+2*n-j)-y)
    (h₂ : d*(q+m) + e*p = d*(e+2*m-2)+x) : -n < p ∧ -m < q := by
  have hd0 : 0 ≤ d := by omega
  have he0 : 0 ≤ e := by omega
  have smallP (hs : n = 1) : 2*d+1 ≤ e := by
    have h : 2 ≤ m := by omega
    subst n
    nlinarith only [hdet, mul_nonneg (sub_nonneg.mpr h) hd0]
  have smallQ (hs : m = 1) : 2*e-1 ≤ d := by
    have h : 2 ≤ n := by omega
    subst m
    nlinarith only [hdet, mul_nonneg (sub_nonneg.mpr h) he0]
  constructor
  · by_contra! h
    have h0 := mul_nonpos_of_nonneg_of_nonpos he0 (show p+n ≤ 0 by omega)
    rcases le_total (2*m) e with hlow | hhigh
    · rw [max_eq_left hlow] at hq
      have hneg : e*(2*n-j) ≤ y := by
        nlinarith only [h₁,h0,mul_le_mul_of_nonneg_left hq hd0]
      by_cases h : 2 ≤ 2*n-j
      · have := mul_le_mul_of_nonneg_left h he0
        omega
      · have h' : n = 1 := by omega
        have := smallP h'
        have h'' : j = 1 := by omega
        subst n; subst j; simp at hneg hxys; omega
    · rw [max_eq_right hhigh] at hq
      have hneg : e*(d-j)+2 ≤ y := by
        nlinarith only [h₁,h0,hdet,mul_le_mul_of_nonneg_left hq hd0]
      have := mul_le_mul_of_nonneg_left (show 1 ≤ d-j by omega) he0
      omega
  · by_contra! h
    have h0 := mul_nonpos_of_nonneg_of_nonpos hd0 (show q+m ≤ 0 by omega)
    rcases le_total (2*n) d with hlow | hhigh
    · rw [max_eq_left hlow] at hp
      have hneg : d*(2*m-2)+x ≤ 0 := by
        nlinarith only [h₂,h0,mul_le_mul_of_nonneg_left hp he0]
      by_cases h : 2 ≤ m
      · have := mul_le_mul_of_nonneg_left (show 2 ≤ 2*m-2 by omega) hd0
        omega
      · have h' : m = 1 := by omega
        have := smallQ h'
        subst m
        rcases hj with rfl | rfl <;> simp at hxys hneg <;> omega
    · rw [max_eq_right hhigh] at hp
      have hneg : d*(e-2)+x ≤ 2 := by
        nlinarith only [h₂,h0,hdet,mul_le_mul_of_nonneg_left hp he0]
      by_cases h : 4 ≤ e
      · have := mul_le_mul_of_nonneg_left (show 2 ≤ e-2 by omega) hd0
        omega
      · have h' : e = 3 := by omega
        have hn' : 2 ≤ n := by
          by_contra! h
          have := smallP (by omega)
          omega
        subst e
        simp at hneg
        omega

private theorem parents_large (w : Word) (hw : ¬ IsBase w.dropLast) :
    2 ≤ (parentsAt w).odd.num ∨ 2 ≤ (parentsAt w).even.num := by
  induction w using List.reverseRecOn with
  | nil => exact (hw (Or.inl rfl)).elim
  | append_singleton u s _ =>
    simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil] at hw
    have hp := (H3Data.odd_parent_interior u (H3Data.nonbase_one_two hw)).1
    have hq := (H3Data.even_parent_interior u (H3Data.nonbase_one_three hw)).1
    rw [parentsAt_append_singleton]
    cases s <;> simp [Parents.step, Parents.current, Parents.combine] <;> omega

/-- At a horizontal mixed contact both local coordinates have grade strictly greater than
minus the corresponding numerator. -/
theorem contact_grades (w u v : Word) (hw : ¬ IsBase w.dropLast)
    (hP : (parentsAt w).odd = fracOdd u) (hQ : (parentsAt w).even = fracEven v)
    (x y : Site) (hx : x ∈ oddTile u) (hy : y ∈ evenTile v) (hs : contactSum w (x+y)) :
    -(fracOdd u).num < tCo (fracOdd u) x ∧ -(fracEven v).num < tCo (fracEven v) y := by
  let n := (fracOdd u).num
  let d := (fracOdd u).den
  let m := (fracEven v).num
  let e := (fracEven v).den
  let p := tCo (fracOdd u) x
  let q := tCo (fracEven v) y
  have hi : 0 < n ∧ n < d := SiteHullOdd.curO_pos_lt u
  have hj : 0 < m ∧ m < e := SiteHullEven.curE_pos_lt v
  have ee : (m+e)%2 = 0 := (parentsAt_valid v).current_even_parity
  have e3 : 3 ≤ e := by omega
  have big := parents_large w hw
  rw [hP,hQ] at big
  have hdet := H3Data.eps_det w
  rw [hP,hQ] at hdet
  have hp : p ≤ max d (2*n) := by
    have h := H3Data.lam_bound_odd u x hx
    change -max d (2*n) ≤ d*x.2-n*x.1 at h
    change n*x.1-d*x.2 ≤ _; omega
  have hq : q ≤ max e (2*m) := by
    have h := H3Data.lam_bound_even v y hy
    change -max e (2*m) ≤ e*y.2-m*y.1 at h
    change m*y.1-e*y.2 ≤ _; omega
  have bx := ClosedPathExcluded.site_box_odd u x hx
  have by' := ClosedPathExcluded.site_box_even v y hy
  unfold contactSum at hs
  rw [hP,hQ] at hs
  change n*e-m*d = _ at hdet
  have id₁ : e*(p+n) + d*q = e*(n+tCo (fracOdd u) (x+y))-(n*e-m*d)*y.1 := by
    dsimp [p,q,n,m,d,e,tCo]; ring
  have id₂ : d*(q+m) + e*p = d*(m+tCo (fracEven v) (x+y))+(n*e-m*d)*x.1 := by
    dsimp [p,q,n,m,d,e,tCo]; ring
  by_cases h : phase w = 1
  · rw [if_pos h] at hs hdet
    obtain ⟨j,hj',hh⟩ : ∃ j : ℤ, (j = 0 ∨ j = 1) ∧
        x+y = (2*d-j*e+1,2*n-j*m-1) := by
      rcases hs with hs | hs
      · exact ⟨0, Or.inl rfl, by rw [hs]; ext <;> simp [texV1Odd,d,n,sub_eq_add_neg]⟩
      · exact ⟨1, Or.inr rfl, by rw [hs]; ext <;> simp [texV1Odd,texV1Even,d,n,e,m,sub_eq_add_neg]⟩
    have hP' : tCo (fracOdd u) (x+y) = d+n-j := by
      rw [hh]; change n*(2*d-j*e+1)-d*(2*n-j*m-1) = _
      linear_combination -j * hdet
    have hQ' : tCo (fracEven v) (x+y) = e+m-2 := by
      rw [hh]; change m*(2*d-j*e+1)-e*(2*n-j*m-1) = _
      linear_combination -2 * hdet
    rw [hdet,hP'] at id₁
    rw [hdet,hQ'] at id₂
    exact grade_pos n d m e j p q x.1 y.1 hi.1 hi.2 hj.1 hj.2 e3 big hj' hdet
      ⟨bx.1,bx.2.1⟩ ⟨by'.1,by'.2.1⟩ (congrArg Prod.fst hh) hp hq (by linarith only [id₁]) (by linarith only [id₂])
  · rw [if_neg h] at hs hdet
    obtain ⟨j,hj',hh⟩ : ∃ j : ℤ, (j = 1 ∨ j = 2) ∧
        x+y = (j*e+1,j*m-1) := by
      rcases hs with hs | hs
      · exact ⟨1, Or.inl rfl, by rw [hs]; ext <;> simp [texV1Even,e,m,sub_eq_add_neg]⟩
      · exact ⟨2, Or.inr rfl, by rw [hs]; ext <;> simp [texV1Even,e,m,two_mul,sub_eq_add_neg]⟩
    have hP' : tCo (fracOdd u) (x+y) = d+n-j := by
      rw [hh]; change n*(j*e+1)-d*(j*m-1) = _
      linear_combination j * hdet
    have hQ' : tCo (fracEven v) (x+y) = e+m := by
      rw [hh]; change m*(j*e+1)-e*(j*m-1) = _
      ring
    rw [hdet,hP'] at id₁
    rw [hdet,hQ'] at id₂
    exact grade_neg n d m e j p q x.1 y.1 hi.1 hi.2 hj.1 hj.2 e3 big hj' hdet
      ⟨bx.1,bx.2.1⟩ ⟨by'.1,by'.2.1⟩ (congrArg Prod.fst hh) hp hq (by linarith only [id₁]) (by linarith only [id₂])

end FLatticePaper.Tiles.MixedStringGrade
