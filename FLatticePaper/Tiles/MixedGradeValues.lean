import FLatticePaper.Tiles.MixedStringGrade
import FLatticePaper.Tiles.SiteBoundaryCover

/-! Heights of a normalized standard odometer in the strip adjoining its horizontal side. -/

namespace FLatticePaper.Tiles.MixedGradeValues

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard StandardClause SiteInduction SiteStrings SiteFwdCover CeilWords SurgicalWeak JointFamily

private theorem cursor_site (w : BinaryWord) (n d x y k : ℤ) (j : ℕ)
    (hc : CursorB (.q :: w) n d) (hd : n < d) (hj : j < (Letter.q :: w).length)
    (hxy : x+y = 2*(j : ℤ) + 2*k)
    (herr : 0 ≤ (d+n)*(y+1-k)-2*n*((j : ℤ)+1) ∧
      (d+n)*(y+1-k)-2*n*((j : ℤ)+1) < d+n) (hk : k = 0 ∨ k = 1) (_hn : 0 < n) :
    (x,y) ∈ stringSites false false (.q :: w) := by
  have hv := qPrefix_eq_of_err (.q :: w) n d hc (by omega : 0 < d+n) (j+1) hj (y+1-k)
  push_cast at hv
  apply mem_of_cursor w n d hc hd j hj (k,k) x y (hv herr.1 herr.2)
  · rcases hk with rfl | rfl <;> norm_num
  · dsimp; omega

private theorem strip (o : PartialOdometer) (w : BinaryWord) (f : Fraction) (μ β : ℤ)
    (hn : 0 < f.num) (hd : f.num < f.den) (hh : w.head? = some .q)
    (hc : CursorB w f.num f.den) (len : 2*(w.length : ℤ) = μ*(f.den+f.num))
    (hr : RespectsTiles .horizontal false (hStringAt w 0) o.val) (hβ : FirstTileNormal o 0 β)
    (z : Site) (hH : InH f z) (hbox : z.1 ≤ μ*f.den ∧ 0 ≤ z.2)
    (hg : -f.num < tCo f z) : o.val z = β := by
  obtain ⟨x,y⟩ := z
  apply MixedStringGrade.forward_value o w f.num f.den β hn hd hh hc hr hβ _ _ hg
  obtain ⟨w',rfl⟩ : ∃ w', w = .q :: w' := by
    cases w with
    | nil => simp at hh
    | cons a l => simp only [List.head?_cons, Option.some.injEq] at hh; exact ⟨l, by rw [hh]⟩
  let n := f.num
  let d := f.den
  let t := n*x-d*y
  change -n < t at hg
  change x ≤ μ*d ∧ 0 ≤ y at hbox
  change 2*((Letter.q :: w').length : ℤ) = μ*(d+n) at len
  have L : 0 < d+n := by change 0 < f.den+f.num; omega
  have hdn : n < d := hd
  have hn0 : 0 < n := hn
  have grade₁ : t = n*(x+y)-(d+n)*y := by dsimp [t]; ring
  have grade₂ : t = (d+n)*(x-μ*d)-d*((x+y)-μ*(d+n)) := by dsimp [t]; ring
  have low : 0 ≤ x+y := by
    by_contra! h
    have hl := mul_le_mul_of_nonneg_left (show x+y ≤ -1 by omega) hn0.le
    nlinarith only [grade₁, hl, mul_nonneg L.le hbox.2, hg]
  have high : x+y ≤ μ*(d+n) := by
    by_contra! h
    have hl := mul_le_mul_of_nonneg_left (show 1 ≤ x+y-μ*(d+n) by omega) (show 0 ≤ d by omega)
    linarith only [grade₂, hl, hg, hdn, mul_nonpos_of_nonneg_of_nonpos L.le (sub_nonpos.mpr hbox.1)]
  let a := aOf f (decide ((x+y)%2=0))
  have hu : t ≤ d+n-a := hH.2.1
  have ab := SiteHullOdd.site_ab f (x,y)
  by_cases odd : (x+y)%2 = 1
  · have hm1 : 1 ≤ x+y := by omega
    have hm2 : x+y ≤ 2*((Letter.q :: w').length : ℤ)-1 := by omega
    exact SiteBoundaryCover.cover_hi_odd n d w' hn hd hc x y t 0 a 0 odd hm1 hm2 rfl hg hu (ab.1 odd).1
  · have even : (x+y)%2 = 0 := by omega
    by_cases hend : x+y = μ*(d+n)
    · have tzero : t = 0 := by
        have id : t = (d+n)*(x-μ*d) := by rw [grade₂,hend,sub_self,mul_zero,sub_zero]
        by_cases h : x = μ*d
        · rw [id,h,sub_self,mul_zero]
        · have := mul_le_mul_of_nonneg_left (show x-μ*d ≤ -1 by omega) L.le
          nlinarith only [this,id,hg,hn0,hdn]
      let j := (Letter.q :: w').length-1
      have hj : j < (Letter.q :: w').length := by dsimp [j]; simp
      have hj' : (j : ℤ)+1 = (Letter.q :: w').length := by dsimp [j]
      apply cursor_site w' n d x y 1 j hc hd hj (by omega) _ (Or.inr rfl) hn
      have he : (d+n)*(y+1-1)-2*n*((j : ℤ)+1) = 0 := by
        have hs : x+y = 2*((j : ℤ)+1) := by omega
        change n*x-d*y = 0 at tzero
        linear_combination -tzero + n*hs
      omega
    · by_cases ht : 0 < t
      · have hm1 : 1 ≤ x+y := by
          by_contra! h
          nlinarith only [h,low,grade₁,ht,mul_nonneg L.le hbox.2,
            mul_nonpos_of_nonneg_of_nonpos hn0.le (show x+y ≤ 0 by omega)]
        exact SiteBoundaryCover.cover_hi_even n d w' hn hd hc x y t 0 a 0 even hm1 (by omega) rfl hg ht hu (ab.2 even).1
      · let j := ((x+y)/2).toNat
        have hj : (j : ℤ) = (x+y)/2 := Int.toNat_of_nonneg (by omega)
        have hj' : j < (Letter.q :: w').length := by omega
        have hs : x+y = 2*(j : ℤ) := by omega
        apply cursor_site w' n d x y 0 j hc hd hj' (by omega) _ (Or.inl rfl) hn
        have he : (d+n)*(y+1-0)-2*n*((j : ℤ)+1) = d-n-t := by
          dsimp [t]; linear_combination n*hs
        omega

/-- A normalized odd parent has its first-tile height throughout the indicated grade strip. -/
theorem odd_value (w : Word) (o : PartialOdometer) (β : ℤ)
    (hr : RespectsTiles .horizontal false (hStringAt (hWordOf w false) 0) o.val)
    (hβ : FirstTileNormal o 0 β) (z : Site) (hz : z ∈ oddTile w)
    (hg : -(fracOdd w).num < tCo (fracOdd w) z) : o.val z = β := by
  have cw := SiteHullOdd.cw_childP w
  have box := ClosedPathExcluded.site_box_odd w z hz
  exact strip o _ _ 2 β (SiteHullOdd.curO_pos_lt w).1 (SiteHullOdd.curO_pos_lt w).2
    (hWordOf_head_last w false).1 (SiteHullOdd.cursorB_of_ceil _ _ _ cw)
    (by rw [cw.1]) hr hβ z ((SubOddCopy.mem_oddTile_iff w z).1 hz) ⟨box.2.1,box.2.2.1⟩ hg

/-- A normalized even parent has its first-tile height throughout the indicated grade strip. -/
theorem even_value (w : Word) (o : PartialOdometer) (β : ℤ)
    (hr : RespectsTiles .horizontal false (hStringAt (hWordOf w true) 0) o.val)
    (hβ : FirstTileNormal o 0 β) (z : Site) (hz : z ∈ evenTile w)
    (hg : -(fracEven w).num < tCo (fracEven w) z) : o.val z = β := by
  have cw := SiteHullEven.cw_childQ_even w
  have ev : ((curE w).num+(curE w).den)%2 = 0 := (parentsAt_valid w).current_even_parity
  have ev' : ((curE w).den+(curE w).num)%2 = 0 := by omega
  have box := ClosedPathExcluded.site_box_even w z hz
  exact strip o _ _ 1 β (SiteHullEven.curE_pos_lt w).1 (SiteHullEven.curE_pos_lt w).2
    (hWordOf_head_last w true).1 (SiteHullEven.cursorB_even _ _ _ cw ev')
    (by rw [cw.1,one_mul]; omega) hr hβ z ((SubEvenCopy.mem_evenTile_iff w z).1 hz)
    ⟨by rw [one_mul]; exact box.2.1,box.2.2.1⟩ hg

end FLatticePaper.Tiles.MixedGradeValues
