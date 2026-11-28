import FLatticePaper.Tiles.CorrectedColumnRuns
import FLatticePaper.Tiles.SubOddCopy
import FLatticePaper.Tiles.SubEvenCopy

/-! The four oriented lines of a column, including the integer sites on its two ends. -/

namespace FLatticePaper.Tiles.CorrectedCellsBands

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard SiteInduction CorrectedColumnRuns

abbrev cross (a b : Site) : ℤ := a.1*b.2-a.2*b.1
abbrev oddSite (z : Site) := decide ((z.1+z.2)%2=1)
def probe (a : Site) (odd : Bool) : Site :=
  if odd then (0,1) else if 3*a.2 ≤ a.1 then (1,1) else (-2,0)
abbrev transverse (b : Site) : Site := (b.2,-b.1)

/-- Lower and upper allowances for the horizontal determinant; the half turn has centre
`a+b+(1,-1)` in doubled coordinates. -/
def allowances (a b : Site) (o : Bool) : ℤ × ℤ × ℤ × ℤ :=
  let r := probe a o
  let t := probe (transverse b) (!o)
  (-(cross a r), cross a (b+((1,-1):Site)+r), cross (((1,0):Site)+mulI t) b,
    cross (a-((0,1):Site)-mulI t) b)

/-- The four determinant tests after lengthening the horizontal side by `h` copies of `a`
and the vertical side by `v` copies of `b`. -/
def Band (a b : Site) (h v : ℕ) (z : Site) : Prop :=
  let m := cross a b
  let t := allowances a b (oddSite z)
  t.1 ≤ cross a z ∧ cross a z ≤ t.2.1+(v : ℤ)*m ∧
    t.2.2.1 ≤ cross z b ∧ cross z b ≤ t.2.2.2+(h : ℤ)*m

set_option maxHeartbeats 400000 in
private theorem standard_test (f : Fraction) (z : Site) : InH f z ↔ Band (perU f) (perV f) 0 0 z := by
  obtain ⟨n,d⟩ := f
  obtain ⟨x,y⟩ := z
  have par : (x+y)%2=0 ∨ (x+y)%2=1 := by omega
  rcases par with he|he <;> by_cases hf : (n+d)%2=1
  all_goals simp [InH,Band,allowances,oddSite,perU,perV,SiteInduction.muOf,hf,he,
    SiteInduction.tCo,SiteInduction.sCo,SiteInduction.aOf,SiteInduction.lOf,SiteInduction.tOf,
    probe,cross,mulI,min_def]
  all_goals split_ifs <;> dsimp at * <;> ring_nf at * <;> omega

/-- The odd standard tile in the four tests, at an arbitrary word and physical site. -/
theorem odd_band (w : Word) (z : Site) :
    z ∈ oddTile w ↔ Band (texV1Odd (curO w)) (texV2 (curO w)) 0 0 z := by
  rw [SubOddCopy.mem_oddTile_iff,standard_test]
  have h : ((curO w).num+(curO w).den)%2=1 := SiteHullOdd.curO_odd w
  simp [perU,SiteInduction.muOf,h,texV1Odd,perV,texV2,add_comm]

/-- The even standard tile in the same four tests. -/
theorem even_band (w : Word) (z : Site) :
    z ∈ evenTile w ↔ Band (texV1Even (curE w)) (texV2 (curE w)) 0 0 z := by
  rw [SubEvenCopy.mem_evenTile_iff,standard_test]
  have h : ((curE w).num+(curE w).den)%2=0 := SiteHullEven.curE_even w
  simp [perU,SiteInduction.muOf,h,texV1Even,perV,texV2,add_comm]

private theorem interval (k : ℕ) (m lo hi y : ℤ) (hm : 0 ≤ m) (hw : lo+m ≤ hi+1) :
    (∃ j : ℕ, j ≤ k ∧ lo ≤ y-(j : ℤ)*m ∧ y-(j : ℤ)*m ≤ hi) ↔ lo ≤ y ∧ y ≤ hi+(k : ℤ)*m := by
  constructor
  · rintro ⟨j,jk,yl,yh⟩
    have h₁ : 0 ≤ (j : ℤ)*m := mul_nonneg (by exact_mod_cast Nat.zero_le j) hm
    have h₂ : (j : ℤ)*m ≤ (k : ℤ)*m := mul_le_mul_of_nonneg_right (by exact_mod_cast jk) hm
    omega
  · induction k with
    | zero => rintro ⟨yl,yr⟩; exact ⟨0,by omega,by simpa using yl,by simpa using yr⟩
    | succ k ih =>
      rintro ⟨yl,yh⟩
      by_cases h : y ≤ hi+(k : ℤ)*m
      · obtain ⟨j,jk,a,b⟩ := ih ⟨yl,h⟩
        exact ⟨j,by omega,a,b⟩
      · refine ⟨k+1,le_rfl,?_,?_⟩ <;> push_cast at * <;> rw [add_mul,one_mul] at * <;> omega

private theorem parity_sub (z b : Site) (j : ℤ) (hb : (b.1+b.2)%2=0) :
    oddSite (z-j • b) = oddSite z := by
  have e : (z-j • b).1+(z-j • b).2 = (z.1+z.2)-j*(b.1+b.2) := by
    change z.1-j*b.1+(z.2-j*b.2) = _; ring
  simp only [oddSite,e,Int.sub_emod,Int.mul_emod,hb,mul_zero,Int.zero_emod,sub_zero,Int.emod_emod]

private theorem vertical_width (a b : Site) (ha : a.2 ≤ a.1) (o : Bool) :
    (allowances a b o).1 + cross a b ≤ (allowances a b o).2.1 + 1 := by
  obtain ⟨x,y⟩ := a
  cases o <;> by_cases h : 3*y ≤ x <;> simp [allowances,probe,cross,h] <;> linarith

private theorem horizontal_width (a b : Site) (hb : -b.1 ≤ b.2) (o : Bool) :
    (allowances a b o).2.2.1 + cross a b ≤ (allowances a b o).2.2.2 + 1 := by
  obtain ⟨x,y⟩ := b
  cases o <;> by_cases h : -(3*x) ≤ y <;> simp [allowances,probe,cross,mulI,h] <;> linarith

/-- Stacking tiles with the given four faces extends just the upper horizontal determinant bound.
The interval overlap condition is tested separately at each physical parity. -/
theorem vertical_iff (a b : Site) (k : ℕ) (hb : (b.1+b.2)%2=0) (hm : 0 ≤ cross a b)
    (ha : a.2 ≤ a.1) (z : Site) :
    (∃ j ≤ k, Band a b 0 0 (z-(j : ℤ) • b)) ↔ Band a b 0 k z := by
  have h₁ (j : ℤ) : cross a (z-j • b) = cross a z-j*cross a b := by
    change a.1*(z.2-j*b.2)-a.2*(z.1-j*b.1) = _; dsimp [cross]; ring
  have h₂ (j : ℤ) : cross (z-j • b) b = cross z b := by
    change (z.1-j*b.1)*b.2-(z.2-j*b.2)*b.1 = _; dsimp [cross];ring
  simp only [Band,h₁,h₂,parity_sub _ _ _ hb,Nat.cast_zero,zero_mul,add_zero]
  have h := interval k (cross a b) _ _ (cross a z) hm (vertical_width a b ha (oddSite z))
  constructor
  · rintro ⟨j,jk,yl,yh,xl,xh⟩
    obtain ⟨l,r⟩ := h.mp ⟨j,jk,yl,yh⟩
    exact ⟨l,r,xl,xh⟩
  · rintro ⟨yl,yh,xl,xh⟩
    obtain ⟨j,jk,l,r⟩ := h.mpr ⟨yl,yh⟩
    exact ⟨j,jk,l,r,xl,xh⟩

/-- The horizontal stem row extends just the upper vertical determinant bound. -/
theorem horizontal_iff (a b : Site) (k : ℕ) (ha : (a.1+a.2)%2=0) (hm : 0 ≤ cross a b)
    (hb : -b.1 ≤ b.2) (z : Site) :
    (∃ j ≤ k, Band a b 0 0 (z-(j : ℤ) • a)) ↔ Band a b k 0 z := by
  have h₁ (j : ℤ) : cross a (z-j • a) = cross a z := by
    change a.1*(z.2-j*a.2)-a.2*(z.1-j*a.1) = _; dsimp [cross]; ring
  have h₂ (j : ℤ) : cross (z-j • a) b = cross z b - j*cross a b := by
    change (z.1-j*a.1)*b.2-(z.2-j*a.2)*b.1 = _; dsimp [cross];ring
  simp only [Band,h₁,h₂,parity_sub _ _ _ ha,Nat.cast_zero,zero_mul,add_zero]
  have h := interval k (cross a b) _ _ (cross z b) hm (horizontal_width a b hb (oddSite z))
  constructor
  · rintro ⟨j,jk,yl,yh,xl,xh⟩
    obtain ⟨l,r⟩ := h.mp ⟨j,jk,xl,xh⟩
    exact ⟨yl,yh,l,r⟩
  · rintro ⟨yl,yh,xl,xh⟩
    obtain ⟨j,jk,l,r⟩ := h.mpr ⟨xl,xh⟩
    exact ⟨j,jk,yl,yh,l,r⟩

/-- Membership in an actual stack with a known polygonal head. -/
theorem vertical_column (T : Tile) (a b : Site) (k : ℕ) (hb : (b.1+b.2)%2=0)
    (hm : 0 ≤ cross a b) (ha : a.2 ≤ a.1) (hT : ∀ z, z ∈ T ↔ Band a b 0 0 z) (z : Site) :
    z ∈ column T b k ↔ Band a b 0 k z := by
  simp only [mem_column,hT,vertical_iff a b k hb hm ha]

/-- Membership in an actual stem row with a known polygonal tile. -/
theorem horizontal_row (T : Tile) (a b : Site) (k : ℕ) (ha : (a.1+a.2)%2=0)
    (hm : 0 ≤ cross a b) (hb : -b.1 ≤ b.2) (hT : ∀ z, z ∈ T ↔ Band a b 0 0 z) (z : Site) :
    z ∈ column T a k ↔ Band a b k 0 z := by
  simp only [mem_column,hT,horizontal_iff a b k ha hm hb]


/-- Rotate a lengthened polygon clockwise in its corner normalization. A horizontal extension
becomes a vertical extension, and the physical parity changes at the new corner. -/
theorem clockwise (a b z : Site) (h v : ℕ) (ha : (a.1+a.2)%2=0) :
    Band a b h v z ↔ Band (transverse b) (mulI a) v h
      (transverse z + ((h : ℤ)+1) • mulI a + ((1,0):Site)) := by
  let z' := transverse z + ((h : ℤ)+1) • mulI a + ((1,0):Site)
  have ep : (a.1-a.2)%2=0 := by omega
  have ep' : (((h : ℤ)+1)*(a.1-a.2))%2=0 := by rw [Int.mul_emod,ep]; simp
  have eq : z'.1+z'.2 = z.2-z.1+1+((h : ℤ)+1)*(a.1-a.2) := by
    change z.2+((h : ℤ)+1)*(-a.2)+1+(-z.1+((h : ℤ)+1)*a.1+0) = _
    ring
  have hp : oddSite z' = !oddSite z := by
    unfold oddSite
    rw [eq]
    by_cases hc : (z.1+z.2)%2=1
    · have hc' : ¬ (z.2-z.1+1+((h : ℤ)+1)*(a.1-a.2))%2=1 := by omega
      simp [hc,hc']
    · have hc' : (z.2-z.1+1+((h : ℤ)+1)*(a.1-a.2))%2=1 := by omega
      simp [hc,hc']
  have flip : transverse (mulI a) = a := by ext <;> simp [mulI]
  change Band a b h v z ↔ Band (transverse b) (mulI a) v h z'
  simp only [Band,allowances,hp,Bool.not_not,flip]
  generalize probe a (oddSite z) = r
  generalize probe (transverse b) (!oddSite z) = s
  obtain ⟨ax,ay⟩ := a
  obtain ⟨bx,by'⟩ := b
  obtain ⟨x,y⟩ := z
  simp [z',cross,transverse,mulI,Prod.smul_mk]
  ring_nf
  omega

/-- A head made of two translates of one polygon gives exactly two lengthened polygons,
with the same displacement at every column length. -/
theorem paired_column (T : Tile) (a b δ : Site) (k : ℕ) (hb : (b.1+b.2)%2=0)
    (hm : 0 ≤ cross a b) (ha : a.2 ≤ a.1)
    (hT : ∀ z, z ∈ T ↔ Band a b 0 0 z ∨ Band a b 0 0 (z-δ)) (z : Site) :
    z ∈ column T b k ↔ Band a b 0 k z ∨ Band a b 0 k (z-δ) := by
  have move (i : ℤ) : z-i • b-δ = z-δ-i • b := by abel
  simp only [mem_column,hT,move,←vertical_iff a b k hb hm ha]
  constructor
  · rintro ⟨i,hi,h|h⟩
    exacts [Or.inl ⟨i,hi,h⟩,Or.inr ⟨i,hi,h⟩]
  · rintro (⟨i,hi,h⟩|⟨i,hi,h⟩)
    exacts [⟨i,hi,Or.inl h⟩,⟨i,hi,Or.inr h⟩]

end FLatticePaper.Tiles.CorrectedCellsBands
