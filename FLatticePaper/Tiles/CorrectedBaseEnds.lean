import FLatticePaper.Tiles.CorrectedBaseBands
import FLatticePaper.Tiles.CorrectedDomainLattice

/-! The exceptional strips and the four missing sites of the pure head columns in integral coordinates. -/

namespace FLatticePaper.Tiles.CorrectedBaseEnds

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open CorrectedCellsBands CorrectedColumnRuns CorrectedDomainLattice

/-- Double the first coordinate of the Farey chart so that sites of both checkerboard parities
can be compared in one integer lattice. -/
def coords (p : Fraction) (z : Site) : Site :=
  ((p.den+p.num)*z.1+(p.den-p.num)*z.2,p.den*z.2-p.num*z.1)

theorem coords_add (p : Fraction) (z t : Site) : coords p (z+t)=coords p z+coords p t := by
  ext <;> dsimp [coords] <;> ring

theorem coords_chart (p : Fraction) (z : Site) (h : (z.1+z.2)%2=0) :
    coords p z = (2*(chart p z).1,(chart p z).2) :=
  Prod.ext (twice_first p z h).symm rfl

theorem coords_injective (p : Fraction) (hp : scale p ≠ 0) : Function.Injective (coords p) := by
  intro z t h
  have a := congrArg Prod.fst h
  have b := congrArg Prod.snd h
  change (p.den+p.num)*z.1+(p.den-p.num)*z.2=(p.den+p.num)*t.1+(p.den-p.num)*t.2 at a
  change p.den*z.2-p.num*z.1=p.den*t.2-p.num*t.1 at b
  apply Prod.ext
  · apply (mul_right_inj' hp).mp
    unfold scale; linarith only [congrArg (· * p.den) a,congrArg (· * (p.den-p.num)) b]
  · apply (mul_right_inj' hp).mp
    unfold scale; linarith only [congrArg (· * p.num) a,congrArg (· * (p.den+p.num)) b]

/-- In the pure-two frame the strip is a rectangle of width one fewer than the odd
denominator and height precisely the number of copies times one period. -/
def strip (d : ℤ) (k : ℕ) (z : Site) : Prop :=
  let c := coords ⟨d-1,d⟩ z
  0 ≤ c.1 ∧ c.1 ≤ 2*d-2 ∧ 0 ≤ c.2 ∧ c.2 < ((k : ℤ)+1)*(2*d^2-1)

private theorem strip_iff (d : ℤ) (hd : 2 ≤ d) (k : ℕ) (a b : ℤ) :
    (-(k : ℤ) ≤ a ∧ a ≤ 0 ∧ 0 ≤ b+(2*d-1)*a ∧ b+(2*d-1)*a < 2*d-1) ↔ strip d k (a,b) := by
  let M := 2*d^2-1
  let t := b+(2*d-1)*a
  let y := d*b-(d-1)*a
  have hm : 0 < M := by dsimp [M]; nlinarith [sq_nonneg (d-2)]
  have key : y=(-a)*M+d*t := by dsimp [M,t,y]; ring
  have tBounds (l : 0≤t) (u : t≤2*d-2) : 0 ≤ d*t ∧ d*t < M := by
    refine ⟨mul_nonneg (by omega) l,?_⟩
    have h := mul_le_mul_of_nonneg_left u (show 0≤d by omega)
    dsimp [M]; linarith
  have c : coords ⟨d-1,d⟩ (a,b) = (t,y) := by
    apply Prod.ext
    · dsimp [coords,t]; ring
    · rfl
  unfold strip
  rw [c]
  change (-(k : ℤ)≤a ∧ a≤0 ∧ 0≤t ∧ t<2*d-1) ↔ 0≤t ∧ t≤2*d-2 ∧ 0≤y ∧ y<((k : ℤ)+1)*M
  constructor
  · rintro ⟨ka,az,tl,tu⟩
    obtain ⟨l,u⟩ := tBounds tl (by omega)
    have h := mul_le_mul_of_nonneg_right (show -a≤(k:ℤ) by omega) hm.le
    have n := mul_nonneg (show 0≤ -a by omega) hm.le
    exact ⟨tl,by omega,by rw [key]; omega,by rw [key,add_mul,one_mul]; omega⟩
  · rintro ⟨tl,tu,lo,hi⟩
    obtain ⟨l,u⟩ := tBounds tl tu
    have ka : -(k : ℤ)≤a := by
      by_contra! hh
      have m := mul_le_mul_of_nonneg_right (show (k:ℤ)+1≤ -a by omega) hm.le
      omega
    have az : a≤0 := by
      by_contra! hh
      have m := mul_le_mul_of_nonneg_right (show -a≤ -1 by omega) hm.le
      rw [neg_one_mul] at m
      omega
    exact ⟨ka,az,tl,by omega⟩

/-- The two extra vertical strings in the actual base register extend through the
uppermost copy, with a strict upper endpoint in the second chart coordinate. -/
theorem two_column (j k : ℕ) (s : Digit) (hs : s=.one ∨ s=.two) (z : Site) :
    let u := List.replicate j Digit.two
    let d := (j : ℤ)+2
    let D := 2*d-1
    z ∈ column (LCorrecRecursion.headE (u++[s])) (-1,D) k ↔
      (Band (D,D-2) (-1,D) 0 k z ∨ Band (D,D-2) (-1,D) 0 k (z-(0,D-1))) ∨
      strip d k (z-(-1,D)) ∨ strip d k (z-(D+1,D-3)) := by
  intro u d D
  have size : 2*(j:ℤ)+3=D := by dsimp [d,D]; omega
  have H := CorrectedBaseBands.two_column j k s hs z
  dsimp only at H
  rw [size] at H
  rw [H]
  apply or_congr_right
  apply or_congr
  · change _ ↔ strip d k (z.1-(-1),z.2-D)
    simpa only [sub_neg_eq_add] using strip_iff d (by dsimp [d]; omega) k (z.1+1) (z.2-D)
  · exact strip_iff d (by dsimp [d]; omega) k (z.1-(D+1)) (z.2-(D-3))

/-- The four punctures of the pure-three column can be tested in the same integral coordinates
as its two bands, including the last translate of the top pair. -/
theorem three_column (j k : ℕ) (s : Digit) (hs : s=.one ∨ s=.two) (z : Site) :
    let u := List.replicate (j+1) Digit.three
    let d := 2*((j+1 : ℕ):ℤ)+2
    let p : Fraction := ⟨1,d⟩
    let b : Site := (1-d,d+1)
    let v := (k:ℤ) • b
    let C := coords p
    z ∈ column (LCorrecRecursion.headE (u++[s])) b k ↔
      (Band (d+1,1) b 0 k z ∨ Band (d+1,1) b 0 k (z-(d-2,2))) ∧
      C z≠C (d+1,0) ∧ C z≠C (d+1,1) ∧ C z≠C ((0,d+2)+v) ∧ C z≠C ((0,d+3)+v) := by
  intro u d p b v C
  have hd : 4≤d := by dsimp [d]; omega
  have hm : 0<scale p := by dsimp [scale,p]; nlinarith [sq_nonneg d]
  have inj := coords_injective p hm.ne'
  have eq (x y : Site) : C x=C y ↔ x=y := inj.eq_iff
  have H := CorrectedBaseBands.three_column j k s hs z
  dsimp only at H
  rw [H]
  apply and_congr Iff.rfl
  change z ∉ ({(d+1,0),(d+1,1)} : Standard.Tile) ∪ Standard.shift ({(0,d+2),(0,d+3)} : Standard.Tile) v ↔
    C z≠C (d+1,0) ∧ C z≠C (d+1,1) ∧ C z≠C ((0,d+2)+v) ∧ C z≠C ((0,d+3)+v)
  have ne (x y : Site) : C x≠C y ↔ x≠y := not_congr (eq x y)
  rw [ne,ne,ne,ne]
  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Standard.mem_shift,
    sub_eq_iff_eq_add,not_or,and_assoc]

end FLatticePaper.Tiles.CorrectedBaseEnds
