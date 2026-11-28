import FLatticePaper.Tiles.SiteScope
import FLatticePaper.Construction.OffsetTables

/-! Integer coordinates of the even checkerboard in the frame of a Farey register.
The two divisibility relations exclude the open intervals between successive periods. -/

namespace FLatticePaper.Tiles.CorrectedDomainLattice

open FLatticePaper.Farey FLatticePaper.Construction

/-- The coordinates relative to the odd periods, with both diagonal basis vectors sent to the same scale. -/
def chart (p : Fraction) (z : Site) : Site :=
  (((p.den+p.num)*z.1+(p.den-p.num)*z.2)/2, p.den*z.2-p.num*z.1)

/-- The common scale of the two odd periods. -/
def scale (p : Fraction) : ℤ := p.den^2+2*p.den*p.num-p.num^2

private theorem even_prod (a b x y : ℤ) (ha : (a+b)%2=0) (hx : (x+y)%2=0) :
    (a*x-b*y)%2=0 := by
  have h₁ : a%2 = b%2 := by omega
  have h₂ : x%2 = y%2 := by omega
  rw [Int.sub_emod,Int.mul_emod,Int.mul_emod b,h₁,h₂,sub_self]
  decide

theorem twice_first (p : Fraction) (z : Site) (hz : (z.1+z.2)%2=0) :
    2*(chart p z).1 = (p.den+p.num)*z.1+(p.den-p.num)*z.2 := by
  have h := even_prod (p.den+p.num) (p.num-p.den) z.1 z.2 (by omega) hz
  rw [show (p.den+p.num)*z.1-(p.num-p.den)*z.2 = (p.den+p.num)*z.1+(p.den-p.num)*z.2 by ring] at h
  dsimp [chart]
  omega

/-- The four period images, at any Farey frame with an even second register. -/
theorem periods (p q : Fraction) (hq : (q.num+q.den)%2=0) :
    let e := -p.det q
    let t := (chart p (texV1Even q)).1
    chart p (texV1Odd p) = (scale p,0) ∧ chart p (texV2 p) = (0,scale p) ∧
      chart p (texV1Even q) = (t,e) ∧ chart p (texV2 q) = (e,2*t) := by
  dsimp only
  have ht := twice_first p (texV1Even q) (by simp only [texV1Even]; omega)
  have hh := twice_first p (texV1Odd p) (by simp only [texV1Odd]; omega)
  have hv := twice_first p (texV2 p) (by simp only [texV2]; omega)
  have hqv := twice_first p (texV2 q) (by simp only [texV2]; omega)
  refine ⟨Prod.ext ?_ ?_,Prod.ext ?_ ?_,Prod.ext rfl ?_,Prod.ext ?_ ?_⟩
  all_goals simp only [texV1Even,texV1Odd,texV2,scale,chart,Fraction.det] at *
  all_goals linarith only [ht,hh,hv,hqv]

/-- Every even site in the register frame lies on the required integer levels in both directions. -/
theorem chart_multiples (p q : Fraction) (hzq : (q.num+q.den)%2=0) (z : Site)
    (hz : (z.1+z.2)%2=0) (hd : p.det q = 1 ∨ p.det q = -1) :
    let t := (chart p (texV1Even q)).1
    let e := -p.det q
    scale p ∣ (chart p z).1-e*(chart p z).2*t ∧
      scale p ∣ (chart p z).2-2*e*(chart p z).1*t := by
  obtain ⟨n,d⟩ := p
  obtain ⟨g,f⟩ := q
  obtain ⟨x,y⟩ := z
  dsimp only [Fraction.det] at hd
  let X := (chart ⟨n,d⟩ (x,y)).1
  let T := (chart ⟨n,d⟩ (f,g)).1
  let M := scale ⟨n,d⟩
  let Y := d*y-n*x
  have hx : 2*X=(d+n)*x+(d-n)*y := twice_first _ _ hz
  have ht : 2*T=(d+n)*f+(d-n)*g := twice_first _ _ (by change (f+g)%2=0; change (g+f)%2=0 at hzq; omega)
  have hp : (g*x-f*y)%2=0 := even_prod _ _ _ _ hzq hz
  have hv : ((g-f)*y-(g+f)*x)%2=0 := even_prod _ _ _ _ (by omega) (by change (x+y)%2=0 at hz; omega)
  let k := (g*x-f*y)/2
  let l := ((g-f)*y-(g+f)*x)/2
  have hk : 2*k=g*x-f*y := by dsimp [k]; omega
  have hl : 2*l=(g-f)*y-(g+f)*x := by dsimp [l]; omega
  have h₁ : (2*k)*M+Y*(2*T)=(d*g-n*f)*(2*X) := by rw [hk,hx,ht]; dsimp [M,scale,Y]; ring
  have h₂ : (2*l)*M+(2*X)*(2*T)=2*(d*g-n*f)*Y := by rw [hl,hx,ht]; dsimp [M,scale,Y]; ring
  change M ∣ X-(-(n*f-g*d))*Y*T ∧ M ∣ Y-2*(-(n*f-g*d))*X*T
  rcases hd with h|h
  · have he : d*g-n*f = -1 := by linarith
    rw [he] at h₁ h₂
    rw [h]
    exact ⟨⟨-k,by linarith only [h₁]⟩,⟨-l,by linarith only [h₂]⟩⟩
  · have he : d*g-n*f = 1 := by linarith
    rw [he] at h₁ h₂
    rw [h]
    exact ⟨⟨k,by linarith only [h₁]⟩,⟨l,by linarith only [h₂]⟩⟩

private theorem outside_gap (M S t j k : ℤ) (hm : 0 ≤ M) (hs : M ∣ S) (ht : M ∣ t) :
    ¬ (k*S+j*M < t ∧ t < k*S+(j+1)*M) := by
  obtain ⟨n,rfl⟩ := hs
  obtain ⟨r,rfl⟩ := ht
  rcases le_or_gt r (k*n+j) with h|h
  · have b := mul_le_mul_of_nonneg_left h hm
    rintro ⟨lo,_⟩; linarith only [lo,b]
  · have b := mul_le_mul_of_nonneg_left (show k*n+j+1 ≤ r by omega) hm
    rintro ⟨_,hi⟩; linarith only [hi,b]

/-- The two lattice interval exclusions in the coordinates of an actual word, including translated runs. -/
theorem word_exclusions (w : Word) (z : Site) (hz : (z.1+z.2)%2=0) (N : ℕ) (j k : ℤ) :
    let p := (parentsAt w).odd
    let q := (parentsAt w).even
    let S := (N : ℤ)*scale p
    let X := (chart p z).1
    let Y := (chart p z).2
    let T := (chart p (texV1Even q)).1
    let e := -p.det q
    let lo := k*S+j*scale p
    let hi := k*S+(j+1)*scale p
    ¬ (lo<X-e*Y*T ∧ X-e*Y*T<hi) ∧ ¬ (lo<Y-2*e*X*T ∧ Y-2*e*X*T<hi) := by
  let p := (parentsAt w).odd
  let q := (parentsAt w).even
  have vr := parentsAt_valid w
  obtain ⟨h₁,h₂⟩ := chart_multiples p q vr.even_parity z hz vr.unit_det
  have hi := vr.odd_bounds
  change 0 < p.den ∧ 0 ≤ p.num ∧ p.num ≤ p.den at hi
  have hm : 0 ≤ scale p := by
    unfold scale
    nlinarith [mul_nonneg (show 0 ≤ p.den-p.num by omega) (show 0 ≤ p.den+p.num by omega),
      mul_nonneg (show 0 ≤ p.den by omega) hi.2.1]
  have hs : scale p ∣ (N : ℤ)*scale p := dvd_mul_left _ _
  exact ⟨outside_gap _ _ _ j k hm hs h₁,outside_gap _ _ _ j k hm hs h₂⟩


/-- Addition in the even checkerboard gives literal addition of chart coordinates. -/
theorem chart_add (p : Fraction) (z v : Site) (hz : (z.1+z.2)%2=0) (hv : (v.1+v.2)%2=0) :
    chart p (z+v) = chart p z + chart p v := by
  have h := twice_first p (z+v) (by simp only [Prod.fst_add,Prod.snd_add]; omega)
  apply Prod.ext
  · simp only [Prod.fst_add,Prod.snd_add] at h ⊢
    linarith only [h,twice_first p z hz,twice_first p v hv]
  · dsimp [chart]; ring

theorem chart_smul (p : Fraction) (i : ℤ) (z : Site) (hz : (z.1+z.2)%2=0) :
    chart p (i • z) = i • chart p z := by
  have hi : ((i • z).1+(i • z).2)%2=0 := by
    change (i*z.1+i*z.2)%2=0
    rw [←mul_add,Int.mul_emod,hz]; simp
  have h := twice_first p (i • z) hi
  apply Prod.ext
  · change 2*(chart p (i • z)).1 = (p.den+p.num)*(i*z.1)+(p.den-p.num)*(i*z.2) at h
    change (chart p (i • z)).1 = i*(chart p z).1
    linarith only [h,congrArg (i*·) (twice_first p z hz)]
  · change p.den*(i*z.2)-p.num*(i*z.1) = i*(p.den*z.2-p.num*z.1)
    ring

/-- The determinant of two chart vectors is the physical determinant times half the register scale. -/
theorem chart_det (p : Fraction) (a z : Site) (ha : (a.1+a.2)%2=0) (hz : (z.1+z.2)%2=0) :
    2*((chart p a).1*(chart p z).2-(chart p a).2*(chart p z).1) =
      scale p*(a.1*z.2-a.2*z.1) := by
  change 2*((chart p a).1*(p.den*z.2-p.num*z.1)-(p.den*a.2-p.num*a.1)*(chart p z).1) = _
  unfold scale
  linear_combination (p.den*z.2-p.num*z.1)*(twice_first p a ha) -
    (p.den*a.2-p.num*a.1)*(twice_first p z hz)

/-- Recover both physical coordinates by the integer adjugate, with no choice of a lattice representative. -/
theorem reconstruct (p : Fraction) (z : Site) (hz : (z.1+z.2)%2=0) :
    scale p • z = (chart p z).1 • texV1Odd p + (chart p z).2 • texV2 p := by
  apply Prod.ext
  · change scale p*z.1 = (chart p z).1*(2*p.den)+(p.den*z.2-p.num*z.1)*(p.num-p.den)
    unfold scale
    linear_combination -p.den*(twice_first p z hz)
  · change scale p*z.2 = (chart p z).1*(2*p.num)+(p.den*z.2-p.num*z.1)*(p.num+p.den)
    unfold scale
    linear_combination -p.num*(twice_first p z hz)

private theorem two_terms (u v c d m : ℤ) (hu : |u| ≤ m) (hv : |v| ≤ m) :
    |u*c+v*d| ≤ m*(|c|+|d|) := by
  calc
    _ ≤ |u*c|+|v*d| := abs_add_le _ _
    _ ≤ m*|c|+m*|d| := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right hu (abs_nonneg _)) (mul_le_mul_of_nonneg_right hv (abs_nonneg _))
    _ = _ := by ring

/-- Every even site in the small box around a projected corner is among the finitely enumerated physical offsets. -/
theorem corner_bounds (p : Fraction) (hp : p.InUnitInterval) (z : Site) (hz : (z.1+z.2)%2=0)
    (hx : |(chart p z).1| ≤ 3*p.den) (hy : |(chart p z).2| ≤ 3*p.den) :
    |z.1| ≤ 9 ∧ |z.2| ≤ 12 := by
  obtain ⟨hd,hn,hnd⟩ := hp
  have hM : p.den^2 ≤ scale p := by
    unfold scale
    nlinarith [mul_nonneg hn (show 0 ≤ 2*p.den-p.num by omega)]
  have pos : 0 < scale p := lt_of_lt_of_le (sq_pos_of_pos hd) hM
  have h := reconstruct p z hz
  have x := congrArg Prod.fst h
  have y := congrArg Prod.snd h
  change scale p*z.1 = (chart p z).1*(2*p.den)+(chart p z).2*(p.num-p.den) at x
  change scale p*z.2 = (chart p z).1*(2*p.num)+(chart p z).2*(p.num+p.den) at y
  have bx := two_terms _ _ (2*p.den) (p.num-p.den) _ hx hy
  have by' := two_terms _ _ (2*p.num) (p.num+p.den) _ hx hy
  rw [←x,abs_mul,abs_of_pos pos,abs_of_nonneg (show 0 ≤ 2*p.den by omega),abs_of_nonpos (by omega : p.num-p.den ≤ 0)] at bx
  rw [←y,abs_mul,abs_of_pos pos,abs_of_nonneg (show 0 ≤ 2*p.num by omega),abs_of_nonneg (show 0 ≤ p.num+p.den by omega)] at by'
  constructor
  · apply le_of_mul_le_mul_left (a := scale p) _ pos
    nlinarith [mul_nonneg hd.le hn]
  · apply le_of_mul_le_mul_left (a := scale p) _ pos
    nlinarith [mul_nonneg hd.le (show 0 ≤ p.den-p.num by omega)]

end FLatticePaper.Tiles.CorrectedDomainLattice
