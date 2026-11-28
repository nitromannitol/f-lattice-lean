import FLatticePaper.Tiles.CorrectedRegisterLattice
import FLatticePaper.Tiles.BaseTileProps

/-! Arithmetic of the determinant register at either pure predecessor, including the empty word. -/

namespace FLatticePaper.Tiles.CorrectedBaseArithmetic

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open CorrectedRegisterWords CorrectedRegisterDiagram CorrectedDomainLattice

structure Three (r : Register) (one : Bool) : Prop where
  size : 4≤r.d
  even : r.d%2=0
  numerator : r.n=1
  nextDen : r.f=r.d+(if one then 1 else -1)
  nextNum : r.g=1
  turn : 2*r.T=r.M+(if one then 1 else -1)*(r.d+1)
  width : 5*r.d+3≤r.M
  period : r.M≤r.S
  odd : r.M%2=1

structure Two (r : Register) (one : Bool) : Prop where
  size : 2≤r.d
  numerator : r.n=r.d-1
  nextDen : r.f=if one then 2*r.d-1 else 1
  nextNum : r.g=if one then 2*r.d-3 else 1
  turn : r.T=if one then r.M-r.d else r.d
  width : 5*r.d-3≤r.M
  period : r.M≤r.S
  odd : r.M%2=1
  scale : r.M=2*r.d^2-1

private theorem product_bound (N : ℕ) (hn : 0<N) (M : ℤ) (pos : 0≤M) : M≤(N:ℤ)*M := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (show (1:ℤ)≤N by omega) pos

/-- Numerators, denominators, scale and turn of a positive pure-three predecessor. -/
theorem three (j N : ℕ) (hn : 0<N) (one : Bool) (Z : Site) :
    Three (register (parentsAt (List.replicate (j+1) .three)) one N Z) one := by
  let P := parentsAt (List.replicate (j+1) .three)
  let p := P.current .odd
  let q := if one then P.current .even else P.even
  let r := register P one N Z
  have axis : p=⟨1,2*((j:ℤ)+1)+2⟩ := by
    apply Fraction.ext <;> simp [p,P,BaseTileProps.parents_three,Parents.current,Parents.combine]
    all_goals ring
  have sub : q=⟨1,p.den+(if one then 1 else -1)⟩ := by
    cases one <;> apply Fraction.ext <;> simp [q,p,P,BaseTileProps.parents_three,Parents.current,Parents.combine]
    all_goals ring
  have parity : ((texV1Even q).1+(texV1Even q).2)%2=0 := by
    rw [sub,axis]; cases one <;> dsimp [texV1Even]
    all_goals omega
  have tr := twice_first p (texV1Even q) parity
  change 2*r.T=(p.den+p.num)*q.den+(p.den-p.num)*q.num at tr
  have sq : r.M=p.den^2+2*p.den*p.num-p.num^2 := rfl
  have n : r.n=p.num := rfl
  have d : r.d=p.den := rfl
  have f : r.f=q.den := by cases one <;> rfl
  have g : r.g=q.num := by cases one <;> rfl
  change Three r one
  simp only [sub,axis] at tr sq n d f g
  have lower : 4≤r.d := by omega
  have mm : r.M=r.d^2+2*r.d-1 := by rw [d,sq]; ring
  have width : 5*r.d+3≤r.M := by nlinarith [mul_nonneg (show 0≤r.d-4 by omega) (show 0≤r.d+1 by omega)]
  have odd : r.M%2=1 := by
    have sq' : r.M=2*(2*((j:ℤ)+1)^2+6*((j:ℤ)+1)+3)+1 := by rw [sq]; ring
    omega
  refine ⟨lower,by omega,by omega,by omega,by omega,?_,width,product_bound N hn _ (by omega),odd⟩
  cases one <;> simp only [Bool.false_eq_true,if_false,if_true] at tr ⊢ <;> nlinarith only [tr,sq,d]

/-- The pure-two arithmetic is valid from run length zero. -/
theorem two (j N : ℕ) (hn : 0<N) (one : Bool) (Z : Site) :
    let r := register (parentsAt (List.replicate j .two)) one N Z
    Two r one ∧ r.d=(j:ℤ)+2 := by
  let P := parentsAt (List.replicate j .two)
  let p := P.current .odd
  let q := if one then P.current .even else P.even
  intro r
  have axis : p=⟨(j:ℤ)+1,(j:ℤ)+2⟩ := by
    apply Fraction.ext <;> simp [p,P,BaseTileProps.parents_two,Parents.current,Parents.combine]
    all_goals ring
  have sub : q=if one then ⟨2*(j:ℤ)+1,2*(j:ℤ)+3⟩ else ⟨1,1⟩ := by
    cases one <;> apply Fraction.ext <;> simp [q,P,BaseTileProps.parents_two,Parents.current,Parents.combine]
    all_goals ring
  have parity : ((texV1Even q).1+(texV1Even q).2)%2=0 := by
    rw [sub]; cases one <;> dsimp [texV1Even]
    all_goals omega
  have tr := twice_first p (texV1Even q) parity
  change 2*r.T=(p.den+p.num)*q.den+(p.den-p.num)*q.num at tr
  have sq : r.M=p.den^2+2*p.den*p.num-p.num^2 := rfl
  have n : r.n=p.num := rfl
  have d : r.d=p.den := rfl
  have f : r.f=q.den := by cases one <;> rfl
  have g : r.g=q.num := by cases one <;> rfl
  rw [sub,axis] at tr
  rw [axis] at sq n d
  rw [sub] at f g
  simp only at sq n d
  have size : 2≤r.d := by omega
  have mm : r.M=2*r.d^2-1 := by rw [d,sq]; ring
  have width : 5*r.d-3≤r.M := by nlinarith [mul_nonneg (show 0≤2*r.d-1 by omega) (show 0≤r.d-2 by omega)]
  have odd : r.M%2=1 := by omega
  refine ⟨⟨size,by omega,?_,?_,?_,width,product_bound N hn _ (by omega),odd,mm⟩,d⟩
  all_goals cases one <;> simp only [Bool.false_eq_true,if_false,if_true] at tr f g ⊢ <;> nlinarith only [tr,sq,f,g,d]

end FLatticePaper.Tiles.CorrectedBaseArithmetic
