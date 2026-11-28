import FLatticePaper.Tiles.CorrectedDomainLattice

/-! The possible lattice sites in the small corner boxes of the pure-two correction. -/

namespace FLatticePaper.Tiles.CorrectedPureCorners

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles CorrectedDomainLattice

/-- The even physical lattice in the pure-two chart has coordinates
`(d*a+b, 2*d*b+a)` with integral coefficients. -/
theorem basis (d : ℤ) (z : Site) (h : (z.1+z.2)%2=0) :
    ∃ b : ℤ, chart ⟨d-1,d⟩ z=(d*z.1+b,2*d*b+z.1) := by
  let b := (z.2-z.1)/2
  have eq : z.2=z.1+2*b := by dsimp [b]; omega
  have first := twice_first ⟨d-1,d⟩ z h
  change 2*(chart ⟨d-1,d⟩ z).1=(d+(d-1))*z.1+(d-(d-1))*z.2 at first
  refine ⟨b,Prod.ext ?_ ?_⟩
  · change (chart ⟨d-1,d⟩ z).1=d*z.1+b
    nlinarith only [first,eq]
  · change d*z.2-(d-1)*z.1=2*d*b+z.1
    linear_combination d*eq

/-- Every physical lattice point within three denominators of a corner is one of
the forty-five offsets given by the two short coefficient intervals. -/
theorem bounded (d : ℤ) (hd : 2≤d) (z : Site) (h : (z.1+z.2)%2=0)
    (hx : |(chart ⟨d-1,d⟩ z).1| ≤ 3*d) (hy : |(chart ⟨d-1,d⟩ z).2| ≤ 3*d) :
    ∃ a b : ℤ, -4≤a ∧ a≤4 ∧ -2≤b ∧ b≤2 ∧ chart ⟨d-1,d⟩ z=(d*a+b,2*d*b+a) := by
  obtain ⟨b,E⟩ := basis d z h
  have broad := (corner_bounds ⟨d-1,d⟩ ⟨by dsimp; omega,by dsimp; omega,by dsimp; omega⟩ z h hx hy).1
  rw [E] at hx hy
  obtain ⟨xl,xu⟩ := abs_le.mp hx
  obtain ⟨yl,yu⟩ := abs_le.mp hy
  change -(3*d)≤d*z.1+b at xl
  change d*z.1+b≤3*d at xu
  change -(3*d)≤2*d*b+z.1 at yl
  change 2*d*b+z.1≤3*d at yu
  obtain ⟨al,au⟩ := abs_le.mp broad
  have pos : 0≤2*d := by omega
  have inner : -2≤b ∧ b≤2 := by
    by_cases hg : 4≤d
    · constructor
      · by_contra! no
        have le := mul_le_mul_of_nonneg_left (show b≤ -3 by omega) pos
        linarith
      · by_contra! no
        have le := mul_le_mul_of_nonneg_left (show 3≤b by omega) pos
        linarith
    · rcases (show d=2 ∨ d=3 by omega) with rfl|rfl <;> omega
  refine ⟨z.1,b,?_,?_,inner.1,inner.2,E⟩
  · by_contra! no
    have le := mul_le_mul_of_nonneg_left (show z.1≤ -5 by omega) (show 0≤d by omega)
    linarith [inner.2]
  · by_contra! no
    have le := mul_le_mul_of_nonneg_left (show 5≤z.1 by omega) (show 0≤d by omega)
    linarith [inner.1]

end FLatticePaper.Tiles.CorrectedPureCorners
