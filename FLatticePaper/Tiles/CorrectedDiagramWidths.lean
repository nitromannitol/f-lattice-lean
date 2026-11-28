import FLatticePaper.Tiles.CorrectedRegisterWidths

/-! The primitive sides of all the ordinary, elongated and mixed register polygons have sufficient width. -/

namespace FLatticePaper.Tiles.CorrectedDiagramWidths

open CorrectedRegisterDiagram CorrectedRegisterFaces CorrectedRegisterWidths CorrectedMixedDiagram

private structure Widths (r : Register) : Prop where
  num : 1 ≤ r.n
  den : r.n < r.d
  period : 2*r.d+r.n ≤ r.T
  complement : 2*r.d+r.n ≤ r.M-r.T
  run : r.M ≤ r.S

private theorem of_regular {r : Register} {one : Bool} {sec : Fin 3} (h : Regular r one sec) : Widths r :=
  ⟨h.num,by have := h.den; omega,(register_widths h).1,(register_widths h).2,h.run⟩

local macro "check_widths " name:ident " for " table:ident a:term:max e:term:max b:term:max : command =>
  `(private theorem $name (r : Register) (h : Widths r) (i : Fin 10) :
      Sizes r ($table r $a $e $b i.val) := by
    obtain ⟨n,d,t,c,s⟩ := h
    unfold $table
    fin_cases i <;> constructor <;> norm_num [orientation,Fin.ext_iff,Prod.smul_mk] <;> omega)

check_widths shortOneMin for corrected true (-1) false
check_widths shortOnePlus for corrected true 1 false
check_widths shortTwoMin for corrected false (-1) false
check_widths shortTwoPlus for corrected false 1 false
check_widths longOneMin for corrected true (-1) true
check_widths longOnePlus for corrected true 1 true
check_widths longTwoMin for corrected false (-1) true
check_widths longTwoPlus for corrected false 1 true

check_widths mixedOddOneMin for mixed true (-1) false
check_widths mixedOddOnePlus for mixed true 1 false
check_widths mixedOddTwoMin for mixed false (-1) false
check_widths mixedOddTwoPlus for mixed false 1 false
check_widths mixedEvenOneMin for mixed true (-1) true
check_widths mixedEvenOnePlus for mixed true 1 true
check_widths mixedEvenTwoMin for mixed false (-1) true
check_widths mixedEvenTwoPlus for mixed false 1 true

/-- All the corrected polygons meet the cutoff estimates in either orientation. -/
theorem corrected_fits (r : Register) (one long par : Bool) (prev : ℤ) (sec : Fin 3)
    (h : Regular r one sec) (hp : prev=1 ∨ prev= -1) (i : Fin 10) :
    Fits ((corrected r one prev long i.val).probe r par sec) := by
  refine fits _ _ h.num (of_regular h).den ?_ _ _
  have hw := of_regular h
  rcases hp with rfl | rfl <;> cases one <;> cases long
  all_goals first | exact shortOneMin r hw i | exact shortOnePlus r hw i
                  | exact shortTwoMin r hw i | exact shortTwoPlus r hw i
                  | exact longOneMin r hw i | exact longOnePlus r hw i
                  | exact longTwoMin r hw i | exact longTwoPlus r hw i

/-- Both alternate targets and every source of the mixed diagram meet the same estimates. -/
theorem mixed_fits (r : Register) (one even par : Bool) (prev : ℤ) (sec : Fin 3)
    (h : Regular r one sec) (hp : prev=1 ∨ prev= -1) (i : Fin 10) :
    Fits ((mixed r one prev even i.val).probe r par sec) := by
  refine fits _ _ h.num (of_regular h).den ?_ _ _
  have hw := of_regular h
  rcases hp with rfl | rfl <;> cases one <;> cases even
  all_goals first | exact mixedOddOneMin r hw i | exact mixedOddOnePlus r hw i
                  | exact mixedOddTwoMin r hw i | exact mixedOddTwoPlus r hw i
                  | exact mixedEvenOneMin r hw i | exact mixedEvenOnePlus r hw i
                  | exact mixedEvenTwoMin r hw i | exact mixedEvenTwoPlus r hw i

end FLatticePaper.Tiles.CorrectedDiagramWidths
