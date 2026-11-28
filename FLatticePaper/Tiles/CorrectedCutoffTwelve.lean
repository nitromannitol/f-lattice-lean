import FLatticePaper.Tiles.CorrectedFiniteFaces
import FLatticePaper.Tiles.CorrectedRegisterFaces

/-! The twelve-level cutoff for physical polygons in the two base shears. -/

namespace FLatticePaper.Tiles.CorrectedCutoffTwelve

open FLatticePaper.Construction CorrectedRegisterDiagram CorrectedLevelTests CorrectedFaceBounds
open CorrectedFiniteFaces
open CorrectedRegisterFaces (box low high)

private def index : Side → Fin 4
  | .bottom => 0
  | .top => 1
  | .left => 2
  | .right => 3

def face (q : Fin 4 → Probe) (s : Side) : Face :=
  let a := q (index s)
  ⟨a.width,if (index s).val%2=1 then -a.slope else a.slope,a.v⟩

/-- When the other coordinate ranges across the reference rectangle, both ends
of its interval stay within twelve multiples of the face width. -/
structure Fits (q : Fin 4 → Probe) : Prop where
  horizontal : (q 3).w ≤ (q 2).w+24
  vertical : (q 1).w ≤ (q 0).w+24
  widths : ∀ i, |(q i).slope| < (q i).width
  endpoints : ∀ i, -12*(q i).width ≤ |(q i).slope| *((q i).v-low q i-12) ∧
    |(q i).slope| *((q i).v-high q i+12) ≤ 12*(q i).width

private theorem cut_line (q : Probe) (reverse : Bool) (hp : 0 < q.width) :
    Cut 12 ⟨q.width,if reverse then -q.slope else q.slope,q.v⟩
      (if reverse then -q.w else q.w) 0 ↔ inside 12 (q.line reverse) := by
  cases reverse
  · simpa [Cut,Probe.line] using inside_iff 12 q.width q.slope q.w q.v (by decide) hp
  · simpa [Cut,Probe.line] using inside_iff 12 q.width q.slope (-q.w) (-q.v) (by decide) hp

private theorem forall_sides (p : Fin 4 → Prop) : (∀ s, p (index s)) ↔ ∀ i, p i := by
  constructor
  · intro h i; fin_cases i
    · exact h .bottom
    · exact h .top
    · exact h .left
    · exact h .right
  · intro h s; exact h _

/-- With the endpoint bounds, a site passes the four normalized tests exactly
when it passes the original four determinant inequalities. -/
theorem exact_iff (q : Fin 4 → Probe) (h : Fits q) :
    CorrectedRegisterFaces.exact q ↔ ∀ i, inside 12 ((q i).line (decide (i.val%2=1))) := by
  have hx := h.horizontal
  have hy := h.vertical
  have hw (s : Side) : |(face q s).slope| < (face q s).width := by
    cases s <;> simpa [face,index] using h.widths _
  have ends (s : Side) : -12*(face q s).width ≤ |(face q s).slope| *((extent (box q) 12 s).1+(face q s).offset) ∧
      |(face q s).slope| *((extent (box q) 12 s).2+(face q s).offset) ≤ 12*(face q s).width := by
    have E := h.endpoints (index s)
    cases s <;> norm_num [face,index,box,extent,low,high,Fin.ext_iff] at E ⊢ <;> constructor
    all_goals first | linarith only [E.1] | linarith only [E.2]
  have H := four_faces_of_endpoints (box q) (face q) 12 (by decide)
    (by change -(q 2).w-12 ≤ -(q 3).w+12; omega)
    (by change -(q 0).w-12 ≤ -(q 1).w+12; omega) hw ends 0
  rw [←forall_sides (fun i => inside 12 ((q i).line (decide (i.val%2=1))))]
  unfold CorrectedRegisterFaces.exact
  rw [←forall_sides]
  refine Iff.trans (forall_congr' fun s => ?_) (H.trans (forall_congr' fun s => ?_))
  · cases s <;> simp [Exact,face,index,margin,box,transverse]
  · have pos (j : Fin 4) : 0 < (q j).width := lt_of_le_of_lt (abs_nonneg _) (h.widths j)
    cases s
    · simpa [face,index,box,margin,transverse] using cut_line (q 2) false (pos 2)
    · simpa [face,index,box,margin,transverse] using cut_line (q 3) true (pos 3)
    · simpa [face,index,box,margin,transverse] using cut_line (q 0) false (pos 0)
    · simpa [face,index,box,margin,transverse] using cut_line (q 1) true (pos 1)

end FLatticePaper.Tiles.CorrectedCutoffTwelve
