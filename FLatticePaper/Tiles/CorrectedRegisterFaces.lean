import FLatticePaper.Tiles.CorrectedRegisterDiagram

/-! Exact determinant tests and their four-level readings in a register diagram. -/

namespace FLatticePaper.Tiles.CorrectedRegisterFaces

open FLatticePaper.Construction CorrectedRegisterDiagram CorrectedLevelTests CorrectedFaceBounds

private def index : Side → Fin 4
  | .bottom => 0
  | .top => 1
  | .left => 2
  | .right => 3

/-- The reference rectangle with origin at the tested site. -/
def box (q : Fin 4 → Probe) : Box := ⟨-(q 2).w,-(q 3).w,-(q 0).w,-(q 1).w⟩

def face (q : Fin 4 → Probe) (s : Side) : Face :=
  let a := q (index s)
  ⟨a.width,if (index s).val%2=1 then -a.slope else a.slope,a.v⟩

def low (q : Fin 4 → Probe) (i : Fin 4) := if i.val<2 then (q 2).w else (q 0).w
def high (q : Fin 4 → Probe) (i : Fin 4) := if i.val<2 then (q 3).w else (q 1).w

/-- When the other coordinate ranges across the reference rectangle, both ends
of its interval stay within four multiples of the face width. -/
structure Fits (q : Fin 4 → Probe) : Prop where
  horizontal : (q 3).w ≤ (q 2).w+8
  vertical : (q 1).w ≤ (q 0).w+8
  widths : ∀ i, |(q i).slope| < (q i).width
  endpoints : ∀ i, -4*(q i).width ≤ |(q i).slope| *((q i).v-low q i-4) ∧
    |(q i).slope| *((q i).v-high q i+4) ≤ 4*(q i).width

/-- Four unbounded determinant inequalities, with the upper and right inequalities reversed. -/
def exact (q : Fin 4 → Probe) : Prop :=
  ∀ i, let a := q i
       if i.val%2=1 then a.width*a.w ≤ a.slope*a.v else a.slope*a.v ≤ a.width*a.w

private theorem cut_line (q : Probe) (reverse : Bool) (hp : 0 < q.width) :
    Cut 4 ⟨q.width,if reverse then -q.slope else q.slope,q.v⟩
      (if reverse then -q.w else q.w) 0 ↔ (q.line reverse).holds := by
  cases reverse
  · simpa [Cut,Probe.line] using holds_of_cut q.width q.slope q.w q.v hp
  · simpa [Cut,Probe.line] using holds_of_cut q.width q.slope (-q.w) (-q.v) hp

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
    exact q ↔ ∀ i, ((q i).line (decide (i.val%2=1))).holds := by
  have hx := h.horizontal
  have hy := h.vertical
  have hw (s : Side) : |(face q s).slope| < (face q s).width := by
    cases s <;> simpa [face,index] using h.widths _
  have ends (s : Side) : -4*(face q s).width ≤ |(face q s).slope| *((extent (box q) 4 s).1+(face q s).offset) ∧
      |(face q s).slope| *((extent (box q) 4 s).2+(face q s).offset) ≤ 4*(face q s).width := by
    have E := h.endpoints (index s)
    cases s <;> norm_num [face,index,box,extent,low,high,Fin.ext_iff] at E ⊢ <;> constructor
    all_goals first | linarith only [E.1] | linarith only [E.2]
  have H := four_faces_of_endpoints (box q) (face q) 4 (by decide)
    (by change -(q 2).w-4 ≤ -(q 3).w+4; omega)
    (by change -(q 0).w-4 ≤ -(q 1).w+4; omega) hw ends 0
  rw [←forall_sides (fun i => ((q i).line (decide (i.val%2=1))).holds)]
  unfold exact
  rw [←forall_sides]
  refine Iff.trans (forall_congr' fun s => ?_) (H.trans (forall_congr' fun s => ?_))
  · cases s <;> simp [Exact,face,index,margin,box,transverse]
  · have pos (j : Fin 4) : 0 < (q j).width := lt_of_le_of_lt (abs_nonneg _) (h.widths j)
    cases s
    · simpa [face,index,box,margin,transverse] using cut_line (q 2) false (pos 2)
    · simpa [face,index,box,margin,transverse] using cut_line (q 3) true (pos 3)
    · simpa [face,index,box,margin,transverse] using cut_line (q 0) false (pos 0)
    · simpa [face,index,box,margin,transverse] using cut_line (q 1) true (pos 1)

/-- The determinant inequalities of a shape with these bounds give its membership predicate. -/
theorem shape_iff (s : Shape) (r : Register) (par : Bool) (sec : Fin 3) (h : Fits (s.probe r par sec)) :
    exact (s.probe r par sec) ↔ s.contains r par sec := exact_iff _ h

end FLatticePaper.Tiles.CorrectedRegisterFaces
