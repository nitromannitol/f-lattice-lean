import FLatticePaper.Tiles.CorrectedBandFaces
import FLatticePaper.Tiles.CorrectedRegisterFaces
import FLatticePaper.Tiles.CorrectedRegisterLattice

/-! The four unbounded tests of a register shape at a physical point, including sector boundaries. -/

namespace FLatticePaper.Tiles.CorrectedPhysicalFaces

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open CorrectedCellsBands CorrectedDomainLattice CorrectedRegisterDiagram

abbrev EvenPoint (z : Site) := (z.1+z.2)%2=0

theorem even_sub {v u : Site} (a : EvenPoint v) (b : EvenPoint u) : EvenPoint (v-u) := by
  change (v.1+v.2)%2=0 at a
  change (u.1+u.2)%2=0 at b
  change ((v.1-u.1)+(v.2-u.2))%2=0
  omega

theorem even_add {v u : Site} (a : EvenPoint v) (b : EvenPoint u) : EvenPoint (v+u) := by
  change (v.1+v.2)%2=0 at a
  change (u.1+u.2)%2=0 at b
  change ((v.1+u.1)+(v.2+u.2))%2=0
  omega

theorem even_smul (k : ℤ) {u : Site} (h : EvenPoint u) : EvenPoint (k • u) := by
  change (k*u.1+k*u.2)%2=0
  rw [←mul_add,Int.mul_emod,h]; simp

theorem chart_sub (p : Fraction) {v u : Site} (hv : EvenPoint v) (hu : EvenPoint u) :
    chart p (v-u) = chart p v-chart p u := by
  have h := chart_add p (v-u) u (even_sub hv hu) hu
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

/-- The two closed-sector comparisons for the horizontal and vertical primitive sides. -/
def Aligned (a b : Site) (sec : Fin 3) : Prop :=
  (if sec=0 then 3*a.2 ≤ a.1 else a.1 ≤ 3*a.2) ∧
  (if sec=2 then 3*(-b.1) ≤ b.2 else b.2 ≤ 3*(-b.1))

private def selected (odd bright : Bool) : Site :=
  if odd then (0,1) else if bright then (1,1) else (-2,0)

private theorem selected_cross (a : Site) (odd bright : Bool)
    (h : if bright then 3*a.2 ≤ a.1 else a.1 ≤ 3*a.2) :
    cross a (probe a odd) = cross a (selected odd bright) := by
  cases odd
  · cases bright
    · change a.1 ≤ 3*a.2 at h
      by_cases hi : 3*a.2 ≤ a.1
      · have e : a.1=3*a.2 := le_antisymm h hi
        simp [probe,selected,cross,e]; ring
      · simp [probe,selected,hi]
    · change 3*a.2 ≤ a.1 at h
      simp [probe,selected,h]
  · rfl

private def four (a b x : Site) (h v : ℕ) (p q : Site) : Prop :=
  0 ≤ cross a (x+p) ∧ cross a (x-b-(v : ℤ) • b-((1,-1):Site)-p) ≤ 0 ∧
  0 ≤ cross (x-((1,0):Site)-mulI q) b ∧ cross (x-a-(h : ℤ) • a+((0,1):Site)+mulI q) b ≤ 0

private theorem selected_band (a b x : Site) (h v : ℕ) (par : Bool) (sec : Fin 3)
    (hp : oddSite x=par) (hs : Aligned a b sec) :
    Band a b h v x ↔ four a b x h v (selected par (decide (sec=0))) (selected (!par) (decide (sec=2))) := by
  have H := selected_cross a par (decide (sec=0)) (by simpa using hs.1)
  have V := selected_cross (transverse b) (!par) (decide (sec=2)) (by simpa [transverse] using hs.2)
  unfold Band allowances four
  rw [hp]
  generalize probe a par = P at H ⊢
  generalize probe (transverse b) (!par) = Q at V ⊢
  generalize selected par (decide (sec=0)) = R at H ⊢
  generalize selected (!par) (decide (sec=2)) = T at V ⊢
  simp [cross,mulI] at H V ⊢
  ring_nf at H V ⊢
  constructor <;> rintro ⟨h₀,h₁,h₂,h₃⟩ <;> refine ⟨?_,?_,?_,?_⟩ <;> linarith only [h₀,h₁,h₂,h₃,H,V]

/-- Project the corner, primitive vectors and the two displacements of the outer edges. -/
def projectedShape (p : Fraction) (a b c : Site) (h v : ℕ) : Shape :=
  ⟨chart p c,chart p a,chart p b,chart p ((h : ℤ) • a),chart p ((v : ℤ) • b)⟩

private def exactAt (a b : Site) (U : Fin 4 → Site) : Prop :=
  0 ≤ cross a (U 0) ∧ cross a (U 1) ≤ 0 ∧ 0 ≤ cross (U 2) b ∧ cross (U 3) b ≤ 0

private def coordinates (a b : Site) (h v : ℕ) (Z : Fin 4 → Site) (i : Fin 4) : Site :=
  match i.val with
  | 1 => Z i-b-(v : ℤ) • b
  | 3 => Z i-a-(h : ℤ) • a
  | _ => Z i

private theorem bias_test (a b c z : Site) (h v : ℕ) (par : Bool) (sec : Fin 3) :
    let ref : Site := if par then (1,0) else 0
    let Z := fun i => z-ref-c+bias par sec i
    four a b (z-c) h v (selected par (decide (sec=0))) (selected (!par) (decide (sec=2))) ↔
       exactAt a b (coordinates a b h v Z) := by
  dsimp only
  unfold four exactAt
  simp [coordinates,bias,selected]
  abel

private theorem chart_sign (p : Fraction) (a u : Site) (hm : 0 < scale p)
    (ha : EvenPoint a) (hu : EvenPoint u) :
    (0 ≤ cross a u ↔ 0 ≤ cross (chart p a) (chart p u)) ∧
    (cross a u ≤ 0 ↔ cross (chart p a) (chart p u) ≤ 0) := by
  have H : 2*cross (chart p a) (chart p u) = scale p*cross a u := chart_det p a u ha hu
  constructor <;> constructor <;> intro h
  · linarith only [H,mul_nonneg hm.le h]
  · by_contra! h'; linarith only [H,h,mul_neg_of_pos_of_neg hm h']
  · linarith only [H,mul_nonpos_of_nonneg_of_nonpos hm.le h]
  · by_contra! h'; linarith only [H,h,mul_pos hm h']

/-- At an arbitrary actual site, the four physical determinant inequalities are precisely
those of its register polygon. On a dividing line both choices of probe have the same determinant. -/
theorem band_iff (r : Register) (a b c z : Site) (h v : ℕ) (sec : Fin 3)
    (ha : EvenPoint a) (hb : EvenPoint b) (hc : EvenPoint c) (aligned : Aligned a b sec) :
    let p : Fraction := ⟨r.n,r.d⟩
    let par := oddSite z
    let ref : Site := if par then (1,0) else 0
    0 < scale p → (r.X,r.Y) = chart p (z-ref) →
    (Band a b h v (z-c) ↔ CorrectedRegisterFaces.exact ((projectedShape p a b c h v).probe r par sec)) := by
  intro p par ref hm base
  have hp : oddSite (z-c)=par := by
    change (c.1+c.2)%2=0 at hc
    change decide (((z.1-c.1)+(z.2-c.2))%2=1)=decide ((z.1+z.2)%2=1)
    rw [show ((z.1-c.1)+(z.2-c.2))%2=(z.1+z.2)%2 by omega]
  have hz : EvenPoint (z-ref) := by
    by_cases ho : (z.1+z.2)%2=1 <;> simp [EvenPoint,ref,par,oddSite,ho] <;> omega
  let Z := fun i => z-ref-c+bias par sec i
  let U := coordinates a b h v Z
  have eZ (i) : EvenPoint (Z i) := even_add (even_sub hz hc) (CorrectedRegisterLattice.bias_even par sec i)
  have eU (i) : EvenPoint (U i) := by
    fin_cases i
    · exact eZ 0
    · exact even_sub (even_sub (eZ 1) hb) (even_smul _ hb)
    · exact eZ 2
    · exact even_sub (even_sub (eZ 3) ha) (even_smul _ ha)
  have chartZ (i) : chart p (Z i) = (r.X,r.Y)-chart p c+displacement r (bias par sec i) := by
    rw [displacement_eq r _ (CorrectedRegisterLattice.bias_even par sec i),base]
    dsimp [Z]
    rw [chart_add p _ _ (even_sub hz hc) (CorrectedRegisterLattice.bias_even par sec i),chart_sub p hz hc]
  have bt := bias_test a b c z h v par sec
  dsimp only at bt
  rw [selected_band a b _ h v par sec hp aligned,bt]
  change exactAt a b U ↔ _
  unfold exactAt
  rw [(chart_sign p a _ hm ha (eU 0)).1,(chart_sign p a _ hm ha (eU 1)).2,
    (chart_sign p _ b hm (eU 2) hb).1,(chart_sign p _ b hm (eU 3) hb).2]
  have top : chart p (U 1)=chart p (Z 1)-chart p b-chart p ((v : ℤ) • b) :=
    (chart_sub p (even_sub (eZ 1) hb) (even_smul _ hb)).trans (by rw [chart_sub p (eZ 1) hb])
  have right : chart p (U 3)=chart p (Z 3)-chart p a-chart p ((h : ℤ) • a) :=
    (chart_sub p (even_sub (eZ 3) ha) (even_smul _ ha)).trans (by rw [chart_sub p (eZ 3) ha])
  rw [top,right,show U 0=Z 0 from rfl,show U 2=Z 2 from rfl,chartZ 0,chartZ 1,chartZ 2,chartZ 3]
  let q := (projectedShape p a b c h v).probe r par sec
  have eq : CorrectedRegisterFaces.exact q ↔
      ((q 0).slope*(q 0).v ≤ (q 0).width*(q 0).w ∧ (q 1).width*(q 1).w ≤ (q 1).slope*(q 1).v ∧
       (q 2).slope*(q 2).v ≤ (q 2).width*(q 2).w ∧ (q 3).width*(q 3).w ≤ (q 3).slope*(q 3).v) := by
    constructor
    · intro k; exact ⟨k 0,k 1,k 2,k 3⟩
    · rintro ⟨k₀,k₁,k₂,k₃⟩ i; fin_cases i <;> assumption
  rw [show (projectedShape p a b c h v).probe r par sec=q from rfl,eq]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · exact sub_nonneg
  · exact sub_nonpos
  · have H (u w : Site) : 0 ≤ cross u w ↔ w.1*u.2 ≤ w.2*u.1 := by
      unfold cross; rw [sub_nonneg,mul_comm u.1,mul_comm u.2]
    exact H _ _
  · have H (u w : Site) : cross u w ≤ 0 ↔ w.2*u.1 ≤ w.1*u.2 := by
      unfold cross; rw [sub_nonpos,mul_comm u.1,mul_comm u.2]
    exact H _ _

end FLatticePaper.Tiles.CorrectedPhysicalFaces
