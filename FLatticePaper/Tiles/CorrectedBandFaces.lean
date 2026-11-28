import FLatticePaper.Tiles.CorrectedCellsBands
import FLatticePaper.Tiles.CorrectedDomainLattice
import FLatticePaper.Tiles.CorrectedFaceBounds

/-! The four physical probes of a lengthened tile in register coordinates. -/

namespace FLatticePaper.Tiles.CorrectedBandFaces

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open CorrectedCellsBands CorrectedDomainLattice

private abbrev even (v : Site) := (v.1+v.2)%2=0
def reference (z : Site) : Site := if oddSite z then (1,0) else 0

/-- The displacement of the point used on each of the four lines in a fixed physical parity. -/
def bias (a b : Site) (h v : ℕ) (o : Bool) : CorrectedFaceBounds.Side → Site
  | .bottom => probe a o
  | .top => -b-(v : ℤ) • b-((1,-1):Site)-probe a o
  | .left => -((1,0):Site)-mulI (probe (transverse b) (!o))
  | .right => -a-(h : ℤ) • a+((0,1):Site)+mulI (probe (transverse b) (!o))

private def positive (a b z : Site) : CorrectedFaceBounds.Side → Prop
  | .bottom => 0 ≤ cross a z
  | .top => cross a z ≤ 0
  | .left => 0 ≤ cross z b
  | .right => cross z b ≤ 0

private theorem physical (a b : Site) (h v : ℕ) (z : Site) :
    Band a b h v z ↔ ∀ s, positive a b (z+bias a b h v (oddSite z) s) s := by
  have enum (P : CorrectedFaceBounds.Side → Prop) : (∀ s, P s) ↔ P .bottom ∧ P .top ∧ P .left ∧ P .right := by
    constructor
    · intro h; exact ⟨h _,h _,h _,h _⟩
    · rintro ⟨hb,ht,hl,hr⟩ s; cases s <;> assumption
  rw [enum]
  simp only [Band,allowances,positive,bias]
  generalize probe a (oddSite z) = r
  generalize probe (transverse b) (!oddSite z) = t
  obtain ⟨ax,ay⟩ := a
  obtain ⟨bx,by'⟩ := b
  simp [cross,mulI,Prod.smul_mk]
  ring_nf
  omega

private theorem change_units (p : Fraction) (a b z : Site) (hm : 0 < scale p)
    (ha : even a) (hb : even b) (hz : even z) (s : CorrectedFaceBounds.Side) :
    positive a b z s ↔ positive (chart p a) (chart p b) (chart p z) s := by
  have pa := chart_det p a z ha hz
  have pb := chart_det p z b hz hb
  cases s <;> simp only [positive,cross] <;> constructor <;> intro h
  all_goals first
    | nlinarith only [pa,mul_nonneg hm.le h]
    | nlinarith only [pb,mul_nonneg hm.le h]
    | nlinarith only [pa,mul_nonpos_of_nonneg_of_nonpos hm.le h]
    | nlinarith only [pb,mul_nonpos_of_nonneg_of_nonpos hm.le h]
    | by_contra! hn; nlinarith only [pa,h,mul_neg_of_pos_of_neg hm hn]
    | by_contra! hn; nlinarith only [pb,h,mul_neg_of_pos_of_neg hm hn]
    | by_contra! hn; nlinarith only [pa,h,mul_pos hm hn]
    | by_contra! hn; nlinarith only [pb,h,mul_pos hm hn]

/-- The reference rectangle of the four projected probes; their values at the origin determine all its faces. -/
def box (c : CorrectedFaceBounds.Side → Site) : CorrectedFaceBounds.Box := ⟨-(c .left).1,-(c .right).1,-(c .bottom).2,-(c .top).2⟩

/-- The slope is signed inward on each of the two opposite faces. -/
def faces (a b : Site) (c : CorrectedFaceBounds.Side → Site) : CorrectedFaceBounds.Side → CorrectedFaceBounds.Face
  | .bottom => ⟨a.1,a.2,(c .bottom).1⟩
  | .top => ⟨a.1,-a.2,(c .top).1⟩
  | .left => ⟨b.2,b.1,(c .left).2⟩
  | .right => ⟨b.2,-b.1,(c .right).2⟩

private theorem exact_face (a b Z : Site) (c : CorrectedFaceBounds.Side → Site) (s : CorrectedFaceBounds.Side) :
    positive a b (Z+c s) s ↔ CorrectedFaceBounds.Exact (faces a b c s) (CorrectedFaceBounds.margin (box c) Z s) (CorrectedFaceBounds.transverse Z s) := by
  cases s <;> simp [positive,cross,CorrectedFaceBounds.Exact,faces,CorrectedFaceBounds.margin,box,CorrectedFaceBounds.transverse] <;> constructor <;> intro h <;> linarith

private theorem parity_facts (a b c z : Site) (h v : ℕ) (ha : even a) (hb : even b) (hc : even c) :
    oddSite (z-c)=oddSite z ∧ even (z-reference z) ∧
      ∀ s, even (reference z-c+bias a b h v (oddSite z) s) := by
  have sh (i : ℤ) (w : Site) (hw : even w) : even (i • w) := by
    change (i*w.1+i*w.2)%2=0
    rw [←mul_add,Int.mul_emod,hw]; simp
  have H := sh (h : ℤ) a ha
  have V := sh (v : ℤ) b hb
  change (a.1+a.2)%2=0 at ha
  change (b.1+b.2)%2=0 at hb
  change (c.1+c.2)%2=0 at hc
  change ((h : ℤ)*a.1+(h : ℤ)*a.2)%2=0 at H
  change ((v : ℤ)*b.1+(v : ℤ)*b.2)%2=0 at V
  have same : ((z-c).1+(z-c).2)%2=(z.1+z.2)%2 := by simp only [Prod.fst_sub,Prod.snd_sub]; omega
  refine ⟨by simp only [oddSite,same],?_,?_⟩
  · by_cases p : (z.1+z.2)%2=1 <;> simp [even,reference,oddSite,p] <;> omega
  · intro s
    by_cases p : (z.1+z.2)%2=1 <;> cases s
    all_goals simp [even,bias,reference,oddSite,probe,p,mulI]
    all_goals try split_ifs
    all_goals try dsimp
    all_goals omega

/-- The projected test for any translated polygon. The offsets use its four probes at one reference
site of the required parity. Each tested coordinate is integral. -/
theorem projected (p : Fraction) (a b c : Site) (h v : ℕ) (z : Site) (hm : 0 < scale p)
    (ha : even a) (hb : even b) (hc : even c) :
    let Z := chart p (z-reference z)
    let t := fun s => chart p (reference z-c+bias a b h v (oddSite z) s)
    let F := faces (chart p a) (chart p b) t
    Band a b h v (z-c) ↔ ∀ s, CorrectedFaceBounds.Exact (F s) (CorrectedFaceBounds.margin (box t) Z s) (CorrectedFaceBounds.transverse Z s) := by
  obtain ⟨par,base,rest⟩ := parity_facts a b c z h v ha hb hc
  dsimp only
  rw [physical,par]
  apply forall_congr'
  intro s
  let r := reference z-c+bias a b h v (oddSite z) s
  have add : z-c+bias a b h v (oddSite z) s = (z-reference z)+r := by dsimp [r]; abel
  rw [add]
  have ep : even ((z-reference z)+r) := by
    have rr := rest s
    change (r.1+r.2)%2=0 at rr
    change ((z-reference z).1+(z-reference z).2)%2=0 at base
    change (((z-reference z).1+r.1)+((z-reference z).2+r.2))%2=0
    omega
  rw [change_units p _ _ _ hm ha hb ep,chart_add p _ _ base (rest s)]
  exact exact_face _ _ _ (fun i => chart p (reference z-c+bias a b h v (oddSite z) i)) s

/-- With the endpoint bounds checked, membership in a physical tile is exactly four bounded integer tests. -/
theorem projected_cut (p : Fraction) (a b c : Site) (h v : ℕ) (z : Site) (hm : 0 < scale p)
    (ha : even a) (hb : even b) (hc : even c) (m : ℤ) (hm' : 0 ≤ m) :
    let Z := chart p (z-reference z)
    let t := fun s => chart p (reference z-c+bias a b h v (oddSite z) s)
    let F := faces (chart p a) (chart p b) t
    let R := box t
    R.left-m ≤ R.right+m → R.bottom-m ≤ R.top+m →
    (∀ s, |(F s).slope| < (F s).width) →
    (∀ s, -m*(F s).width ≤ |(F s).slope| * ((CorrectedFaceBounds.extent R m s).1+(F s).offset) ∧
      |(F s).slope| * ((CorrectedFaceBounds.extent R m s).2+(F s).offset) ≤ m*(F s).width) →
    (Band a b h v (z-c) ↔ ∀ s, CorrectedFaceBounds.Cut m (F s) (CorrectedFaceBounds.margin R Z s)
      (CorrectedFaceBounds.transverse Z s)) := by
  intro Z t F R hx hy widths ends
  exact (projected p a b c h v z hm ha hb hc).trans
    (CorrectedFaceBounds.four_faces_of_endpoints R F m hm' hx hy widths ends Z)

end FLatticePaper.Tiles.CorrectedBandFaces
