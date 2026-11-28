import FLatticePaper.Tiles.StandardTiles

/-! Finite tests for the four determinant inequalities in the coordinates of the odd register. -/

namespace FLatticePaper.Tiles.CorrectedFaceBounds

open FLatticePaper.Construction FLatticePaper.Tiles

/-- The two coordinate intervals delimited by the four reference lines. -/
structure Box where
  left : ℤ
  right : ℤ
  bottom : ℤ
  top : ℤ

/-- The four signed distances used to locate a site relative to the reference lines. -/
inductive Side where
  | left | right | bottom | top
  deriving DecidableEq

def margin (r : Box) (z : Site) : Side → ℤ
  | .left => z.1-r.left
  | .right => r.right-z.1
  | .bottom => z.2-r.bottom
  | .top => r.top-z.2

def transverse (z : Site) : Side → ℤ
  | .left | .right => z.2
  | .bottom | .top => z.1

/-- The face inequality is `slope * (transverse + offset) ≤ width * margin`. -/
structure Face where
  width : ℤ
  slope : ℤ
  offset : ℤ

def Exact (f : Face) (w u : ℤ) : Prop := f.slope*(u+f.offset) ≤ f.width*w

/-- Above the cutoff the face is automatic. Inside the bounded range only the indicated integer level is tested. -/
def Cut (m : ℤ) (f : Face) (w u : ℤ) : Prop :=
  m < w ∨ ∃ l : ℤ, -m ≤ l ∧ l ≤ m ∧ w=l ∧ f.slope*(u+f.offset) ≤ l*f.width

private def distance (m : ℤ) (r : Box) (z : Site) :=
  max 0 (max (r.left-m-z.1) (max (z.1-r.right-m) (max (r.bottom-m-z.2) (z.2-r.top-m))))
private def clamp (m : ℤ) (r : Box) (z : Site) : Site :=
  (max (r.left-m) (min z.1 (r.right+m)), max (r.bottom-m) (min z.2 (r.top+m)))

private theorem clamp_mem (m : ℤ) (r : Box) (z : Site)
    (hx : r.left-m ≤ r.right+m) (hy : r.bottom-m ≤ r.top+m) (s : Side) :
    -m ≤ margin r (clamp m r z) s := by
  cases s <;> simp only [margin,clamp] <;> omega

private theorem clamp_distance (m : ℤ) (r : Box) (z : Site) (s : Side) :
    |transverse z s - transverse (clamp m r z) s| ≤ distance m r z := by
  cases s <;> simp only [transverse,clamp,distance,abs_le] <;> omega

private theorem outside (m : ℤ) (r : Box) (z : Site) (h : 0 < distance m r z) :
    ∃ s : Side, margin r z s = -m-distance m r z := by
  have h' := h
  unfold distance at h'
  by_cases hl : r.left-m-z.1 = distance m r z
  · exact ⟨.left,by change z.1-r.left = _; omega⟩
  by_cases hr : z.1-r.right-m = distance m r z
  · exact ⟨.right,by change r.right-z.1 = _; omega⟩
  by_cases hb : r.bottom-m-z.2 = distance m r z
  · exact ⟨.bottom,by change z.2-r.bottom = _; omega⟩
  exact ⟨.top,by simp only [margin,distance] at *; omega⟩

/-- For any four faces, testing the bounded integer levels suffices at every site if the slopes are
smaller than the widths and the transverse terms fit on the expanded box. -/
theorem four_faces (r : Box) (f : Side → Face) (m : ℤ) (hm : 0 ≤ m)
    (hx : r.left-m ≤ r.right+m) (hy : r.bottom-m ≤ r.top+m)
    (hw : ∀ s, |(f s).slope| < (f s).width)
    (fit : ∀ z : Site, (∀ s, -m ≤ margin r z s) →
      ∀ s, |(f s).slope*(transverse z s + (f s).offset)| ≤ m*(f s).width) (z : Site) :
    (∀ s, Exact (f s) (margin r z s) (transverse z s)) ↔
      (∀ s, Cut m (f s) (margin r z s) (transverse z s)) := by
  constructor
  · intro allFaces
    have inBox : ∀ s, -m ≤ margin r z s := by
      by_contra! bad
      obtain ⟨s,hs⟩ := bad
      have hd : 0 < distance m r z := by cases s <;> simp only [margin,distance] at * <;> omega
      obtain ⟨t,ht⟩ := outside m r z hd
      set δ := distance m r z
      let c := clamp m r z
      let v := transverse z t
      let v₀ := transverse c t
      let sl := (f t).slope
      let W := (f t).width
      let b := (f t).offset
      have h₀ : -m*W ≤ sl*(v₀+b) := by
        have e := (abs_le.mp (fit c (clamp_mem m r z hx hy) t)).1
        simpa only [neg_mul] using e
      have h₁ : |sl*(v-v₀)| ≤ |sl| *δ := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (clamp_distance m r z t) (abs_nonneg _)
      have h₂ : |sl| *δ < W*δ := mul_lt_mul_of_pos_right (hw t) hd
      have h' : sl*(v+b) ≤ W*(-m-δ) := by
        have h := allFaces t
        rwa [Exact,ht] at h
      have low := (abs_le.mp h₁).1
      linarith only [h₀,low,h₂,h']
    intro s
    by_cases h : m < margin r z s
    · exact Or.inl h
    · exact Or.inr ⟨_,inBox s,by omega,rfl,by simpa only [Exact,mul_comm (margin r z s)] using allFaces s⟩
  · intro allCuts
    have inBox (s : Side) : -m ≤ margin r z s := by
      rcases allCuts s with h|⟨l,hl,_,he,_⟩ <;> omega
    intro s
    rcases allCuts s with h|⟨l,_,_,rfl,he⟩
    · have hfit := (abs_le.mp (fit z inBox s)).2
      have pos : 0 ≤ (f s).width := le_trans (abs_nonneg _) (hw s).le
      have bound := mul_le_mul_of_nonneg_right h.le pos
      exact hfit.trans (by rwa [mul_comm (f s).width])
    · simpa only [Exact,mul_comm (f s).width] using he


/-- The transverse interval of a face on the box expanded by the cutoff. -/
def extent (r : Box) (m : ℤ) : Side → ℤ × ℤ
  | .left | .right => (r.bottom-m,r.top+m)
  | .bottom | .top => (r.left-m,r.right+m)

/-- Two endpoint checks per face suffice for the global equivalence of the four exact inequalities
and their bounded integer tests. -/
theorem four_faces_of_endpoints (r : Box) (f : Side → Face) (m : ℤ) (hm : 0 ≤ m)
    (hx : r.left-m ≤ r.right+m) (hy : r.bottom-m ≤ r.top+m)
    (hw : ∀ s, |(f s).slope| < (f s).width)
    (ends : ∀ s, -m*(f s).width ≤ |(f s).slope| * ((extent r m s).1+(f s).offset) ∧
      |(f s).slope| * ((extent r m s).2+(f s).offset) ≤ m*(f s).width) (z : Site) :
    (∀ s, Exact (f s) (margin r z s) (transverse z s)) ↔
      (∀ s, Cut m (f s) (margin r z s) (transverse z s)) := by
  apply four_faces r f m hm hx hy hw _ z
  intro x h s
  have bl := h .bottom
  have bt := h .top
  have xl := h .left
  have xr := h .right
  have e : (extent r m s).1 ≤ transverse x s ∧ transverse x s ≤ (extent r m s).2 := by
    cases s <;> simp only [extent,transverse,margin] at * <;> omega
  have lo := (ends s).1.trans (mul_le_mul_of_nonneg_left (add_le_add_left e.1 _) (abs_nonneg _))
  have hi := (mul_le_mul_of_nonneg_left (add_le_add_left e.2 _) (abs_nonneg _)).trans (ends s).2
  rw [show |(f s).slope*(transverse x s+(f s).offset)| =
    abs (|(f s).slope| * (transverse x s+(f s).offset)) by simp only [abs_mul,abs_abs],abs_le,←neg_mul]
  exact ⟨lo,hi⟩

end FLatticePaper.Tiles.CorrectedFaceBounds
