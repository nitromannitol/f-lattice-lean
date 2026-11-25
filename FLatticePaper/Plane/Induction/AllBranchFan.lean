import FLatticePaper.Plane.Induction.FanAcyclic
import FLatticePaper.Plane.Induction.FanCompat
import FLatticePaper.Plane.Induction.ContactCone
import FLatticePaper.Plane.Induction.FanPropagation
import FLatticePaper.Plane.Induction.CapRay

/-! # The all-branch contact fan (AUDIT_FREE_THREE_STEP_RETURNS §1, "Contact-fan acyclicity")

For the cone of base `b` (height `b.2`, depth `K`), the contact fan `D` is the set of cone sites of the open rectangle that are contacts of
the parabola `parabolaField b.2 z = capMin (z.2 − b.2)`. Its physical edges (`fanRel`): an even contact is white with its east edge; an odd
contact is black (both vertical inputs) or white (one vertical input). The rank `fanRank = −2x + parity` strictly decreases on every edge
(`FanAcyclic`), so the relation has no cycle (`contactFan_acyclic`). Here the rank argument is run on the whole fan, black branches included:
black odd contacts have two even inputs, which the rank also lowers.

Named inputs of the acyclicity: the cone window `hwin` (`CapRay.cone_window` supplies it) and the successor designations `sel` (east at
even contacts, a vertical input at odd white contacts; `contactFan_odd_input` shows the latter exists). -/

namespace FLatticePaper.AllBranchFan

open FLatticePaper FLatticePaper.Induction FLatticePaper.ContactCone FLatticePaper.FanAcyclic FLatticePaper.FanCompat
  FLatticePaper.CapRay FLatticePaper.FanPropagation

/-- The all-branch contact fan of the cone of base `b` and depth `K`: cone sites of the open rectangle that are contacts. -/
def contactFan (frame : ChildFrame) (F : Field) (b : Site) (K : ℕ) : Set Site :=
  {x | (frame.openRect x ∧ ConeRoot b K x) ∧ F x = parabolaField b.2 x}

theorem mem_contactFan {frame : ChildFrame} {F : Field} {b : Site} {K : ℕ} {x : Site} :
    x ∈ contactFan frame F b K ↔ (frame.openRect x ∧ ConeRoot b K x) ∧ F x = parabolaField b.2 x :=
  Iff.rfl

/-- **An even contact of the fan is white** (the window gives nonnegative input excesses; the even parabola has zero Laplacian). -/
theorem contactFan_even_white {frame : ChildFrame} {F : Field} {b : Site} {K : ℕ}
    (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hwin : WindowOn (fun x => frame.openRect x ∧ ConeRoot b K x) F (fun i => parabolaField b.2 i))
    {x : Site} (hx : x ∈ contactFan frame F b K) (he : EvenSite x) : laplacian F x = 0 := by
  obtain ⟨hcone, hc⟩ := mem_contactFan.mp hx
  exact even_contact_white (hbin x) hc he (hwin x hcone (incomingNeg x) (Or.inl rfl))
    (hwin x hcone (incomingPos x) (Or.inr rfl))

/-- **An odd white contact has a contact vertical input** (the input excesses sum to `lap F x + 1 = 1`, each `≥ 0`). -/
theorem contactFan_odd_input {frame : ChildFrame} {F : Field} {b : Site} {K : ℕ}
    (hwin : WindowOn (fun x => frame.openRect x ∧ ConeRoot b K x) F (fun i => parabolaField b.2 i))
    {x : Site} (hx : x ∈ contactFan frame F b K) (ho : ¬ EvenSite x) (hw : laplacian F x = 0) :
    ∃ y, (y = incomingNeg x ∨ y = incomingPos x) ∧ F y = parabolaField b.2 y := by
  obtain ⟨hcone, hc⟩ := mem_contactFan.mp hx
  have key := excess_sum (F := F) (m := parabolaField b.2) hc
  rw [parabola_lap_odd b.2 x ho, hw] at key
  have hn : parabolaField b.2 (incomingNeg x) ≤ F (incomingNeg x) := hwin x hcone (incomingNeg x) (Or.inl rfl)
  have hp : parabolaField b.2 (incomingPos x) ≤ F (incomingPos x) := hwin x hcone (incomingPos x) (Or.inr rfl)
  by_cases hn0 : F (incomingNeg x) = parabolaField b.2 (incomingNeg x)
  · exact ⟨incomingNeg x, Or.inl rfl, hn0⟩
  · by_cases hp0 : F (incomingPos x) = parabolaField b.2 (incomingPos x)
    · exact ⟨incomingPos x, Or.inr rfl, hp0⟩
    · exfalso
      omega

/-- **A contact input of a fan site is in the fan** (`fan_next_P`: the cone step at an even site is east, at an odd site either vertical
input; the open-rectangle membership of the input is the named `hopen`). -/
theorem contactFan_mem_of_input {frame : ChildFrame} {F : Field} {b : Site} {K : ℕ}
    (hP : frame.Packet F) (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num)
    (hK2 : 2 ≤ K) (hKs : frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ))
    (hKr : 2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 5 * frame.child.num - 1)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (hb : frame.child.num + 2 ≤ frame.tGrade b)
    {x w : Site} (hx : x ∈ contactFan frame F b K) (hw : w = incomingNeg x ∨ w = incomingPos x)
    (hEven : EvenSite x → w = incomingPos x) (hopen : frame.openRect w)
    (hcontact : F w = parabolaField b.2 w) : w ∈ contactFan frame F b K := by
  obtain ⟨hcone, -⟩ := mem_contactFan.mp hx
  exact mem_contactFan.mpr ⟨fan_next_P frame hP hsig hs K hK2 hKs hKr hcap b hb x w hcone hw hEven hopen hcontact,
    hcontact⟩

/-- The fan rank drops along a fan edge: even designations go east, odd designations (and black odd inputs) go vertical. -/
theorem contactFan_rank_lt {frame : ChildFrame} {F : Field} {b : Site} {K : ℕ}
    (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hwin : WindowOn (fun x => frame.openRect x ∧ ConeRoot b K x) F (fun i => parabolaField b.2 i))
    {free : Site → Prop} {sel : Site → Site}
    (hEvenSel : ∀ x ∈ contactFan frame F b K, EvenSite x → sel x = incomingPos x)
    (hOddSel : ∀ x ∈ contactFan frame F b K, ¬ EvenSite x → laplacian F x = 0 →
      sel x = incomingNeg x ∨ sel x = incomingPos x)
    {x y : Site} (h : fanRel F (contactFan frame F b K) free sel x y) : fanRank y < fanRank x := by
  obtain ⟨hxD, hcase⟩ := h
  rcases hcase with ⟨hb, hy, -⟩ | ⟨hw, -, hsy, -⟩
  · have ho : ¬ EvenSite x := fun he => by
      have := contactFan_even_white hbin hwin hxD he
      rw [hb] at this
      norm_num at this
    exact fanRank_vertical_of_odd x ho y hy
  · by_cases he : EvenSite x
    · have hyE : y = incomingPos x := hsy.trans (hEvenSel x hxD he)
      rw [hyE]
      exact fanRank_east_of_even x he
    · rcases hOddSel x hxD he hw with hs | hs
      · exact fanRank_vertical_of_odd x he y (Or.inl (hsy.trans hs))
      · exact fanRank_vertical_of_odd x he y (Or.inr (hsy.trans hs))

/-- Along any fan path the rank strictly decreases. -/
theorem contactFan_rank_chain {frame : ChildFrame} {F : Field} {b : Site} {K : ℕ}
    (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hwin : WindowOn (fun x => frame.openRect x ∧ ConeRoot b K x) F (fun i => parabolaField b.2 i))
    {free : Site → Prop} {sel : Site → Site}
    (hEvenSel : ∀ x ∈ contactFan frame F b K, EvenSite x → sel x = incomingPos x)
    (hOddSel : ∀ x ∈ contactFan frame F b K, ¬ EvenSite x → laplacian F x = 0 →
      sel x = incomingNeg x ∨ sel x = incomingPos x)
    {a c : Site} (h : Relation.TransGen (fanRel F (contactFan frame F b K) free sel) a c) :
    fanRank c < fanRank a := by
  induction h with
  | single h => exact contactFan_rank_lt hbin hwin hEvenSel hOddSel h
  | tail _ hbc ih => exact lt_trans (contactFan_rank_lt hbin hwin hEvenSel hOddSel hbc) ih

/-- **The all-branch contact fan is acyclic**: no site of the fan reaches itself through the fan relation. -/
theorem contactFan_acyclic {frame : ChildFrame} {F : Field} {b : Site} {K : ℕ}
    (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hwin : WindowOn (fun x => frame.openRect x ∧ ConeRoot b K x) F (fun i => parabolaField b.2 i))
    {free : Site → Prop} {sel : Site → Site}
    (hEvenSel : ∀ x ∈ contactFan frame F b K, EvenSite x → sel x = incomingPos x)
    (hOddSel : ∀ x ∈ contactFan frame F b K, ¬ EvenSite x → laplacian F x = 0 →
      sel x = incomingNeg x ∨ sel x = incomingPos x)
    (x : Site) : ¬ Relation.TransGen (fanRel F (contactFan frame F b K) free sel) x x := by
  intro h
  exact lt_irrefl _ (contactFan_rank_chain hbin hwin hEvenSel hOddSel h)

end FLatticePaper.AllBranchFan
