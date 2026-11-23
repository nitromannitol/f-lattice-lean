import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.OldPolicy
import FLatticePaper.Plane.Induction.W1Constructor
import FLatticePaper.Plane.Induction.ComparisonContacts

/-! Task 72 (nonfree roots, deck form): the nonfree root condition with the forced edge at the root itself.

* `laplacian_span_inv`: the Laplacian of the standard packet is invariant under the child deck (the kernel shifts `F` by a constant, the
  transverse vector shifts it by an affine function, which has zero Laplacian).
* `forcedEdge_add`: unseeded forced edges are carried by even translations that preserve the Laplacian (the unit squares and their
  inputs translate).
* `nonfree_root_forced_nonfree`: a nonfree root of the old policy is black, or its retained edge is the unseeded forced edge: the
  strict-interior translate (`nonfree_bridge`) carries `W1Forced` to the root, and the uniqueness of the retained input identifies the
  edge. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper FLatticePaper.SquareClauses FLatticePaper.AndOrRank

/-- Translating a unit square by `t` (`x + t ∈ squareCorners (a + t₁) (b + t₂) ↔ x ∈ squareCorners a b`). -/
theorem mem_corners_translate (a b : ℤ) (t x : Site) :
    x + t ∈ squareCorners (a + t.1) (b + t.2) ↔ x ∈ squareCorners a b := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨t1, t2⟩ := t
  show (x1 + t1, x2 + t2) ∈ squareCorners (a + t1) (b + t2) ↔ (x1, x2) ∈ squareCorners a b
  simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor <;> intro h <;> omega

/-- A subgroup-closed predicate holds on the child deck span, if it holds on the kernel and the transverse vector. -/
theorem span_pred {frame : ChildFrame} (P : Site → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hneg : ∀ a, P a → P (-a)) (hK : P (Kdeck frame)) (hV : P (Vdeck frame)) {v : Site}
    (hv : v ∈ frame.child.modifiedDeck.span) : P v := by
  let S : AddSubgroup Site :=
    { carrier := {x | P x}
      add_mem' := fun ha hb => hadd _ _ ha hb
      zero_mem' := h0
      neg_mem' := fun ha => hneg _ ha }
  have hKS : Kdeck frame ∈ S := hK
  have hVS : Vdeck frame ∈ S := hV
  have hvS : v ∈ S := by
    obtain ⟨i, j, rfl⟩ := hv
    have e : frame.child.modifiedDeck.combine i j = i • Kdeck frame + j • Vdeck frame := by
      simp only [PeriodDeck.combine, ChildFrame.child_modifiedDeck_kernel, ChildFrame.child_modifiedDeck_transverse,
        Kdeck, Vdeck]
      ext <;> simp
    rw [e]
    exact S.add_mem (S.zsmul_mem hKS i) (S.zsmul_mem hVS j)
  exact hvS

/-- The kernel of the child deck is `K = (d, n)`, which is even. -/
theorem evenSite_Kdeck (frame : ChildFrame) : EvenSite (Kdeck frame) := by
  obtain ⟨hn, hd⟩ := FLatticePaper.W1Exit.child_parity frame
  unfold EvenSite Kdeck
  simp only
  omega

theorem evenSite_Vdeck (frame : ChildFrame) : EvenSite (Vdeck frame) := by
  obtain ⟨hn, hd⟩ := FLatticePaper.W1Exit.child_parity frame
  unfold EvenSite Vdeck
  simp only
  omega

/-- The deck span consists of even sites. -/
theorem evenSite_of_span (frame : ChildFrame) {v : Site} (hv : v ∈ frame.child.modifiedDeck.span) : EvenSite v :=
  span_pred (frame := frame) (fun x => EvenSite x) (by unfold EvenSite; simp)
    (fun a b ha hb => by unfold EvenSite at *; simp only [Prod.fst_add, Prod.snd_add]; omega)
    (fun a ha => by unfold EvenSite at *; simp only [Prod.fst_neg, Prod.snd_neg]; omega)
    (evenSite_Kdeck frame) (evenSite_Vdeck frame) hv

theorem incomingNeg_add_incomingPos (z : Site) : FLatticePaper.incomingNeg z + FLatticePaper.incomingPos z = z + z := by
  unfold FLatticePaper.incomingNeg FLatticePaper.incomingPos
  split_ifs <;> ext <;> simp

/-- **The Laplacian is invariant under the child deck** (the standard packet). -/
theorem laplacian_span_inv (frame : ChildFrame) (G : Field) (hP : frame.Packet G) {v : Site}
    (hv : v ∈ frame.child.modifiedDeck.span) (z : Site) : laplacian G (z + v) = laplacian G z := by
  have hper := hP.periods
  unfold HasGeneratorPeriods at hper
  obtain ⟨hK, hV⟩ := hper
  refine span_pred (frame := frame) (fun x => ∀ z, laplacian G (z + x) = laplacian G z) ?_ ?_ ?_ ?_ ?_ hv z
  · intro z
    simp
  · intro a b ha hb z
    rw [← add_assoc, hb, ha]
  · intro a ha z
    have h := ha (z + -a)
    rw [neg_add_cancel_right] at h
    exact h.symm
  · intro z
    have hKe : EvenSite (Kdeck frame) := evenSite_Kdeck frame
    have hKdef : Kdeck frame = frame.child.modifiedDeck.kernel := by
      rw [ChildFrame.child_modifiedDeck_kernel]
      rfl
    rw [hKdef]
    unfold laplacian
    rw [FLatticePaper.Contacts.incomingNeg_add_even z _ (hKdef ▸ hKe),
      FLatticePaper.Contacts.incomingPos_add_even z _ (hKdef ▸ hKe)]
    rw [hK, hK, hK]
    ring
  · intro z
    have hVe : EvenSite (Vdeck frame) := evenSite_Vdeck frame
    have hVdef : Vdeck frame = frame.child.modifiedDeck.transverse := by
      rw [ChildFrame.child_modifiedDeck_transverse]
      rfl
    rw [hVdef]
    unfold laplacian
    rw [FLatticePaper.Contacts.incomingNeg_add_even z _ (hVdef ▸ hVe),
      FLatticePaper.Contacts.incomingPos_add_even z _ (hVdef ▸ hVe)]
    rw [hV, hV, hV]
    have hlin : FLatticePaper.incomingNeg z + FLatticePaper.incomingPos z = z + z := incomingNeg_add_incomingPos z
    have h1 := congrArg Prod.fst hlin
    have h2 := congrArg Prod.snd hlin
    simp only [Prod.fst_add, Prod.snd_add] at h1 h2
    unfold Fraction.transverseGrade
    linear_combination (-(frame.child.den)) * h2 + frame.child.num * h1

/-- **Unseeded forced edges are carried by even translations that preserve the Laplacian.** -/
theorem forcedEdge_add (G : Field) {v : Site} (hv : EvenSite v) (hL : ∀ z, laplacian G (z + v) = laplacian G z)
    {c o : Site} (h : ForcedEdge G (fun _ _ => False) c o) :
    ForcedEdge G (fun _ _ => False) (c + v) (o + v) := by
  induction h with
  | seed hs => exact False.elim hs
  | @unit a b c' o' inside hc hw ho hout hin hforced ih =>
    have hLx : ∀ x, laplacian G x = laplacian G (x - v) := by
      intro x
      have := hL (x - v)
      rw [sub_add_cancel] at this
      exact this
    refine ForcedEdge.unit (a := a + v.1) (b := b + v.2) (fun z => inside (z - v) + v) ?_ ?_ ?_ ?_ ?_ ?_
    · exact (mem_corners_translate a b v c').mpr hc
    · rw [hL]
      exact hw
    · rcases ho with rfl | rfl
      · left
        rw [FLatticePaper.Contacts.incomingNeg_add_even c' v hv]
      · right
        rw [FLatticePaper.Contacts.incomingPos_add_even c' v hv]
    · intro hmem
      exact hout ((mem_corners_translate a b v o').mp hmem)
    · intro x hx hne
      have hy : x - v ∈ squareCorners a b := (mem_corners_translate a b v (x - v)).mp (by rwa [sub_add_cancel])
      have hne' : x - v ≠ c' := fun e => hne (by rw [← e, sub_add_cancel])
      rw [hLx x]
      rcases hin (x - v) hy hne' with hb | ⟨hw', hin', hinp⟩
      · left
        exact hb
      · right
        refine ⟨hw', (mem_corners_translate a b v (inside (x - v))).mpr hin', ?_⟩
        rcases hinp with e | e
        · left
          show inside (x - v) + v = FLatticePaper.incomingNeg x
          rw [e, ← FLatticePaper.Contacts.incomingNeg_add_even (x - v) v hv, sub_add_cancel]
        · right
          show inside (x - v) + v = FLatticePaper.incomingPos x
          rw [e, ← FLatticePaper.Contacts.incomingPos_add_even (x - v) v hv, sub_add_cancel]
    · intro x hx hne hwx
      have hy : x - v ∈ squareCorners a b := (mem_corners_translate a b v (x - v)).mp (by rwa [sub_add_cancel])
      have hne' : x - v ≠ c' := fun e => hne (by rw [← e, sub_add_cancel])
      have hwy : laplacian G (x - v) = 0 := by rw [← hLx x]; exact hwx
      have := ih (x - v) hy hne' hwy
      rw [sub_add_cancel] at this
      exact this

/-- **The nonfree root condition in deck form.** A nonfree root of the old policy is black, or its retained edge is the unseeded forced
edge: the strict-interior translate carries `W1Forced` to the root, and the retained input is the forced target. -/
theorem nonfree_root_forced_nonfree {η : ℤ} {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : OldPolicyData frame G seed η) (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G) {z z' : Site}
    (hnf : Nonfree frame z) (hr : P.retained z z') :
    laplacian G z = -1 ∨ ForcedEdge G (fun _ _ => False) z z' := by
  rcases hP.binary z with hb | hw
  · exact Or.inl hb
  · right
    obtain ⟨v, hv, hSI⟩ := nonfree_bridge frame z hnf
    have hwv : laplacian G (z + v) = 0 := by
      rw [laplacian_span_inv frame G hP hv z]
      exact hw
    obtain ⟨o, ho⟩ := hW1 (z + v) hSI hwv
    have hf : ForcedEdge G (fun _ _ => False) (z + v) o := FLatticePaper.W1.forcedEdgeIn_forced ho
    have hnv : -v ∈ frame.child.modifiedDeck.span := span_neg_mem hv
    have hfz := forcedEdge_add G (evenSite_of_span frame hnv) (fun y => laplacian_span_inv frame G hP hnv y) hf
    rw [add_neg_cancel_right] at hfz
    have e := P.forcedWhiteUnique z z' hr hw (o + -v) hfz
    rw [e] at hfz
    exact hfz

end FLatticePaper.Induction
