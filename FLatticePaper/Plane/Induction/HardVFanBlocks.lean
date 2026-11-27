import FLatticePaper.Plane.Induction.HardVFanRefute
import FLatticePaper.Plane.Induction.RotatedForced
import FLatticePaper.Plane.Induction.StrictNonfree
import FLatticePaper.Plane.Induction.PassageRank
import FLatticePaper.Plane.Induction.FanTerminal
import FLatticePaper.Plane.Induction.EasyHRank
import FLatticePaper.Plane.Induction.W1Exit

/-! # The minus-prefix block of the hard V fan (Q41 sections 3 and 4, block 1)

The physical map of the minus prefix is the identity on the block, so the fan node `q` sits at the physical site `Zs q`. This module
proves the three facts `HardVFanRefute.fan_refuted` needs for this block: the parity correspondence of the two inputs (`Zs_exact`),
the nonfreeness of the fan nodes (`nonfree_Zs`), and the finiteness of the fan region (`resRegion_finite`). It then instantiates the
fan refutation; the exit table `hexit` stays a hypothesis. -/

namespace FLatticePaper.HardVFanBlocks

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.ContactCone FLatticePaper.FanAcyclic FLatticePaper.FanPropagation
  FLatticePaper.FanRegion FLatticePaper.RefuteTree FLatticePaper.AuxRankQ1 FLatticePaper.RotatedCap FLatticePaper.RotatedForced
  FLatticePaper.HardVFanRefute FLatticePaper.CapRay

theorem zs_inputs (q : Site) :
    (Zs (incomingNeg q) = incomingNeg (Zs q) ∧ Zs (incomingPos q) = incomingPos (Zs q)) ∨
    (Zs (incomingNeg q) = incomingPos (Zs q) ∧ Zs (incomingPos q) = incomingNeg (Zs q)) := by
  by_cases hq : EvenSite q
  · left
    have h1 : ¬ EvenSite (Zs q) := by
      unfold EvenSite at hq ⊢
      simp only [Zs] at ⊢
      omega
    unfold incomingNeg incomingPos
    simp only [if_pos hq, if_neg h1]
    refine ⟨Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩ <;> simp [Zs]
  · right
    have h1 : EvenSite (Zs q) := by
      unfold EvenSite at hq ⊢
      simp only [Zs] at ⊢
      omega
    unfold incomingNeg incomingPos
    simp only [if_neg hq, if_pos h1]
    refine ⟨Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩ <;> simp [Zs]
    all_goals ring

theorem resRegion_eq_openRect (frame : ChildFrame) (q : Site) :
    resRegion frame.child.num frame.child.den q ↔ frame.openRect (Zs q + RowAt.Uvec frame) := by
  rw [W1Exit.openRect_iff]
  unfold resRegion
  have e : Zs q + RowAt.Uvec frame = (-q.2 + frame.child.den, q.1 - 1 + frame.child.num) := by
    unfold Zs RowAt.Uvec
    ext <;> simp
  rw [e]

theorem nonfree_Zs {frame : ChildFrame} {q : Site} (hq : resRegion frame.child.num frame.child.den q) :
    Nonfree frame (Zs q) := by
  have hSI : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den (Zs q + RowAt.Uvec frame) :=
    (W1Exit.openRect_iff frame _).mp ((resRegion_eq_openRect frame q).mp hq)
  have hnf := FLatticePaper.Induction.strictInterior_nonfree frame hSI
  have hcomb : frame.child.modifiedDeck.combine (-1) 0 = -RowAt.Uvec frame := by
    rw [← EasyHRank.combine_one_zero_eq_Uvec frame]
    ext <;> simp [PeriodDeck.combine]
  have hmem : -RowAt.Uvec frame ∈ frame.child.modifiedDeck.span := ⟨-1, 0, hcomb.symm⟩
  have h := FLatticePaper.PassageRank.nonfree_add_span frame hnf hmem
  rwa [add_neg_cancel_right] at h

theorem resRegion_finite (frame : ChildFrame) :
    {q : Site | resRegion frame.child.num frame.child.den q}.Finite := by
  have hinj : Set.InjOn (fun q : Site => Zs q + RowAt.Uvec frame)
      ((fun q : Site => Zs q + RowAt.Uvec frame) ⁻¹' {c : Site | frame.openRect c}) := by
    intro a _ b _ hab
    have h2 : Zs a = Zs b := add_right_cancel hab
    unfold Zs at h2
    ext
    · have := congrArg Prod.snd h2
      simp at this
      linarith
    · have := congrArg Prod.fst h2
      simp at this
      linarith
  have hpre : (fun q : Site => Zs q + RowAt.Uvec frame) ⁻¹' {c : Site | frame.openRect c} =
      {q : Site | resRegion frame.child.num frame.child.den q} := by
    ext q
    exact (resRegion_eq_openRect frame q).symm
  rw [← hpre]
  exact (FanTerminal.openRect_finite frame).preimage hinj

theorem fanRank_lower_of_finite {R : Site → Prop} (hR : {q : Site | R q}.Finite) :
    ∃ lo : ℤ, ∀ q, R q → lo ≤ fanRank q := by
  obtain ⟨lo, hlo⟩ := (hR.image fanRank).bddBelow
  exact ⟨lo, fun q hq => hlo ⟨q, hq, rfl⟩⟩

/-- **The minus-prefix block: every node of the rotated fan is refuted.** -/
theorem minus_prefix_refuted (frame : ChildFrame) (F : Field) {η : ℤ} (hP : frame.Packet F) {b : Site} {K : ℕ}
    {E C : Site → Prop}
    (hwin : WindowOn (fun x => resRegion frame.child.num frame.child.den x ∧ ConeRoot b K x)
      (quarterTurnField F) (fun i => parabolaField b.2 i))
    (hexit : ∀ q, q ∈ fanSet (resRegion frame.child.num frame.child.den) (quarterTurnField F) b K →
      ∀ u, ((EvenSite q ∧ u = incomingPos q) ∨ (¬ EvenSite q ∧ Edge u q)) →
        quarterTurnField F u = parabolaField b.2 u →
        u ∉ fanSet (resRegion frame.child.num frame.child.den) (quarterTurnField F) b K →
        Refuted frame F η E C (Zs u)) :
    ∀ q, q ∈ fanSet (resRegion frame.child.num frame.child.den) (quarterTurnField F) b K →
      Refuted frame F η E C (Zs q) := by
  have hbin : ∀ c, laplacian (quarterTurnField F) c = -1 ∨ laplacian (quarterTurnField F) c = 0 := by
    intro c
    rw [laplacian_quarterTurnField]
    exact hP.binary _
  have hlapY : ∀ q, laplacian F (Zs q) = laplacian (quarterTurnField F) q := fun q =>
    (laplacian_quarterTurnField F q).symm
  have hnf : ∀ q, q ∈ fanSet (resRegion frame.child.num frame.child.den) (quarterTurnField F) b K →
      Nonfree frame (Zs q) := fun q hq => nonfree_Zs hq.1.1
  have hlo : ∃ lo : ℤ, ∀ q, q ∈ fanSet (resRegion frame.child.num frame.child.den) (quarterTurnField F) b K →
      lo ≤ fanRank q :=
    fanRank_lower_of_finite (R := resRegion frame.child.num frame.child.den) (resRegion_finite frame)
      |> fun h => by
        obtain ⟨lo, hlo⟩ := h
        exact ⟨lo, fun q hq => hlo q hq.1.1⟩
  exact fan_refuted (η := η) (E := E) (C := C) (Y := Zs) hbin hlapY hwin hnf zs_inputs hexit hlo

end FLatticePaper.HardVFanBlocks
