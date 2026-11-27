import FLatticePaper.Plane.Induction.FanRegion
import FLatticePaper.Plane.Induction.FanAcyclic
import FLatticePaper.Plane.Induction.RefuteTree
import FLatticePaper.Plane.Induction.AuxRankQ1
import FLatticePaper.Plane.Induction.NonfreeBridge

/-! # The fan refutation with empty core (Q41 §3, the Refuted form)

A contact fan of a rotated residual `f` (region `R`, cone of base `b` and depth `K`, `FanRegion.fanSet`) is refuted node by node:
an even node is white with its contacting east input, an odd white node with a contacting vertical input, an odd black node with both
vertical inputs. Every contacting input in the fan is refuted by the induction hypothesis (its fan rank is smaller, `fanRank`); every
contacting input outside the fan is an exit and is refuted by the table hypothesis `hexit`. The physical site of a fan node is `Y q`,
with `Y` preserving the edge relation exactly (`hexact`) and the laplacian (`hlapY`), and with nonfree image (`hnf`). -/

namespace FLatticePaper.HardVFanRefute

open FLatticePaper FLatticePaper.Induction FLatticePaper.ContactCone FLatticePaper.FanAcyclic FLatticePaper.FanPropagation
  FLatticePaper.FanRegion FLatticePaper.RefuteTree FLatticePaper.AuxRankQ1 FLatticePaper.CapRay

theorem not_freeClosure_of_nonfree {frame : ChildFrame} {c : Site} (h : Nonfree frame c) :
    ¬ FreeClosure.freeClosure frame c := by
  rintro ⟨s, hs, hfs⟩
  exact h s hs ((Set.mem_union _ _ _).2 hfs)

/-- **The fan refutation.** Every node of the contact fan is refuted (`Refuted`, core `C`), given the earlier entries `E` and the
exit table `hexit`. -/
theorem fan_refuted {frame : ChildFrame} {F f : Field} {η : ℤ}
    {E C : Site → Prop} {R : Site → Prop} {b : Site} {K : ℕ} (Y : Site → Site)
    (hbin : ∀ c, laplacian f c = -1 ∨ laplacian f c = 0)
    (hlapY : ∀ q, laplacian F (Y q) = laplacian f q)
    (hwin : WindowOn (fun x => R x ∧ ConeRoot b K x) f (fun i => parabolaField b.2 i))
    (hnf : ∀ q, q ∈ fanSet R f b K → Nonfree frame (Y q))
    (hexact : ∀ q, (Y (incomingNeg q) = incomingNeg (Y q) ∧ Y (incomingPos q) = incomingPos (Y q)) ∨
      (Y (incomingNeg q) = incomingPos (Y q) ∧ Y (incomingPos q) = incomingNeg (Y q)))
    (hexit : ∀ q, q ∈ fanSet R f b K → ∀ u, ((EvenSite q ∧ u = incomingPos q) ∨ (¬ EvenSite q ∧ Edge u q)) →
      f u = parabolaField b.2 u → u ∉ fanSet R f b K → Refuted frame F η E C (Y u))
    (hlo : ∃ lo : ℤ, ∀ q, q ∈ fanSet R f b K → lo ≤ fanRank q) :
    ∀ q, q ∈ fanSet R f b K → Refuted frame F η E C (Y q) := by
  obtain ⟨lo, hlo'⟩ := hlo
  have hedge : ∀ q u, Edge u q → Edge (Y u) (Y q) := by
    intro q u hu
    rcases hu with rfl | rfl
    · rcases hexact q with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
    · rcases hexact q with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact Or.inr h2
      · exact Or.inl h2
  suffices H : ∀ k : ℕ, ∀ q, q ∈ fanSet R f b K → fanRank q - lo < (k : ℤ) → Refuted frame F η E C (Y q) by
    intro q hq
    exact H ((fanRank q - lo).toNat + 1) q hq (by have := hlo' q hq; omega)
  intro k
  induction k with
  | zero =>
    intro q hq hk
    have := hlo' q hq
    push_cast at hk
    omega
  | succ k ih =>
    intro q hq hk
    have IHin : ∀ u, Edge u q → u ∈ fanSet R f b K → fanRank u < fanRank q → Refuted frame F η E C (Y u) := by
      intro u hu hus hr
      have := hlo' u hus
      exact ih u hus (by push_cast at hk; omega)
    have hnfq : ¬ FreeClosure.freeClosure frame (Y q) := not_freeClosure_of_nonfree (hnf q hq)
    by_cases hev : EvenSite q
    · -- even node: white, with its contacting east input
      have hw : laplacian f q = 0 := contact_even_white_R hbin hwin hq hev
      have hl : laplacian f q = laplacian (parabolaField b.2) q := by
        rw [hw, parabola_lap_even b.2 q hev]
      have hc := (fan_both_inputs_R hwin hq hl).2
      have hu : Edge (incomingPos q) q := Or.inr rfl
      have hlapY' : laplacian F (Y q) = 0 := by rw [hlapY q, hw]
      have hperm : permitsQ1 frame F η (Y q) (Y (incomingPos q)) :=
        Or.inr ⟨hlapY', Or.inr ⟨hnfq, hedge q _ hu⟩⟩
      by_cases hmem : incomingPos q ∈ fanSet R f b K
      · exact RefuteTree.Refuted.white hlapY' hperm
          (IHin _ hu hmem (fanRank_east_of_even q hev))
      · exact RefuteTree.Refuted.white hlapY' hperm
          (hexit q hq _ (Or.inl ⟨hev, rfl⟩) hc hmem)
    · -- odd node
      have hl0 := hbin q
      rcases hl0 with hneg | hzero
      · -- black: both vertical inputs are contacts
        have hl : laplacian f q = laplacian (parabolaField b.2) q := by
          rw [hneg, parabola_lap_odd b.2 q hev]
        obtain ⟨hcn, hcp⟩ := fan_both_inputs_R hwin hq hl
        have hRneg : Refuted frame F η E C (Y (incomingNeg q)) := by
          by_cases hmem : incomingNeg q ∈ fanSet R f b K
          · exact IHin _ (Or.inl rfl) hmem (fanRank_vertical_of_odd q hev _ (Or.inl rfl))
          · exact hexit q hq _ (Or.inr ⟨hev, Or.inl rfl⟩) hcn hmem
        have hRpos : Refuted frame F η E C (Y (incomingPos q)) := by
          by_cases hmem : incomingPos q ∈ fanSet R f b K
          · exact IHin _ (Or.inr rfl) hmem (fanRank_vertical_of_odd q hev _ (Or.inr rfl))
          · exact hexit q hq _ (Or.inr ⟨hev, Or.inr rfl⟩) hcp hmem
        have hlapY' : laplacian F (Y q) = -1 := by rw [hlapY q, hneg]
        rcases hexact q with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1] at hRneg
          rw [h2] at hRpos
          exact RefuteTree.Refuted.black hlapY' hRneg hRpos
        · rw [h2] at hRpos
          rw [h1] at hRneg
          exact RefuteTree.Refuted.black hlapY' hRpos hRneg
      · -- white: a contacting vertical input
        obtain ⟨u, hu, hcu⟩ := contact_odd_input_R hwin hq hev hzero
        have hlapY' : laplacian F (Y q) = 0 := by rw [hlapY q, hzero]
        have hperm : permitsQ1 frame F η (Y q) (Y u) :=
          Or.inr ⟨hlapY', Or.inr ⟨hnfq, hedge q u hu⟩⟩
        by_cases hmem : u ∈ fanSet R f b K
        · exact RefuteTree.Refuted.white hlapY' hperm
            (IHin u hu hmem (fanRank_vertical_of_odd q hev u hu))
        · exact RefuteTree.Refuted.white hlapY' hperm (hexit q hq u (Or.inr ⟨hev, hu⟩) hcu hmem)

end FLatticePaper.HardVFanRefute
