import FLatticePaper.Plane.Induction.FortAt
import FLatticePaper.Plane.Induction.RankFromForts
import FLatticePaper.Plane.Induction.AuxRankQ1
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.FreeClosure

/-! The restricted fort (RankFromForts, the Q1 game `permitsQ1`) gives the fort condition at nonfree sites (`FortAt`, FortAt.lean). -/

namespace FLatticePaper

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreeClosure

/-- **The restricted fort condition gives the fort condition at nonfree sites.** At a nonfree site `permitsQ1` permits both inputs
(a black keeps both, a white with no free closure keeps both edges), so a restricted fort keeps a member input at a black site and
both at a white site. -/
theorem fortAt_nonfree_of_restricted (frame : ChildFrame) (F : Field) (η : ℤ) {sites : Set Site}
    (h : IsRestrictedFort F (AuxRankQ1.permitsQ1 frame F η) sites) : FortAt (Nonfree frame) F sites := by
  intro site hs hnf
  have hclosed : ¬ freeClosure frame site := fun hc => by
    obtain ⟨v, hv, hmem⟩ := hc
    exact hnf v hv ((Set.mem_union _ _ _).mpr hmem)
  rcases h site hs with ⟨hl, hin⟩ | ⟨hl, hn, hp⟩
  · left
    refine ⟨hl, ?_⟩
    rcases hin with hn | hp
    · rcases hn with hn | hn
      · exact Or.inl hn
      · exact absurd (Or.inl ⟨hl, Or.inl rfl⟩ : AuxRankQ1.permitsQ1 frame F η site (incomingNeg site)) hn
    · rcases hp with hp | hp
      · exact Or.inr hp
      · exact absurd (Or.inl ⟨hl, Or.inr rfl⟩ : AuxRankQ1.permitsQ1 frame F η site (incomingPos site)) hp
  · right
    refine ⟨hl, ?_, ?_⟩
    · rcases hn with hn | hn
      · exact hn
      · exact absurd (Or.inr ⟨hl, Or.inr ⟨hclosed, Or.inl rfl⟩⟩ : AuxRankQ1.permitsQ1 frame F η site (incomingNeg site)) hn
    · rcases hp with hp | hp
      · exact hp
      · exact absurd (Or.inr ⟨hl, Or.inr ⟨hclosed, Or.inr rfl⟩⟩ : AuxRankQ1.permitsQ1 frame F η site (incomingPos site)) hp

end FLatticePaper
