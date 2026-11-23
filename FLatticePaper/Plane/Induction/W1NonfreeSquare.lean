import FLatticePaper.Plane.Induction.W1PrivateSquare
import FLatticePaper.Plane.Induction.W1MSheet
import FLatticePaper.Plane.Induction.DeckForced

/-! # Task 88: the parent square data at nonfree roots (the lead's nonfree hpar)

At a nonfree white parent point `z` (with `W1Forced`), the policy keeps an input `i` of `z` (quota), and `nonfree_root_forced_nonfree` makes
that retained edge a forced edge of the unseeded derivation. The top unit of that derivation is the three-step private square
(`parentSquare_of_forced`), so `ParentSquare P.retained z` holds. The policy's seed is empty (`oldPolicyData_of_canonical`), so its forced
edges are retained (`forcedRetained`) and its forced whites are unique (`forcedWhiteUnique`). -/

namespace FLatticePaper.W1NonfreeSquare

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.W1SheetSquare
open FLatticePaper.W1PrivateSquare FLatticePaper.W1MSheet

/-- **The parent square at a nonfree white root** (task 88). -/
theorem parentSquare_nonfree {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : OldPolicyData frame G seed) (hs : seed = fun _ _ => False) (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G) {z : Site}
    (hz : laplacian G z = 0) (hnf : Nonfree frame z) :
    ParentSquare P.retained z := by
  subst hs
  rcases P.quota.2 z hz with hr | hr
  · rcases nonfree_root_forced_nonfree P hP hW1 hnf hr with hb | hF
    · rw [hz] at hb
      norm_num at hb
    · exact parentSquare_of_forced P.quota P.forcedRetained P.forcedWhiteUnique hF
  · rcases nonfree_root_forced_nonfree P hP hW1 hnf hr with hb | hF
    · rw [hz] at hb
      norm_num at hb
    · exact parentSquare_of_forced P.quota P.forcedRetained P.forcedWhiteUnique hF

/-- The parent point of an `M`-white tie is white for the conjugate field (`laplacian_sub_even` and the quarter-turn identity). -/
theorem parent_white_of_mwhite (word : Word) (hbinF : ∀ x, laplacian (FqW word) x = -1 ∨ laplacian (FqW word) x = 0)
    (hlvE : EvenSite (frameAt word).sheetShift) (c : Site)
    (hM : laplacian (MW word) c = 0) (hT : (frameAt word).sheetC (FqW word) c = (frameAt word).sheetA (FqW word) c) :
    laplacian (standardField (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) = 0 := by
  have hA0 := FLatticePaper.W1TieInputs.lapA_zero_of_mwhite (frameAt word) (FqW word) hbinF c hM hT
  have e1 : laplacian ((frameAt word).sheetA (FqW word)) c =
      laplacian (FqW word) (c - (frameAt word).sheetShift) :=
    laplacian_sub_even (FqW word) (frameAt word).sheetShift hlvE c
  show laplacian (standardField (conjWord word)) (i3Z (c - (frameAt word).sheetShift)) = 0
  rw [← i3_laplacian_quarterTurn (standardField (conjWord word)) (c - (frameAt word).sheetShift), ← e1]
  exact hA0

end FLatticePaper.W1NonfreeSquare
