import FLatticePaper.Plane.Induction.W1Hagree
import FLatticePaper.Plane.Induction.DeckForced

/-! # Task 81 (hagree, nonfree roots): the common arrow at a nonfree sheet root

For a sheet point `c` whose parent root `z = Z (c − lv)` is NONFREE, the A pointer `pointerOf (sheetPolicyA P lv) c` is retained by the
C policy:

* `zTurn_neighbors`: with an even sheet shift `lv`, the parent image of each sheet input of `c` is a parent input of `z`
  (`incomingNeg` and `incomingPos` swap when `c` is odd);
* `sheetPolicyA_pointer_retained`: the A policy retains its pointer, from the parent quota at `z` (both inputs at a black root, one at a
  white root);
* `hagree_at_nonfree_root`: the parent edge of the pointer is black or forced (`nonfree_root_forced_nonfree`), so the reflection
  `sheetPolicyC_of_sheetPolicyA` gives the C retention.

The free roots (`¬ Nonfree`) are NOT covered here: their common arrow needs the collar squares or the descent of the note. -/

namespace FLatticePaper.W1HagreeNonfree

open Farey FLatticePaper FLatticePaper.Induction

/-- With an even sheet shift `lv`, the parent image of each sheet input of `c` is a parent input of `Z (c − lv)`. -/
theorem zTurn_neighbors (c lv : Site) (hlv : EvenSite lv) :
    (EvenSite c → zTurn (incomingNeg c - lv) = incomingNeg (zTurn (c - lv)) ∧
      zTurn (incomingPos c - lv) = incomingPos (zTurn (c - lv))) ∧
    (¬ EvenSite c → zTurn (incomingNeg c - lv) = incomingPos (zTurn (c - lv)) ∧
      zTurn (incomingPos c - lv) = incomingNeg (zTurn (c - lv))) := by
  obtain ⟨c1, c2⟩ := c
  obtain ⟨l1, l2⟩ := lv
  constructor
  · intro hc
    simp only [EvenSite, incomingNeg, incomingPos, zTurn, Prod.mk_sub_mk] at hc hlv ⊢
    split_ifs at hc hlv ⊢ <;> simp only [Prod.mk_sub_mk, Prod.mk.injEq, true_and] <;> repeat' apply And.intro <;> omega
  · intro hc
    simp only [EvenSite, incomingNeg, incomingPos, zTurn, Prod.mk_sub_mk] at hc hlv ⊢
    split_ifs at hc hlv ⊢ <;> simp only [Prod.mk_sub_mk, Prod.mk.injEq, and_true] <;> repeat' apply And.intro <;> omega

/-- **The A policy retains its pointer** (task 81): at a sheet point whose parent point is binary, the A policy retains
`pointerOf (sheetPolicyA P lv) c`. The quota at the parent root supplies one retained input (both at a black root), and the parent
correspondence of `zTurn_neighbors` transports it to the sheet inputs. -/
theorem sheetPolicyA_pointer_retained {η : ℤ} {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : OldPolicyData frame G seed η) (hbin : ∀ z, laplacian G z = -1 ∨ laplacian G z = 0) (lv : Site)
    (hlv : EvenSite lv) (c : Site) :
    sheetPolicyA P lv c (FLatticePaper.W1Pointers.pointerOf (sheetPolicyA P lv) c) := by
  obtain ⟨hq1, hq0⟩ := P.quota
  have hn := zTurn_neighbors c lv hlv
  unfold FLatticePaper.W1Pointers.pointerOf
  classical
  split_ifs with h
  · exact h
  · by_cases hc : EvenSite c
    · have hA : ¬ P.retained (zTurn (c - lv)) (zTurn (incomingNeg c - lv)) := by
        exact h
      rw [(hn.1 hc).1] at hA
      show P.retained (zTurn (c - lv)) (zTurn (incomingPos c - lv))
      rw [(hn.1 hc).2]
      rcases hbin (zTurn (c - lv)) with hl | hl
      · exact (hq1 _ hl).2
      · rcases hq0 _ hl with h1 | h1
        · exact absurd h1 hA
        · exact h1
    · have hA : ¬ P.retained (zTurn (c - lv)) (zTurn (incomingNeg c - lv)) := by
        exact h
      rw [(hn.2 hc).1] at hA
      show P.retained (zTurn (c - lv)) (zTurn (incomingPos c - lv))
      rw [(hn.2 hc).2]
      rcases hbin (zTurn (c - lv)) with hl | hl
      · exact (hq1 _ hl).1
      · rcases hq0 _ hl with h1 | h1
        · exact h1
        · exact absurd h1 hA

/-- **The common arrow at a nonfree sheet root** (task 81, partial hagree): the C policy retains the A pointer at every sheet point whose
parent root `Z (c − lv)` is nonfree, by the reflection of the policy (the parent edge of the pointer is black or forced). -/
theorem hagree_at_nonfree_root {η : ℤ} {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : OldPolicyData frame G seed η) (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G) (lv c : Site) (hlv : EvenSite lv)
    (hnf : Nonfree frame (zTurn (c - lv))) :
    sheetPolicyC P lv (reflectionI + lv + lv) c (FLatticePaper.W1Pointers.pointerOf (sheetPolicyA P lv) c) := by
  have hA := sheetPolicyA_pointer_retained P hP.binary lv hlv c
  have hroot := nonfree_root_forced_nonfree P hP hW1 hnf (z' := zTurn (FLatticePaper.W1Pointers.pointerOf
    (sheetPolicyA P lv) c - lv)) hA
  exact FLatticePaper.W1Hagree.sheetPolicyC_of_sheetPolicyA P lv c _ hroot hA

end FLatticePaper.W1HagreeNonfree
