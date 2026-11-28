import FLatticePaper.Tiles.MixedCompatWalks
import FLatticePaper.Tiles.SiteHullOdd
import FLatticePaper.Tiles.SiteHullEven

/-! The two mixed comparisons at every non-base word of length at most two. -/

namespace FLatticePaper.Tiles.MixedCompatFirstStep

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard SurgicalWeak SiteStrings SiteInduction JointFamily JointInduction
open ClosedPathAssembly ClosedPathCycle ChildGlue MixedPieces MixedOverlapStrings MixedCompatWalks MixedCompatEdges

private def marks (u : Word) (par : Bool) (C : Site) : List Site :=
  let h := stringSites false false (hWordOf u par)
  let v := (stringSites true true (vWordOf u par).reverse).map (fun z => (z.1-1, z.2-1))
  h ++ v ++ h.map (C-·) ++ v.map (C-·)

private theorem simplify_marks (T : Finset Site) (u : Word) (par : Bool) (C : Site)
    (h0 : lowLeft T = (0,0)) (hc : halfTurnCentre T = C) :
    markedSites T (hWordOf u par) (vWordOf u par) = marks u par C := by
  have ht : halfTurn T = fun z => C-z := by
    funext z
    change ((halfTurnCentre T).1-z.1, (halfTurnCentre T).2-z.2) = C-z
    rw [hc]
    rfl
  simp [markedSites, marks, h0, ht, Function.comp_def]

private abbrev oddMarks (u : Word) := marks u false
  ((curO u).den+(curO u).num+1, 3*(curO u).num+(curO u).den-1)
private abbrev evenMarks (v : Word) := marks v true
  ((curE v).num+1, 2*(curE v).num+(curE v).den-1)

private theorem odd_mem {z : Site} {u : Word} (h : z ∈ marksOdd u) : z ∈ oddMarks u := by
  change z ∈ markedSites (oddTile u) _ _ at h
  rwa [simplify_marks _ u false _ (SiteLowLeft.lowLeft_oddTile _) (SiteHullOdd.centre_odd _)] at h
private theorem even_mem {z : Site} {u : Word} (h : z ∈ marksEven u) : z ∈ evenMarks u := by
  change z ∈ markedSites (evenTile u) _ _ at h
  rwa [simplify_marks _ u true _ (SiteLowLeft.lowLeft_evenTile _) (SiteHullEven.centre_even _)] at h

private instance (w wr : BinaryWord) (X Y : Site) (s : Side) (z : Site) : Decidable (edge w wr X Y s z) := by
  cases s <;> unfold edge <;> infer_instance

private instance (w u v : Word) (p q : Site) (s : Side) (z : Site) : Decidable (parentWalkPair w u v p q s z) := by
  unfold parentWalkPair
  infer_instance

private def checks (w u v : Word) (p q : Site) (s : Side) : Prop :=
  ∀ x ∈ oddMarks u, x+p-q ∈ evenMarks v → parentWalkPair w u v p q s (x+p)

private instance (w u v : Word) (p q : Site) (s : Side) : Decidable (checks w u v p q s) := by
  unfold checks
  infer_instance

private def allChecks (w u v : Word) : Prop :=
  (∀ (i : Fin 2) (j : Fin 4), checks w u v ((oddP w).getD i 0) ((oddQ w).getD j 0)
      (stringSide (chooseOdd (phase w == 1) i j).1)) ∧
  (∀ (i : Fin 4) (j : Fin 2), checks w u v ((evenP w).getD i 0) ((evenQ w).getD j 0)
      (stringSide (chooseEven (phase w == 1) i j).1))

private instance (w u v : Word) : Decidable (allChecks w u v) := by unfold allChecks; infer_instance

private theorem at_pair {w u v : Word} {p q : Site} {s : Side} {z : Site} (hc : checks w u v p q s)
    (hp : z ∈ shiftS (marksOdd u) p) (hq : z ∈ shiftS (marksEven v) q) : parentWalkPair w u v p q s z := by
  obtain ⟨x, hx, rfl⟩ := hp
  exact hc x (odd_mem hx) (even_mem (sub_mem_of_shift _ _ _ hq))

private theorem walks {w u v : Word} (hc : allChecks w u v) : OnParentWalks w u v := by
  constructor
  · intro i j z h₁ h₂
    simp only [mOdd, pieceSet, oddP_length, if_pos i.isLt, if_neg (by omega : ¬ j.val+2 < 2),
      Nat.add_sub_cancel] at h₁ h₂
    exact at_pair (hc.1 i j) h₁ h₂
  · intro i j z h₁ h₂
    simp only [mEven, pieceSet, evenP_length, if_pos i.isLt, if_neg (by omega : ¬ j.val+4 < 4),
      Nat.add_sub_cancel] at h₁ h₂
    exact at_pair (hc.2 i j) h₁ h₂

set_option maxRecDepth 8192 in
set_option maxHeartbeats 400000 in
/-- The first non-base prefix, at all three successors, with the actual parent odometers. -/
theorem after_one (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (d : Digit) (u v : Word) (hg : GoodBelow D f [Digit.one,d].length)
    (hr : regsAt [.one,d] = (some u, some v)) :
    MixedCompatOdd [.one,d] u v (placedOdd [.one,d] (f u).tOdd.val (f v).tEven.val 0) ∧
    MixedCompatEven [.one,d] u v (placedEven [.one,d] (f u).tOdd.val (f v).tEven.val 0) := by
  apply mixed_of_walks D f _ u v hS hA hg hr
  apply walks
  cases d <;> simp only [regsAt, regRun, regStep, Option.some.injEq, Prod.mk.injEq] at hr
  all_goals obtain ⟨rfl,rfl⟩ := hr
  all_goals decide +kernel

/-- Both standard children in the joint induction at every non-base word of length at most two. -/
theorem mixed_length_two (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (w u v : Word) (hg : GoodBelow D f w.length) (hw : ¬ IsBase w)
    (hr : regsAt w = (some u, some v)) (h₂ : w.length ≤ 2) :
    MixedCompatOdd w u v (placedOdd w (f u).tOdd.val (f v).tEven.val 0) ∧
    MixedCompatEven w u v (placedEven w (f u).tOdd.val (f v).tEven.val 0) := by
  by_cases hb : IsBase w.dropLast
  · exact MixedCompatBaseStep.mixed_at_base_prefix D hS f w u v hg hw hr hb
  obtain ⟨d, rfl⟩ : ∃ d : Digit, w = [.one,d] := by
    match w with
    | [] => exact (hb (Or.inl rfl)).elim
    | [_] => exact (hb (Or.inl rfl)).elim
    | [a,b] =>
      cases a
      · exact ⟨b,rfl⟩
      · exact (hb (Or.inr (Or.inr (by simp)))).elim
      · exact (hb (Or.inr (Or.inl (by simp)))).elim
    | _ :: _ :: _ :: _ => simp at h₂
  exact after_one D hS hA f d u v hg hr

end FLatticePaper.Tiles.MixedCompatFirstStep
