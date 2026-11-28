import FLatticePaper.Tiles.GlueWords
import FLatticePaper.Tiles.GlueStringDecomp
import FLatticePaper.Tiles.RegisterLink
import FLatticePaper.Tiles.AltRotStep
import FLatticePaper.Tiles.BaseVertPiece
import FLatticePaper.Tiles.ReflectedCover
import FLatticePaper.Tiles.VerticalStepOne
import FLatticePaper.Tiles.BaseTileProps
import FLatticePaper.Tiles.BaseInvariant

/-! # The cells of the special prefixes (towards `JointRot.SpecialCells`)

The words `2^j 3^k` and `3^j 2^k` (`j ≥ 1`) carry the L-corrections at the special prefixes. This file collects what the cell facts
of `JointRot.SpecialCells` need about their children: the first two and the last two letters of their horizontal and vertical
boundary words (`ends_twos_threes`, `ends_threes_twos`), from the base words of `2^j`, `3^j` (`RegisterLink.quad_twos`,
`quad_threes`) and the child words of the registers (`GlueWords.hWordOf_child`, `vWordOf_child`). -/

namespace FLatticePaper.Tiles.SpecialCells

open FLatticePaper.Farey
open FLatticePaper.Tiles
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.SurgicalWeak (regsAt WeakData regOdo)
open FLatticePaper.Tiles.Standard (swapW)

/-- The word starts with the letters `a b`. -/
def HeadTwo (w : BinaryWord) (a b : Letter) : Prop := ∃ r, w = a :: b :: r

/-- The word ends with the letters `a b`. -/
def LastTwo (w : BinaryWord) (a b : Letter) : Prop := ∃ r, w = r ++ [a, b]

theorem HeadTwo.append {A : BinaryWord} {a b : Letter} (h : HeadTwo A a b) (B : BinaryWord) : HeadTwo (A ++ B) a b := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨r ++ B, rfl⟩

theorem LastTwo.append {B : BinaryWord} {a b : Letter} (h : LastTwo B a b) (A : BinaryWord) : LastTwo (A ++ B) a b := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨A ++ r, by simp⟩

theorem headTwo_replicate (n : ℕ) (a : Letter) (B : BinaryWord) :
    HeadTwo (List.replicate (n + 2) a ++ B) a a := ⟨List.replicate n a ++ B, by simp [List.replicate_succ]⟩

theorem lastTwo_replicate (n : ℕ) (a b : Letter) (A : BinaryWord) :
    LastTwo (A ++ List.replicate (n + 1) a ++ [b]) a b :=
  ⟨A ++ List.replicate n a, by simp [List.replicate_succ', List.append_assoc]⟩

/-! ### The base words -/

theorem hWord_two_false (k : ℕ) : hWordOf (List.replicate k Digit.two) false = List.replicate (2 * k + 2) Letter.q ++ [Letter.p] := by
  simp only [hWordOf, Bool.false_eq_true, ↓reduceIte]; exact (RegisterLink.quad_twos k).1

theorem hWord_two_true (k : ℕ) : hWordOf (List.replicate k Digit.two) true = List.replicate (2 * k + 1) Letter.q ++ [Letter.p] := by
  simp only [hWordOf, ↓reduceIte]; exact (RegisterLink.quad_twos k).2.1

theorem hWord_three_false (k : ℕ) : hWordOf (List.replicate k Digit.three) false =
    [Letter.q] ++ List.replicate k Letter.p ++ [Letter.q] ++ List.replicate (k + 1) Letter.p := by
  simp only [hWordOf, Bool.false_eq_true, ↓reduceIte]; exact (RegisterLink.quad_threes k).1

theorem hWord_three_true (k : ℕ) : hWordOf (List.replicate k Digit.three) true = [Letter.q] ++ List.replicate (k + 1) Letter.p := by
  simp only [hWordOf, ↓reduceIte]; exact (RegisterLink.quad_threes k).2.1

theorem vWord_two_false (k : ℕ) : vWordOf (List.replicate k Digit.two) false = [Letter.p] ++ List.replicate (k + 1) Letter.q := by
  unfold vWordOf
  rw [AltRotStep.swapW_replicate_two, if_neg Bool.false_ne_true, (RegisterLink.quad_threes k).2.1]
  simp [swapLetter, List.map_replicate]

theorem vWord_two_true (k : ℕ) : vWordOf (List.replicate k Digit.two) true =
    [Letter.p] ++ List.replicate k Letter.q ++ [Letter.p] ++ List.replicate (k + 1) Letter.q := by
  unfold vWordOf
  rw [AltRotStep.swapW_replicate_two, if_pos rfl, (RegisterLink.quad_threes k).1]
  simp [swapLetter, List.map_replicate]

theorem vWord_three_false (k : ℕ) : vWordOf (List.replicate k Digit.three) false = List.replicate (2 * k + 1) Letter.p ++ [Letter.q] :=
  BaseVertPiece.vWordOf_three_false k

theorem vWord_three_true (k : ℕ) : vWordOf (List.replicate k Digit.three) true = List.replicate (2 * k + 2) Letter.p ++ [Letter.q] := by
  unfold vWordOf
  rw [AltRotStep.swapW_replicate_three, if_pos rfl, (RegisterLink.quad_twos k).1]
  simp [swapLetter, List.map_replicate]

/-! ### The special words -/

theorem regs_twos_threes (j k : ℕ) :
    regsAt (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) =
      (some (List.replicate j Digit.two),
        (regsAt (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)).2) := by
  induction k with
  | zero =>
    rw [List.replicate_zero, List.append_nil, List.replicate_succ', JointRot.regsAt_append_singleton]
    rfl
  | succ k ih =>
    rw [show List.replicate (k + 1) Digit.three = List.replicate k Digit.three ++ [Digit.three] from List.replicate_succ' ..,
      ← List.append_assoc, JointRot.regsAt_append_singleton]
    simp only [SurgicalWeak.regStep]
    rw [ih]

theorem regs_threes_twos (j k : ℕ) :
    regsAt (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) =
      ((regsAt (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two)).1,
        some (List.replicate j Digit.three)) := by
  induction k with
  | zero =>
    rw [List.replicate_zero, List.append_nil, List.replicate_succ', JointRot.regsAt_append_singleton]
    rfl
  | succ k ih =>
    rw [show List.replicate (k + 1) Digit.two = List.replicate k Digit.two ++ [Digit.two] from List.replicate_succ' ..,
      ← List.append_assoc, JointRot.regsAt_append_singleton]
    simp only [SurgicalWeak.regStep]
    rw [ih]

theorem count_one_twos_threes (a b : ℕ) (d e : Digit) (hd : d ≠ Digit.one) (he : e ≠ Digit.one) :
    (List.replicate a d ++ List.replicate b e).count Digit.one = 0 := by
  simp [List.count_replicate, hd, he]

/-- The end letters of the boundary words of the children of `2^(j+1) 3^k`: `h = q q ... q p`, `v = p q ... q q`. -/
theorem ends_twos_threes (j k : ℕ) :
    HeadTwo (hWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false) .q .q ∧
    LastTwo (hWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false) .q .p ∧
    HeadTwo (hWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true) .q .q ∧
    LastTwo (hWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true) .q .p ∧
    HeadTwo (vWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false) .p .q ∧
    LastTwo (vWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false) .q .q ∧
    HeadTwo (vWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true) .p .q ∧
    LastTwo (vWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true) .q .q := by
  induction k with
  | zero =>
    simp only [List.replicate_zero, List.append_nil]
    rw [hWord_two_false, hWord_two_true, vWord_two_false, vWord_two_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨List.replicate (2 * j + 2) Letter.q ++ [Letter.p], by simp [List.replicate_succ, Nat.mul_succ]⟩
    · exact ⟨List.replicate (2 * j + 3) Letter.q, by simp [List.replicate_succ', Nat.mul_succ]⟩
    · exact ⟨List.replicate (2 * j + 1) Letter.q ++ [Letter.p], by simp [List.replicate_succ, Nat.mul_succ]⟩
    · exact ⟨List.replicate (2 * j + 2) Letter.q, by simp [List.replicate_succ', Nat.mul_succ]⟩
    · exact ⟨List.replicate (j + 1) Letter.q, by simp [List.replicate_succ]⟩
    · exact ⟨[Letter.p] ++ List.replicate j Letter.q, by simp [List.replicate_succ']⟩
    · exact ⟨List.replicate j Letter.q ++ [Letter.p] ++ List.replicate (j + 2) Letter.q, by simp [List.replicate_succ]⟩
    · exact ⟨[Letter.p] ++ List.replicate (j + 1) Letter.q ++ [Letter.p] ++ List.replicate j Letter.q,
        by simp [List.replicate_succ']⟩
  | succ k ih =>
    obtain ⟨-, -, h3, -, -, -, -, h8⟩ := ih
    set w := List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three with hw
    have hw' : List.replicate (j + 1) Digit.two ++ List.replicate (k + 1) Digit.three = w ++ [Digit.three] := by
      rw [hw, List.append_assoc, ← List.replicate_succ']
    rw [hw']
    have hreg : regsAt (w ++ [Digit.three]) = (some (List.replicate j Digit.two), some w) := by
      have := regs_twos_threes j (k + 1)
      rw [hw'] at this
      rw [this, JointRot.regsAt_append_singleton]
      rfl
    have hc : (w ++ [Digit.three]).count Digit.one % 2 = 0 := by
      rw [← hw', count_one_twos_threes _ _ _ _ (by decide) (by decide)]
    obtain ⟨hh1, hh2⟩ := GlueWords.hWordOf_child _ _ _ hreg
    obtain ⟨hv1, hv2⟩ := GlueWords.vWordOf_child _ _ _ hreg
    simp only [childWords, if_pos hc] at hh1 hh2 hv1 hv2
    rw [hh1, hh2, hv1, hv2]
    have hpw : LastTwo (hWordOf (List.replicate j Digit.two) false) .q .p := by
      rw [hWord_two_false]; exact ⟨List.replicate (2 * j + 1) Letter.q, by simp [List.replicate_succ']⟩
    have hvw : HeadTwo (vWordOf (List.replicate j Digit.two) false) .p .q := by
      rw [vWord_two_false]; exact ⟨List.replicate j Letter.q, by simp [List.replicate_succ]⟩
    refine ⟨?_, hpw.append _, h3.append _, hpw.append _, hvw.append _, h8.append _, ?_, h8.append _⟩
    · rw [List.append_assoc]; exact h3.append _
    · rw [List.append_assoc]; exact hvw.append _

/-- The end letters of the boundary words of the children of `3^(j+1) 2^k`: `h = q p ... p p`, `v = p p ... p q`. -/
theorem ends_threes_twos (j k : ℕ) :
    HeadTwo (hWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false) .q .p ∧
    LastTwo (hWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false) .p .p ∧
    HeadTwo (hWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) true) .q .p ∧
    LastTwo (hWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) true) .p .p ∧
    HeadTwo (vWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false) .p .p ∧
    LastTwo (vWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false) .p .q ∧
    HeadTwo (vWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) true) .p .p ∧
    LastTwo (vWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) true) .p .q := by
  induction k with
  | zero =>
    simp only [List.replicate_zero, List.append_nil]
    rw [hWord_three_false, hWord_three_true, vWord_three_false, vWord_three_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨List.replicate j Letter.p ++ [Letter.q] ++ List.replicate (j + 2) Letter.p, by simp [List.replicate_succ]⟩
    · exact ⟨[Letter.q] ++ List.replicate (j + 1) Letter.p ++ [Letter.q] ++ List.replicate j Letter.p,
        by simp [List.replicate_succ']⟩
    · exact ⟨List.replicate (j + 1) Letter.p, by simp [List.replicate_succ]⟩
    · exact ⟨[Letter.q] ++ List.replicate j Letter.p, by simp [List.replicate_succ']⟩
    · exact ⟨List.replicate (2 * j + 1) Letter.p ++ [Letter.q], by simp [List.replicate_succ, Nat.mul_succ]⟩
    · exact ⟨List.replicate (2 * j + 2) Letter.p, by simp [List.replicate_succ', Nat.mul_succ]⟩
    · exact ⟨List.replicate (2 * j + 2) Letter.p ++ [Letter.q], by simp [List.replicate_succ, Nat.mul_succ]⟩
    · exact ⟨List.replicate (2 * j + 3) Letter.p, by simp [List.replicate_succ', Nat.mul_succ]⟩
  | succ k ih =>
    obtain ⟨-, h2, -, -, h5, -, -, -⟩ := ih
    set w := List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two with hw
    have hw' : List.replicate (j + 1) Digit.three ++ List.replicate (k + 1) Digit.two = w ++ [Digit.two] := by
      rw [hw, List.append_assoc, ← List.replicate_succ']
    rw [hw']
    have hreg : regsAt (w ++ [Digit.two]) = (some w, some (List.replicate j Digit.three)) := by
      have := regs_threes_twos j (k + 1)
      rw [hw'] at this
      rw [this, JointRot.regsAt_append_singleton]
      rfl
    have hc : (w ++ [Digit.two]).count Digit.one % 2 = 0 := by
      rw [← hw', count_one_twos_threes _ _ _ _ (by decide) (by decide)]
    obtain ⟨hh1, hh2⟩ := GlueWords.hWordOf_child _ _ _ hreg
    obtain ⟨hv1, hv2⟩ := GlueWords.vWordOf_child _ _ _ hreg
    simp only [childWords, if_pos hc] at hh1 hh2 hv1 hv2
    rw [hh1, hh2, hv1, hv2]
    have hqw : HeadTwo (hWordOf (List.replicate j Digit.three) true) .q .p := by
      rw [hWord_three_true]; exact ⟨List.replicate j Letter.p, by simp [List.replicate_succ]⟩
    have hvq : LastTwo (vWordOf (List.replicate j Digit.three) true) .p .q := by
      rw [vWord_three_true]; exact ⟨List.replicate (2 * j + 1) Letter.p, by simp [List.replicate_succ']⟩
    refine ⟨?_, h2.append _, hqw.append _, h2.append _, h5.append _, hvq.append _, ?_, hvq.append _⟩
    · rw [List.append_assoc]; exact hqw.append _
    · rw [List.append_assoc]; exact h5.append _

/-! ### The end tiles of the four strings -/

open FLatticePaper.Tiles.HBottom (zTileOf)
open FLatticePaper.Tiles.ReflectedCover (fwdTiles revTiles fwdTiles_cons fwdTiles_head fwdTiles_single fwdTiles_append
  revTiles_cons2 revTiles_head revTiles_single lastPos_cons_of_ne lastPos_append_single)

/-- The first two tiles of a forward horizontal string. -/
theorem hStr_head (a b : Letter) (r : BinaryWord) (c : GInt) :
    (zTileOf none a, c) ∈ hStringAt (a :: b :: r) c ∧ (zTileOf (some a) b, c + hOffset b) ∈ hStringAt (a :: b :: r) c := by
  show (zTileOf none a, c) ∈ fwdTiles none (a :: b :: r) c ∧ (zTileOf (some a) b, c + hOffset b) ∈ fwdTiles none (a :: b :: r) c
  rw [fwdTiles_cons]
  obtain ⟨rest, hrest⟩ := fwdTiles_head (some a) b r (c + hOffset b)
  rw [hrest]
  simp

/-- The last two tiles of a forward horizontal string: the last at `lastPos`, the one before at `lastPos - hOffset b` (its tile
`zTileOf _ a`, which contains `T_{1/1}` for `a = q` and is `T_{0/1}` for `a = p`). -/
theorem hStr_last (r : BinaryWord) (a b : Letter) (c : GInt) :
    (zTileOf (some a) b, lastPosOf (hStringAt (r ++ [a, b]) c)) ∈ hStringAt (r ++ [a, b]) c ∧
      ∃ pr, (zTileOf pr a, lastPosOf (hStringAt (r ++ [a, b]) c) - hOffset b) ∈ hStringAt (r ++ [a, b]) c := by
  show (zTileOf (some a) b, lastPosOf (fwdTiles none (r ++ [a, b]) c)) ∈ fwdTiles none (r ++ [a, b]) c ∧
    ∃ pr, (zTileOf pr a, lastPosOf (fwdTiles none (r ++ [a, b]) c) - hOffset b) ∈ fwdTiles none (r ++ [a, b]) c
  have e : r ++ [a, b] = (r ++ [a]) ++ [b] := by simp
  rw [e, fwdTiles_append (r ++ [a]) none c b (by simp), lastPos_append_single]
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
  refine ⟨by simp, ?_⟩
  have hsec : ∃ pr, (zTileOf pr a, lastPosOf (fwdTiles none (r ++ [a]) c)) ∈ fwdTiles none (r ++ [a]) c := by
    rcases List.eq_nil_or_concat r with rfl | ⟨r', y, rfl⟩
    · exact ⟨none, by simp [fwdTiles_single, lastPosOf]⟩
    · simp only [List.concat_eq_append]
      refine ⟨some y, ?_⟩
      rw [fwdTiles_append (r' ++ [y]) none c a (by simp), lastPos_append_single]
      simp
  obtain ⟨pr, hpr⟩ := hsec
  refine ⟨pr, ?_⟩
  rw [add_sub_cancel_right]
  exact List.mem_append_left _ hpr

/-- The first two tiles of a reversed horizontal string. -/
theorem hRev_head (a b : Letter) (r : BinaryWord) (c : GInt) :
    (zTileOf none a, c) ∈ hRevStringAt (a :: b :: r) c ∧
      (zTileOf (some a) b, c + hRevOffset a b) ∈ hRevStringAt (a :: b :: r) c := by
  show (zTileOf none a, c) ∈ revTiles none (a :: b :: r) c ∧
    (zTileOf (some a) b, c + hRevOffset a b) ∈ revTiles none (a :: b :: r) c
  rw [revTiles_cons2]
  obtain ⟨rest, hrest⟩ := revTiles_head (some a) b r (c + hRevOffset a b)
  rw [hrest]
  simp

theorem revTiles_append (w : BinaryWord) : ∀ (pr : Option Letter) (c : GInt) (x y : Letter), w.getLast? = some y →
    revTiles pr (w ++ [x]) c = revTiles pr w c ++ [(zTileOf (some y) x, lastPosOf (revTiles pr w c) + hRevOffset y x)] := by
  induction w with
  | nil => intro pr c x y h; simp at h
  | cons a w ih =>
    intro pr c x y hy
    cases w with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hy
      subst hy
      rw [show [a] ++ [x] = a :: x :: [] from rfl, revTiles_cons2, revTiles_single, revTiles_single]
      simp [lastPosOf]
    | cons b w' =>
      obtain ⟨rest, hrest⟩ := revTiles_head (some a) b w' (c + hRevOffset a b)
      have hT : revTiles (some a) (b :: w') (c + hRevOffset a b) ≠ [] := by rw [hrest]; exact List.cons_ne_nil _ _
      have hy' : (b :: w').getLast? = some y := by simpa [List.getLast?_cons_cons] using hy
      have e2 := ih (some a) (c + hRevOffset a b) x y hy'
      rw [show (a :: b :: w') ++ [x] = a :: b :: (w' ++ [x]) from rfl, revTiles_cons2, revTiles_cons2,
        show b :: (w' ++ [x]) = (b :: w') ++ [x] from rfl, e2, lastPos_cons_of_ne _ _ hT]
      simp

/-- The last two tiles of a reversed horizontal string. -/
theorem hRev_last (r : BinaryWord) (a b : Letter) (c : GInt) :
    (zTileOf (some a) b, lastPosOf (hRevStringAt (r ++ [a, b]) c)) ∈ hRevStringAt (r ++ [a, b]) c ∧
      ∃ pr, (zTileOf pr a, lastPosOf (hRevStringAt (r ++ [a, b]) c) - hRevOffset a b) ∈ hRevStringAt (r ++ [a, b]) c := by
  show (zTileOf (some a) b, lastPosOf (revTiles none (r ++ [a, b]) c)) ∈ revTiles none (r ++ [a, b]) c ∧
    ∃ pr, (zTileOf pr a, lastPosOf (revTiles none (r ++ [a, b]) c) - hRevOffset a b) ∈ revTiles none (r ++ [a, b]) c
  have e : r ++ [a, b] = (r ++ [a]) ++ [b] := by simp
  rw [e, revTiles_append (r ++ [a]) none c b a (by simp), lastPos_append_single]
  refine ⟨by simp, ?_⟩
  have hsec : ∃ pr, (zTileOf pr a, lastPosOf (revTiles none (r ++ [a]) c)) ∈ revTiles none (r ++ [a]) c := by
    rcases List.eq_nil_or_concat r with rfl | ⟨r', y, rfl⟩
    · exact ⟨none, by simp [revTiles_single, lastPosOf]⟩
    · simp only [List.concat_eq_append]
      refine ⟨some y, ?_⟩
      rw [revTiles_append (r' ++ [y]) none c a y (by simp), lastPos_append_single]
      simp
  obtain ⟨pr, hpr⟩ := hsec
  refine ⟨pr, ?_⟩
  rw [add_sub_cancel_right]
  exact List.mem_append_left _ hpr

/-- The first two tiles of a forward vertical string. -/
theorem vStr_head (a b : Letter) (r : BinaryWord) (c : GInt) :
    (letterZTile a, c) ∈ vStringAt (a :: b :: r) c ∧ (letterZTile b, c + vOffset b) ∈ vStringAt (a :: b :: r) c := by
  rw [VerticalStepOne.vStringAt_eq]
  refine ⟨by cases r <;> simp [VerticalStepOne.vAux], ?_⟩
  show (letterZTile b, c + vOffset b) ∈ (letterZTile a, c) :: VerticalStepOne.vAux false (b :: r) (c + stepV false a b)
  simp only [stepV, Bool.false_eq_true, ↓reduceIte]
  exact List.mem_cons_of_mem _ (by cases r <;> simp [VerticalStepOne.vAux])

/-- The last tile of a reversed vertical string. -/
theorem vRev_last (u : BinaryWord) (x : Letter) (hx : u.getLast? = some x) (c : GInt) :
    (letterZTile x, lastPosOf (vRevStringAt u c)) ∈ vRevStringAt u c := by
  have hlast := CornerValues.vAux_last_fst true u c
  rw [← VerticalStepOne.vRevStringAt_eq, hx] at hlast
  exact JointRot.last_mem_lastPos _ _ hlast

/-! ### The parents of the special words -/

theorem parents_twos (j : ℕ) : parentsAt (List.replicate j Digit.two) = ⟨⟨j, j + 1⟩, ⟨1, 1⟩⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.replicate_succ', parentsAt_append_singleton, ih]
    simp only [Parents.step, Parents.current, Parents.combine, Parents.mk.injEq, Fraction.mk.injEq, and_true]
    push_cast
    constructor <;> ring

theorem parents_threes (j : ℕ) : parentsAt (List.replicate j Digit.three) = ⟨⟨0, 1⟩, ⟨1, 2 * j + 1⟩⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.replicate_succ', parentsAt_append_singleton, ih]
    simp only [Parents.step, Parents.current, Parents.combine, Parents.mk.injEq, Fraction.mk.injEq, true_and]
    refine ⟨by norm_num, by push_cast; ring⟩

theorem W1Odd_special (j k : ℕ) (d e : Digit) (hd : d ≠ Digit.one) (he : e ≠ Digit.one) :
    JointFamily.W1Odd (List.replicate j d ++ List.replicate k e) = false := by
  unfold JointFamily.W1Odd phase
  rw [count_one_twos_threes _ _ _ _ hd he]
  rfl

/-! ### The special words: letters and registers -/

theorem swap_twos_threes (j k : ℕ) :
    swapW (List.replicate j Digit.two ++ List.replicate k Digit.three) =
      List.replicate j Digit.three ++ List.replicate k Digit.two := by
  rw [JointRot.swapW_append, AltRotStep.swapW_replicate_two, AltRotStep.swapW_replicate_three]

theorem swap_threes_twos (j k : ℕ) :
    swapW (List.replicate j Digit.three ++ List.replicate k Digit.two) =
      List.replicate j Digit.two ++ List.replicate k Digit.three := by
  rw [JointRot.swapW_append, AltRotStep.swapW_replicate_two, AltRotStep.swapW_replicate_three]

theorem trailing_special (d e : Digit) (hde : e ≠ d) (j k : ℕ) :
    JointFamily.trailingCount d (List.replicate (j + 1) e ++ List.replicate k d) = k ∧
      JointFamily.stripTrailing d (List.replicate (j + 1) e ++ List.replicate k d) = List.replicate (j + 1) e := by
  induction k with
  | zero =>
    simp only [List.replicate_zero, List.append_nil]
    rw [List.replicate_succ', JointRot.trailingCount_snoc, JointRot.stripTrailing_snoc]
    simp [hde]
  | succ k ih =>
    rw [show List.replicate (k + 1) d = List.replicate k d ++ [d] from List.replicate_succ' .., ← List.append_assoc,
      JointRot.trailingCount_snoc, JointRot.stripTrailing_snoc]
    simp [ih.1, ih.2]

theorem regs_threes_fst (j : ℕ) : (regsAt (List.replicate j Digit.three)).1 = none := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.replicate_succ', JointRot.regsAt_append_singleton]
    exact ih

theorem regs_twos_snd (j : ℕ) : (regsAt (List.replicate j Digit.two)).2 = none := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.replicate_succ', JointRot.regsAt_append_singleton]
    exact ih

/-! ### The positions of the special pieces -/

open FLatticePaper.Tiles.JointRot (oBridge eMid eHead oHead oK eK)
open FLatticePaper.Tiles.JointFamily (Piece)
open FLatticePaper.Tiles.JointFamily (oddLInitOff evenLInitOff p0Off q0Off vP1 vP2 vQ1 vQ2 W1Odd)
open FLatticePaper.Tiles.SurgicalDict (offsetP0 offsetQ0)
open FLatticePaper.Tiles.SurgicalAlt (coeffOff)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)
open FLatticePaper.Construction (texV1Odd texV1Even texV2)

set_option hygiene false in
macro "sp_pos" : tactic => `(tactic| (
  simp only [oBridge, eMid, oK, eK, oddLInitOff, evenLInitOff, p0Off, q0Off, offsetP0, offsetQ0, JointFamily.altOff,
    coeffOff, JointFamily.oddKCoeff, JointFamily.evenKCoeff, LCorrections.oddBridgeShift, vP1, vP2, vQ1, vQ2, texV1Odd,
    texV1Even, texV2, fracOdd, fracEven, Parents.current, Parents.combine, JointRot.parents_append_twos,
    JointRot.parents_append_threes, JointFamily.stdPiece,
    parents_threes, parents_twos, hW, htr, hst, hTD, ↓reduceIte, Bool.false_eq_true, Bool.not_false, Bool.not_true,
    Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Prod.smul_mk, smul_eq_mul]
  refine Prod.ext ?_ ?_ <;> simp <;> push_cast <;> ring))

/-- (E, `+`) The bridge of the odd L-correction at `3^(j+1) 2^k` is the last tile of the reversed vertical string of its child. -/
theorem pos_E_R_plus (S : WeakData) (pO pE : Word → PartialOdometer) (j k : ℕ) :
    (oBridge S pO pE (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) true).off =
      texV2 (fracOdd (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two)) + ((1 : ℤ), (-2 : ℤ)) := by
  have hW := W1Odd_special (j + 1) k Digit.three Digit.two (by decide) (by decide)
  obtain ⟨htr, hst⟩ := trailing_special Digit.two Digit.three (by decide) j k
  have hTD : (!(List.replicate (j + 1) Digit.three).isEmpty &&
      (List.replicate (j + 1) Digit.three).all (fun d => decide (d = Digit.three))) = true := by simp
  sp_pos

/-- (E, `-`) The bridge is the first tile of the forward vertical string of its child. -/
theorem pos_E_R_minus (S : WeakData) (pO pE : Word → PartialOdometer) (j k : ℕ) :
    (oBridge S pO pE (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false).off = texV1Odd (fracOdd (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two)) - ((1 : ℤ), (1 : ℤ)) := by
  have hW := W1Odd_special (j + 1) k Digit.three Digit.two (by decide) (by decide)
  obtain ⟨htr, hst⟩ := trailing_special Digit.two Digit.three (by decide) j k
  have hTD : (!(List.replicate (j + 1) Digit.three).isEmpty &&
      (List.replicate (j + 1) Digit.three).all (fun d => decide (d = Digit.three))) = true := by simp
  sp_pos

/-- (E, `+`) The image of the bridge under `z` is at `(2, 0)` (the first two tiles of the forward horizontal string). -/
theorem pos_E_O_plus (S : WeakData) (pO pE : Word → PartialOdometer) (j k : ℕ) :
    Farey.mulI (oBridge S pO pE (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) true).off +
        (texV1Even ((parentsAt (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)).current .even) - ((0 : ℤ), (1 : ℤ))) = ((2 : ℤ), (0 : ℤ)) := by
  have hW := W1Odd_special (j + 1) k Digit.three Digit.two (by decide) (by decide)
  obtain ⟨htr, hst⟩ := trailing_special Digit.two Digit.three (by decide) j k
  have hTD : (!(List.replicate (j + 1) Digit.three).isEmpty &&
      (List.replicate (j + 1) Digit.three).all (fun d => decide (d = Digit.three))) = true := by simp
  simp only [Farey.mulI]
  sp_pos

/-- (E, `-`) The image of the bridge under `z` is one step right of the last tile of the reversed horizontal string. -/
theorem pos_E_O_minus (S : WeakData) (pO pE : Word → PartialOdometer) (j k : ℕ) :
    Farey.mulI (oBridge S pO pE (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false).off +
        (texV1Even ((parentsAt (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)).current .even) - ((0 : ℤ), (1 : ℤ))) =
      texV2 (fracEven (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) + ((1 : ℤ), (-2 : ℤ)) + (texV1Even (fracEven (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) - ((1 : ℤ), (1 : ℤ))) +
        ((0 : ℤ), (1 : ℤ)) + ((1 : ℤ), (0 : ℤ)) := by
  have hW := W1Odd_special (j + 1) k Digit.three Digit.two (by decide) (by decide)
  obtain ⟨htr, hst⟩ := trailing_special Digit.two Digit.three (by decide) j k
  have hTD : (!(List.replicate (j + 1) Digit.three).isEmpty &&
      (List.replicate (j + 1) Digit.three).all (fun d => decide (d = Digit.three))) = true := by simp
  simp only [Farey.mulI]
  sp_pos

/-- (O, `s = +`) The middle of the even L-correction at `2^(j+1) 3^k` starts at the origin. -/
theorem pos_O_R_plus (j k : ℕ) : (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).2.1)) = 0 := by
  have hW := W1Odd_special (j + 1) k Digit.two Digit.three (by decide) (by decide)
  obtain ⟨htr, hst⟩ := trailing_special Digit.three Digit.two (by decide) j k
  have hTD : (!(List.replicate (j + 1) Digit.two).isEmpty &&
      (List.replicate (j + 1) Digit.two).all (fun d => decide (d = Digit.two))) = true := by simp
  sp_pos

/-- (O, `s = -`) The copy of `T^d_{1/1}` is the last tile of the reversed horizontal string of its child. -/
theorem pos_O_R_minus (j k : ℕ) :
    (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false).2.1)) + ((1 : ℤ), (1 : ℤ)) =
      texV2 (fracEven (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) + ((1 : ℤ), (-2 : ℤ)) + (texV1Even (fracEven (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) - ((1 : ℤ), (1 : ℤ))) + ((0 : ℤ), (1 : ℤ)) := by
  have hW := W1Odd_special (j + 1) k Digit.two Digit.three (by decide) (by decide)
  obtain ⟨htr, hst⟩ := trailing_special Digit.three Digit.two (by decide) j k
  have hTD : (!(List.replicate (j + 1) Digit.two).isEmpty &&
      (List.replicate (j + 1) Digit.two).all (fun d => decide (d = Digit.two))) = true := by simp
  sp_pos

/-- (O, `s = +`) The image of the middle under `z` starts one step right of the last tile of the forward horizontal string. -/
theorem pos_O_O_plus (j k : ℕ) :
    Farey.mulI (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).2.1)) + (texV1Odd ((parentsAt (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two)).current .odd) - ((0 : ℤ), (1 : ℤ))) =
      texV1Odd (fracOdd (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two)) - ((1 : ℤ), (1 : ℤ)) + ((1 : ℤ), (0 : ℤ)) := by
  have hW := W1Odd_special (j + 1) k Digit.two Digit.three (by decide) (by decide)
  obtain ⟨htr, hst⟩ := trailing_special Digit.three Digit.two (by decide) j k
  have hTD : (!(List.replicate (j + 1) Digit.two).isEmpty &&
      (List.replicate (j + 1) Digit.two).all (fun d => decide (d = Digit.two))) = true := by simp
  simp only [Farey.mulI]
  sp_pos

/-- (O, `s = -`) The image of the copy of `T^d_{1/1}` is at the last tile of the reversed vertical string plus `(1, 1)`. -/
theorem pos_O_O_minus (j k : ℕ) :
    Farey.mulI ((evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false).2.1)) + ((1 : ℤ), (1 : ℤ))) +
        (texV1Odd ((parentsAt (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two)).current .odd) - ((0 : ℤ), (1 : ℤ))) =
      texV2 (fracOdd (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two)) + ((1 : ℤ), (-2 : ℤ)) + ((1 : ℤ), (1 : ℤ)) := by
  have hW := W1Odd_special (j + 1) k Digit.two Digit.three (by decide) (by decide)
  obtain ⟨htr, hst⟩ := trailing_special Digit.three Digit.two (by decide) j k
  have hTD : (!(List.replicate (j + 1) Digit.two).isEmpty &&
      (List.replicate (j + 1) Digit.two).all (fun d => decide (d = Digit.two))) = true := by simp
  simp only [Farey.mulI]
  sp_pos

/-! ### The cells of the special pieces on the kept sides -/

open FLatticePaper.Tiles.Standard (zeroTile oneTile)

theorem mem_zeroTile_iff (s : Site) : s ∈ zeroTile ↔ s ∈ tileShape ZTile.zero := by
  simp [zeroTile, tileShape]

/-- A point of the bridge of the odd L-correction at `3^(j+1) 2^k` is its offset plus a point of `T_{0/1}`. -/
theorem bridge_point (S : WeakData) (hz : S.zeroO.dom = zeroTile) (pO pE : Word → PartialOdometer) (j k : ℕ) (plus : Bool)
    (x : Site) (hx : x ∈ (oBridge S pO pE (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) plus).placed) :
    ∃ s ∈ tileShape ZTile.zero, x = (oBridge S pO pE (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) plus).off + s := by
  rw [JointRot.mem_placed] at hx
  obtain ⟨-, hst⟩ := trailing_special Digit.two Digit.three (by decide) j k
  have hodo : (oBridge S pO pE (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) plus).odo = S.zeroO := by
    simp only [oBridge, JointFamily.stdPiece, hst, regs_threes_fst]
    rfl
  rw [hodo, hz, mem_zeroTile_iff] at hx
  exact ⟨_, hx, by abel⟩

/-- (E, `+`, R) The bridge lies on the reversed vertical string of the odd child of `3^(j+1) 2^k`. -/
theorem cells_E_R_plus (S : WeakData) (hz : S.zeroO.dom = zeroTile) (pO pE : Word → PartialOdometer) (j k : ℕ) (x : Site)
    (hx : x ∈ (oBridge S pO pE (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) true).placed) :
    x ∈ placedSites (vRevStringAt (vWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false).reverse 0) := by
  obtain ⟨s, hs, rfl⟩ := bridge_point S hz pO pE j k true x hx
  have hl : (vWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false).reverse.getLast? = some Letter.p := by
    rw [List.getLast?_reverse]; exact GlueStringDecomp.vp_head _
  have ht := vRev_last _ _ hl 0
  rw [StdCornerAnchors.stdAnchorY_odd, ← pos_E_R_plus S pO pE j k] at ht
  exact JointRot.mem_placedSites_of ht hs

/-- (E, `-`, R) The bridge lies on the forward vertical string of the odd child of `3^(j+1) 2^k`. -/
theorem cells_E_R_minus (S : WeakData) (hz : S.zeroO.dom = zeroTile) (pO pE : Word → PartialOdometer) (j k : ℕ) (x : Site)
    (hx : x ∈ (oBridge S pO pE (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false).placed) :
    x ∈ placedSites (vStringAt (vWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false) (lastPosOf (hStringAt (hWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false) 0))) := by
  obtain ⟨s, hs, rfl⟩ := bridge_point S hz pO pE j k false x hx
  obtain ⟨r, hr⟩ := (ends_threes_twos j k).2.2.2.2.1
  have hpos : lastPosOf (hStringAt (hWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false) 0) =
      (oBridge S pO pE (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false).off := by
    rw [show (0 : GInt) = ((0 : ℤ), (0 : ℤ)) from rfl, StdCornerAnchors.stdAnchorX_odd, pos_E_R_minus]
  rw [hpos, hr]
  exact JointRot.mem_placedSites_of (vStr_head Letter.p Letter.p r _).1 hs

theorem mem_of_tile {L : List (ZTile × GInt)} {t : ZTile} {P : GInt} (ht : (t, P) ∈ L) (u : GInt)
    (hu : u ∈ tileShape t) (y : GInt) (hy : y = P + u) : y ∈ placedSites L := by
  rw [hy]; exact JointRot.mem_placedSites_of ht hu

theorem z_add (a b c : GInt) : Farey.mulI (a + b) + c = (Farey.mulI a + c) + Farey.mulI b := by
  simp only [Farey.mulI]; refine Prod.ext ?_ ?_ <;> simp <;> ring

set_option hygiene false in
/-- Closes `P + v = Q + u` for explicit `v`, `u` given `P = Q + d`. -/
macro "pt_eq" : tactic => `(tactic| (refine Prod.ext ?_ ?_ <;> simp [Farey.mulI] <;> ring))

/-- (E, `+`, O) The image of the bridge lies on the first two tiles of the forward horizontal string of the even child of
`2^(j+1) 3^k`. -/
theorem cells_E_O_plus (S : WeakData) (hz : S.zeroO.dom = zeroTile) (pO pE : Word → PartialOdometer) (j k : ℕ) (x : Site)
    (hx : x ∈ (oBridge S pO pE (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) true).placed) :
    Farey.mulI x + (texV1Even ((parentsAt (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)).current .even) - ((0 : ℤ), (1 : ℤ))) ∈
      placedSites (hStringAt (hWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true) 0) := by
  obtain ⟨s, hs, rfl⟩ := bridge_point S hz pO pE j k true x hx
  rw [z_add, pos_E_O_plus]
  obtain ⟨r, hr⟩ := (ends_twos_threes j k).2.2.1
  rw [hr]
  obtain ⟨h0, h1⟩ := hStr_head Letter.q Letter.q r 0
  simp only [zTileOf, hOffset] at h0 h1
  simp only [tileShape, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_of_tile h1 (1, -1) (by simp [tileShape]) _ (by pt_eq)
  · exact mem_of_tile h0 (1, 0) (by simp [tileShape]) _ (by pt_eq)
  · exact mem_of_tile h0 (0, 0) (by simp [tileShape]) _ (by pt_eq)
  · exact mem_of_tile h1 (1, 0) (by simp [tileShape]) _ (by pt_eq)
  · exact mem_of_tile h0 (1, 1) (by simp [tileShape]) _ (by pt_eq)
  · exact mem_of_tile h0 (0, 1) (by simp [tileShape]) _ (by pt_eq)

/-- (E, `-`, O) The image of the bridge lies on the last two tiles of the reversed horizontal string of the even child of
`2^(j+1) 3^k`. -/
theorem cells_E_O_minus (S : WeakData) (hz : S.zeroO.dom = zeroTile) (pO pE : Word → PartialOdometer) (j k : ℕ) (x : Site)
    (hx : x ∈ (oBridge S pO pE (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false).placed) :
    Farey.mulI x + (texV1Even ((parentsAt (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)).current .even) - ((0 : ℤ), (1 : ℤ))) ∈
      placedSites (hRevStringAt (hWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).reverse (lastPosOf (vRevStringAt (vWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).reverse 0))) := by
  obtain ⟨s, hs, rfl⟩ := bridge_point S hz pO pE j k false x hx
  rw [z_add, pos_E_O_minus]
  obtain ⟨r, hr⟩ := (ends_twos_threes j k).2.2.1
  have hrev : (hWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).reverse = r.reverse ++ [Letter.q, Letter.q] := by rw [hr]; simp
  rw [StdCornerAnchors.stdAnchorY_even]
  obtain ⟨h1, pr, h0⟩ := hRev_last r.reverse Letter.q Letter.q (texV2 (fracEven (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) + ((1 : ℤ), (-2 : ℤ)))
  rw [← hrev, GlueStringDecomp.lp_top_even] at h1 h0
  simp only [zTileOf, hRevOffset] at h1 h0
  simp only [tileShape, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_of_tile h1 (1, 0) (by simp [tileShape]) _ (by pt_eq)
  · exact mem_of_tile h1 (0, 0) (by simp [tileShape]) _ (by pt_eq)
  · exact mem_of_tile h0 (0, 1) (ReflectedCover.R2_sub pr _ (by simp [tileShape])) _ (by pt_eq)
  · exact mem_of_tile h1 (1, 1) (by simp [tileShape]) _ (by pt_eq)
  · exact mem_of_tile h1 (0, 1) (by simp [tileShape]) _ (by pt_eq)
  · exact mem_of_tile h1 (-1, 1) (by simp [tileShape]) _ (by pt_eq)

/-! ### The odd kind: the middle pieces of the even L-correction at `2^(j+1) 3^k` -/

theorem mem_oneTile_iff (s : Site) : s ∈ oneTile ↔ s ∈ tileShape ZTile.one := by
  simp [oneTile, tileShape]

/-- The middle pieces: the bridge `S.oneO` at `B` (for `s = +`) and the copy of `T^d_{1/1}` at `B + (1, 1)`. -/
theorem mid_mem (S : WeakData) (pO pE : Word → PartialOdometer) (j k : ℕ) (sg : Bool)
    (P : Piece) (hP : P ∈ eMid S pO pE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) sg) :
    (sg = true ∧ P.odo = S.oneO ∧ P.off = (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) sg + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) sg).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) sg).2.1))) ∨
      (P.odo = JointFamily.enlOdo ∧ P.off = (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) sg + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) sg).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) sg).2.1)) + ((1 : ℤ), (1 : ℤ))) := by
  have hW := W1Odd_special (j + 1) k Digit.two Digit.three (by decide) (by decide)
  obtain ⟨-, hst⟩ := trailing_special Digit.three Digit.two (by decide) j k
  have hTD : (!(List.replicate (j + 1) Digit.two).isEmpty &&
      (List.replicate (j + 1) Digit.two).all (fun d => decide (d = Digit.two))) = true := by simp
  unfold eMid at hP
  simp only [hst, hTD, hW] at hP
  cases sg <;> simp at hP
  · subst hP
    right
    exact ⟨rfl, by simp [JointFamily.stdPiece, hst]⟩
  · rcases hP with rfl | rfl
    · left
      refine ⟨rfl, ?_, by simp [JointFamily.stdPiece, hst]⟩
      simp only [JointFamily.stdPiece, regs_twos_snd]
      rfl
    · right
      exact ⟨rfl, by simp [JointFamily.stdPiece, hst]⟩

/-- The points of the middle pieces. -/
theorem mid_points (S : WeakData) (hone : S.oneO.dom = oneTile) (pO pE : Word → PartialOdometer) (j k : ℕ) (sg : Bool)
    (P : Piece) (hP : P ∈ eMid S pO pE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) sg) (x : Site) (hx : x ∈ P.placed) :
    (sg = true ∧ ∃ u ∈ tileShape ZTile.one, x = (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) sg + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) sg).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) sg).2.1)) + u) ∨
      ∃ u ∈ tileShape ZTile.oneD, x = (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) sg + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) sg).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) sg).2.1)) + ((1 : ℤ), (1 : ℤ)) + u := by
  rw [JointRot.mem_placed] at hx
  rcases mid_mem S pO pE j k sg P hP with ⟨hs, ho, hoff⟩ | ⟨ho, hoff⟩
  · rw [ho, hone, mem_oneTile_iff, hoff] at hx
    exact Or.inl ⟨hs, _, hx, by abel⟩
  · rw [ho, hoff] at hx
    simp only [JointFamily.enlOdo, List.mem_toFinset] at hx
    exact Or.inr ⟨_, hx, by abel⟩

/-- (O, `s = +`, R) The middle pieces lie on the first two tiles of the forward horizontal string of the even child of
`2^(j+1) 3^k`. -/
theorem cells_O_R_plus (S : WeakData) (hone : S.oneO.dom = oneTile) (pO pE : Word → PartialOdometer) (j k : ℕ)
    (P : Piece) (hP : P ∈ eMid S pO pE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true) (x : Site) (hx : x ∈ P.placed) :
    x ∈ placedSites (hStringAt (hWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true) 0) := by
  obtain ⟨r, hr⟩ := (ends_twos_threes j k).2.2.1
  obtain ⟨h0, h1⟩ := hStr_head Letter.q Letter.q r 0
  simp only [zTileOf, hOffset] at h0 h1
  rw [hr]
  rcases mid_points S hone pO pE j k true P hP x hx with ⟨-, u, hu, rfl⟩ | ⟨u, hu, rfl⟩
  · rw [pos_O_R_plus]
    exact mem_of_tile h0 u hu _ (by abel)
  · rw [pos_O_R_plus]
    exact mem_of_tile h1 u hu _ (by pt_eq)

/-- (O, `s = -`, R) The copy of `T^d_{1/1}` is the last tile of the reversed horizontal string of the even child of
`2^(j+1) 3^k`. -/
theorem cells_O_R_minus (S : WeakData) (hone : S.oneO.dom = oneTile) (pO pE : Word → PartialOdometer) (j k : ℕ)
    (P : Piece) (hP : P ∈ eMid S pO pE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false) (x : Site) (hx : x ∈ P.placed) :
    x ∈ placedSites (hRevStringAt (hWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).reverse (lastPosOf (vRevStringAt (vWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).reverse 0))) := by
  obtain ⟨r, hr⟩ := (ends_twos_threes j k).2.2.1
  have hrev : (hWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).reverse = r.reverse ++ [Letter.q, Letter.q] := by rw [hr]; simp
  rw [StdCornerAnchors.stdAnchorY_even]
  obtain ⟨h1, -, -⟩ := hRev_last r.reverse Letter.q Letter.q (texV2 (fracEven (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) + ((1 : ℤ), (-2 : ℤ)))
  rw [← hrev, GlueStringDecomp.lp_top_even] at h1
  simp only [zTileOf] at h1
  rcases mid_points S hone pO pE j k false P hP x hx with ⟨h, -⟩ | ⟨u, hu, rfl⟩
  · exact absurd h (by decide)
  · rw [pos_O_R_minus]
    exact mem_of_tile h1 u hu _ rfl

/-- (O, `s = +`, image, elongated) The images lie on the last two tiles of the forward horizontal string of the odd child of
`3^(j+1) 2^k`. -/
theorem cells_O_O_plus_elong (S : WeakData) (hone : S.oneO.dom = oneTile) (pO pE : Word → PartialOdometer) (j k : ℕ)
    (P : Piece) (hP : P ∈ eMid S pO pE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true) (x : Site) (hx : x ∈ P.placed) :
    Farey.mulI x + (texV1Odd ((parentsAt (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two)).current .odd) - ((0 : ℤ), (1 : ℤ))) ∈ placedSites (hStringAt (hWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false) 0) := by
  obtain ⟨r, hr⟩ := (ends_threes_twos j k).2.1
  obtain ⟨h1, pr, h0⟩ := hStr_last r Letter.p Letter.p 0
  rw [← hr, show (0 : GInt) = ((0 : ℤ), (0 : ℤ)) from rfl, StdCornerAnchors.stdAnchorX_odd] at h1 h0
  simp only [zTileOf, hOffset] at h1 h0
  rw [show (0 : GInt) = ((0 : ℤ), (0 : ℤ)) from rfl]
  rcases mid_points S hone pO pE j k true P hP x hx with ⟨-, u, hu, rfl⟩ | ⟨u, hu, rfl⟩
  · rw [z_add, pos_O_O_plus]
    simp only [tileShape, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact mem_of_tile h1 (1, 0) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile h1 (0, 0) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile h1 (1, 1) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile h1 (0, 1) (by simp [tileShape]) _ (by pt_eq)
  · rw [z_add, z_add, pos_O_O_plus]
    simp only [tileShape, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · exact mem_of_tile h1 (0, 1) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile h0 (1, 1) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile h1 (0, 2) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile h0 (1, 2) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile h0 (1, 0) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile h1 (1, 2) (by simp [tileShape]) _ (by pt_eq)

/-- (O, `s = +`, image, short) The images lie on the first two tiles of the forward vertical string of the odd child of
`3^(j+1) 2^k`, except the tip `(-1, 1)` of the copy of `T^d_{1/1}`. -/
theorem cells_O_O_plus_short (S : WeakData) (hone : S.oneO.dom = oneTile) (pO pE : Word → PartialOdometer) (j k : ℕ)
    (P : Piece) (hP : P ∈ eMid S pO pE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true) (x : Site) (hx : x ∈ P.placed)
    (htip : x ≠ (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).2.1)) + ((1 : ℤ), (1 : ℤ)) + ((-1 : ℤ), (1 : ℤ))) :
    Farey.mulI x + (texV1Odd ((parentsAt (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two)).current .odd) - ((0 : ℤ), (1 : ℤ))) ∈
      placedSites (vStringAt (vWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false) (lastPosOf (hStringAt (hWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false) 0))) := by
  obtain ⟨r, hr⟩ := (ends_threes_twos j k).2.2.2.2.1
  rw [show (0 : GInt) = ((0 : ℤ), (0 : ℤ)) from rfl, StdCornerAnchors.stdAnchorX_odd, hr]
  obtain ⟨h0, h1⟩ := vStr_head Letter.p Letter.p r (texV1Odd (fracOdd (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two)) - ((1 : ℤ), (1 : ℤ)))
  simp only [letterZTile, vOffset] at h0 h1
  rcases mid_points S hone pO pE j k true P hP x hx with ⟨-, u, hu, rfl⟩ | ⟨u, hu, rfl⟩
  · rw [z_add, pos_O_O_plus]
    simp only [tileShape, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact mem_of_tile h0 (1, 0) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile h0 (0, 0) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile h0 (1, 1) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile h0 (0, 1) (by simp [tileShape]) _ (by pt_eq)
  · rw [z_add, z_add, pos_O_O_plus]
    simp only [tileShape, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · exact mem_of_tile h0 (0, 1) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile h1 (0, 0) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile h0 (0, 2) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile h1 (0, 1) (by simp [tileShape]) _ (by pt_eq)
    · exact absurd rfl htip
    · exact mem_of_tile h0 (1, 2) (by simp [tileShape]) _ (by pt_eq)

/-- (O, `s = -`, image, elongated) The images lie on the first two tiles of the reversed horizontal string of the odd child of
`3^(j+1) 2^k`. -/
theorem cells_O_O_minus_elong (S : WeakData) (hone : S.oneO.dom = oneTile) (pO pE : Word → PartialOdometer) (j k : ℕ)
    (P : Piece) (hP : P ∈ eMid S pO pE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false) (x : Site) (hx : x ∈ P.placed) :
    Farey.mulI x + (texV1Odd ((parentsAt (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two)).current .odd) - ((0 : ℤ), (1 : ℤ))) ∈
      placedSites (hRevStringAt (hWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false).reverse (lastPosOf (vRevStringAt (vWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false).reverse 0))) := by
  obtain ⟨r, hr⟩ := (ends_threes_twos j k).2.1
  have hrev : (hWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false).reverse = Letter.p :: Letter.p :: r.reverse := by rw [hr]; simp
  rw [StdCornerAnchors.stdAnchorY_odd, hrev]
  obtain ⟨h0, h1⟩ := hRev_head Letter.p Letter.p r.reverse (texV2 (fracOdd (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two)) + ((1 : ℤ), (-2 : ℤ)))
  simp only [zTileOf, hRevOffset] at h0 h1
  rcases mid_points S hone pO pE j k false P hP x hx with ⟨h, -⟩ | ⟨u, hu, rfl⟩
  · exact absurd h (by decide)
  · rw [z_add, pos_O_O_minus]
    simp only [tileShape, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · exact mem_of_tile h0 (1, 1) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile h0 (0, 1) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile h0 (1, 2) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile h0 (0, 2) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile h0 (0, 0) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile h1 (0, 2) (by simp [tileShape]) _ (by pt_eq)

/-- (O, `s = -`, image, short) The images lie on the last tile of the reversed vertical string of the odd child of
`3^(j+1) 2^k`, except the tip `(1, -1)` of the copy of `T^d_{1/1}`. -/
theorem cells_O_O_minus_short (S : WeakData) (hone : S.oneO.dom = oneTile) (pO pE : Word → PartialOdometer) (j k : ℕ)
    (P : Piece) (hP : P ∈ eMid S pO pE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false) (x : Site) (hx : x ∈ P.placed)
    (htip : x ≠ (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false).2.1)) + ((1 : ℤ), (1 : ℤ)) + ((1 : ℤ), (-1 : ℤ))) :
    Farey.mulI x + (texV1Odd ((parentsAt (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two)).current .odd) - ((0 : ℤ), (1 : ℤ))) ∈ placedSites (vRevStringAt (vWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false).reverse 0) := by
  have hl : (vWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false).reverse.getLast? = some Letter.p := by
    rw [List.getLast?_reverse]; exact GlueStringDecomp.vp_head _
  have ht := vRev_last _ _ hl 0
  rw [StdCornerAnchors.stdAnchorY_odd] at ht
  simp only [letterZTile] at ht
  rcases mid_points S hone pO pE j k false P hP x hx with ⟨h, -⟩ | ⟨u, hu, rfl⟩
  · exact absurd h (by decide)
  · rw [z_add, pos_O_O_minus]
    simp only [tileShape, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · exact mem_of_tile ht (1, 1) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile ht (0, 1) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile ht (1, 2) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile ht (0, 2) (by simp [tileShape]) _ (by pt_eq)
    · exact mem_of_tile ht (0, 0) (by simp [tileShape]) _ (by pt_eq)
    · exact absurd rfl htip

/-! ### The exceptional points of the first heads

The first head of each L-correction at a special prefix carries two exceptional points: the points of its set `A` (of
`lemma:basecase_3k_even_alt` for the odd L-correction, of `lemma:basecase_2k_odd_alt` for the even one) that lie in the last
stem. The rotation maps the set `A` of the rotated first head onto that of the other, and the last stems are the base tiles
`T_{1/d}`-type staircases of `2^j` and `3^j`; the two lemmas below are the resulting finite check, for `d = 2j + 3`. -/

open FLatticePaper.Construction (paperStairAltA paperNearStairAltA)
open FLatticePaper.Tiles.Standard (stairF nstairN shift mem_shift)

theorem mem_nstairN_ab (d a b : ℤ) : (a, b) ∈ nstairN d ↔ (a, b + 1) ∈ Standard.nstairF d := by
  unfold nstairN
  rw [mem_shift]
  have h : ((a, b) : Site) - ((0 : ℤ), (-1 : ℤ)) = (a, b + 1) := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [h]

/-- The even kind: a point `x` of the rotated (odd) first head whose image is exceptional in the even first head is
exceptional. -/
theorem exc_transfer_E (d : ℤ) (hd : 3 ≤ d) (oO sO oR sR c G F x : Site)
    (hE1 : Farey.mulI oR + c = oO + (d, 2 * d - 4)) (hG : oO = sO + G) (hF : oR = sR + F)
    (hGF : (G = ((-1 : ℤ), (1 : ℤ)) ∧ F = (d - 1, (2 : ℤ))) ∨ (G = ((2 : ℤ), 1 - d) ∧ F = ((-1 : ℤ), (-1 : ℤ))))
    (h1 : Farey.mulI x + c - oO + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltA d)
    (h2 : Farey.mulI x + c ∈ shift (nstairN d) sO) :
    x - oR ∈ paperStairAltA d ∧ x ∈ shift (stairF d) sR := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨o1, o2⟩ := oO
  obtain ⟨s1, s2⟩ := sO
  obtain ⟨r1, r2⟩ := oR
  obtain ⟨t1, t2⟩ := sR
  obtain ⟨c1, c2⟩ := c
  obtain ⟨g1, g2⟩ := G
  obtain ⟨f1, f2⟩ := F
  simp only [Farey.mulI, Prod.mk_add_mk, Prod.mk.injEq] at hE1 hG hF hGF
  rw [mem_shift] at h2 ⊢
  simp only [Farey.mulI, Prod.mk_add_mk, Prod.mk_sub_mk] at h1 h2 ⊢
  rw [mem_nstairN_ab, BaseTileProps.mem_nstairF_ab d hd] at h2
  rw [BaseTileProps.mem_stairF_ab d hd]
  simp only [paperNearStairAltA, paperStairAltA, Set.mem_union, Set.mem_setOf_eq] at h1 ⊢
  omega

/-- The odd kind: a point `x` of the rotated (even) first head whose image is exceptional in the odd first head is
exceptional. -/
theorem exc_transfer_O (d : ℤ) (hd : 3 ≤ d) (oO sO oR sR c G F x : Site)
    (hE1 : Farey.mulI oR + c = oO + (d, (0 : ℤ))) (hG : oO = sO + G) (hF : oR = sR + F)
    (hGF : (G = (d - 1, (2 : ℤ)) ∧ F = ((2 : ℤ), 1 - d)) ∨ (G = ((-1 : ℤ), (-1 : ℤ)) ∧ F = ((-1 : ℤ), (1 : ℤ))))
    (h1 : Farey.mulI x + c - oO ∈ paperStairAltA d)
    (h2 : Farey.mulI x + c ∈ shift (stairF d) sO) :
    x - oR + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltA d ∧ x ∈ shift (nstairN d) sR := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨o1, o2⟩ := oO
  obtain ⟨s1, s2⟩ := sO
  obtain ⟨r1, r2⟩ := oR
  obtain ⟨t1, t2⟩ := sR
  obtain ⟨c1, c2⟩ := c
  obtain ⟨g1, g2⟩ := G
  obtain ⟨f1, f2⟩ := F
  simp only [Farey.mulI, Prod.mk_add_mk, Prod.mk.injEq] at hE1 hG hF hGF
  rw [mem_shift] at h2 ⊢
  simp only [Farey.mulI, Prod.mk_add_mk, Prod.mk_sub_mk] at h1 h2 ⊢
  rw [BaseTileProps.mem_stairF_ab d hd] at h2
  rw [mem_nstairN_ab, BaseTileProps.mem_nstairF_ab d hd]
  simp only [paperNearStairAltA, paperStairAltA, Set.mem_union, Set.mem_setOf_eq] at h1 ⊢
  omega

theorem regs_twos_fst' (j : ℕ) : (regsAt (List.replicate (j + 1) Digit.two)).1 = some (List.replicate j Digit.two) := by
  have h := regs_twos_threes j 0
  rw [List.replicate_zero, List.append_nil] at h
  rw [h]

theorem regs_threes_snd' (j : ℕ) : (regsAt (List.replicate (j + 1) Digit.three)).2 = some (List.replicate j Digit.three) := by
  have h := regs_threes_twos j 0
  rw [List.replicate_zero, List.append_nil] at h
  rw [h]

theorem len_d (d : Digit) (j : ℕ) : 2 * ((List.replicate (j + 1) d).length : ℤ) + 1 = 2 * (j : ℤ) + 3 := by
  simp; ring

theorem getLast_rep (d : Digit) (j : ℕ) : (List.replicate (j + 1) d).getLast? = some d := by
  rw [List.replicate_succ']
  simp

set_option hygiene false in
/-- The positions at the two special words of a pair (`hW2`, `hW3`, `htr2`, `htr3` in context). -/
macro "sp_pos2" : tactic => `(tactic| (
  simp only [Farey.mulI, oK, eK, oddLInitOff, evenLInitOff, p0Off, q0Off, offsetP0, offsetQ0, JointFamily.altOff,
    coeffOff, JointFamily.oddKCoeff, JointFamily.evenKCoeff, vP1, vP2, vQ1, vQ2, texV1Odd,
    texV1Even, texV2, fracOdd, fracEven, Parents.current, Parents.combine, JointRot.parents_append_twos,
    JointRot.parents_append_threes, parents_threes, parents_twos, hW2, hW3, htr2, htr3, hst2, hst3, getLast_rep, ↓reduceIte, Bool.false_eq_true,
    Bool.not_false, Bool.not_true, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Prod.smul_mk, smul_eq_mul]
  refine Prod.ext ?_ ?_ <;> simp <;> push_cast <;> ring))

/-- (E) The exceptional points of the first heads correspond. -/
theorem exc_E (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (j k : ℕ) (plus : Bool)
    (hdO : (pO (List.replicate j Digit.two)).dom = nstairN (2 * (j : ℤ) + 3))
    (hdR : (pE (List.replicate j Digit.three)).dom = stairF (2 * (j : ℤ) + 3)) (x : Site)
    (hx : x ∉ (oHead S pO pE aO aE (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) plus 0).exc) :
    Farey.mulI x + (texV1Even ((parentsAt (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)).current .even) - ((0 : ℤ), (1 : ℤ))) ∉
      (eHead S pO pE aO aE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) plus 0).exc := by
  intro hz
  apply hx
  obtain ⟨-, hst2⟩ := trailing_special Digit.three Digit.two (by decide) j k
  obtain ⟨-, hst3⟩ := trailing_special Digit.two Digit.three (by decide) j k
  have hTD2 : (!(List.replicate (j + 1) Digit.two).isEmpty &&
      (List.replicate (j + 1) Digit.two).all (fun d => decide (d = Digit.two))) = true := by simp
  have hTD3 : (!(List.replicate (j + 1) Digit.three).isEmpty &&
      (List.replicate (j + 1) Digit.three).all (fun d => decide (d = Digit.three))) = true := by simp
  simp only [eHead, hst2, hTD2, regs_twos_fst', regOdo, hdO, len_d, Bool.true_and, beq_self_eq_true, ↓reduceIte,
    Set.mem_setOf_eq] at hz
  simp only [oHead, hst3, hTD3, regs_threes_snd', regOdo, hdR, len_d, Bool.true_and, beq_self_eq_true, ↓reduceIte,
    Set.mem_setOf_eq]
  have hW2 := W1Odd_special (j + 1) k Digit.two Digit.three (by decide) (by decide)
  have hW3 := W1Odd_special (j + 1) k Digit.three Digit.two (by decide) (by decide)
  obtain ⟨htr2, -⟩ := trailing_special Digit.three Digit.two (by decide) j k
  obtain ⟨htr3, -⟩ := trailing_special Digit.two Digit.three (by decide) j k
  cases plus
  · refine exc_transfer_E (2 * (j : ℤ) + 3) (by omega) _ _ _ _ _ _ _ _ ?_ ?_ ?_ (Or.inr ⟨rfl, rfl⟩) hz.1 hz.2
    all_goals sp_pos2
  · refine exc_transfer_E (2 * (j : ℤ) + 3) (by omega) _ _ _ _ _ _ _ _ ?_ ?_ ?_ (Or.inl ⟨rfl, rfl⟩) hz.1 hz.2
    all_goals sp_pos2

/-- (O) The exceptional points of the first heads correspond. -/
theorem exc_O (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (j k : ℕ) (plus : Bool)
    (hdO : (pE (List.replicate j Digit.three)).dom = stairF (2 * (j : ℤ) + 3))
    (hdR : (pO (List.replicate j Digit.two)).dom = nstairN (2 * (j : ℤ) + 3)) (x : Site)
    (hx : x ∉ (eHead S pO pE aO aE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) (!plus) 0).exc) :
    Farey.mulI x + (texV1Odd ((parentsAt (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two)).current .odd) - ((0 : ℤ), (1 : ℤ))) ∉
      (oHead S pO pE aO aE (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) plus 0).exc := by
  intro hz
  apply hx
  obtain ⟨htr2, hst2⟩ := trailing_special Digit.three Digit.two (by decide) j k
  obtain ⟨htr3, hst3⟩ := trailing_special Digit.two Digit.three (by decide) j k
  have hTD2 : (!(List.replicate (j + 1) Digit.two).isEmpty &&
      (List.replicate (j + 1) Digit.two).all (fun d => decide (d = Digit.two))) = true := by simp
  have hTD3 : (!(List.replicate (j + 1) Digit.three).isEmpty &&
      (List.replicate (j + 1) Digit.three).all (fun d => decide (d = Digit.three))) = true := by simp
  have hW2 := W1Odd_special (j + 1) k Digit.two Digit.three (by decide) (by decide)
  have hW3 := W1Odd_special (j + 1) k Digit.three Digit.two (by decide) (by decide)
  simp only [oHead, hst3, hTD3, regs_threes_snd', regOdo, hdO, len_d, Bool.true_and, beq_self_eq_true, ↓reduceIte,
    Set.mem_setOf_eq] at hz
  simp only [eHead, hst2, hTD2, regs_twos_fst', regOdo, hdR, len_d, Bool.true_and, beq_self_eq_true, ↓reduceIte,
    Set.mem_setOf_eq]
  cases plus
  · refine exc_transfer_O (2 * (j : ℤ) + 3) (by omega) _ _ _ _ _ _ _ _ ?_ ?_ ?_ (Or.inr ⟨rfl, rfl⟩) hz.1 hz.2
    all_goals sp_pos2
  · refine exc_transfer_O (2 * (j : ℤ) + 3) (by omega) _ _ _ _ _ _ _ _ ?_ ?_ ?_ (Or.inl ⟨rfl, rfl⟩) hz.1 hz.2
    all_goals sp_pos2

/-! ### The tip of the short odd case

In the short case the image of one tip of the copy of `T^d_{1/1}` in the even L-correction at `2^(j+1) 3^k` is off the kept
side of the odd child of `3^(j+1) 2^k`. The tip lies in the first head of that L-correction (the alternate odd tile of `2^j`,
`lemma:basecase_2k_odd_alt`), which has a neighbouring point on both kept sides. -/

open FLatticePaper.Construction (paperNearStairAltTile)
open FLatticePaper.Tiles.JointRot (OnSides)
open FLatticePaper.Tiles.JointFamily (paperLSides printedEvenSides)

theorem vAux_append (rev : Bool) : ∀ (w : BinaryWord) (c : GInt) (x y : Letter), w.getLast? = some y →
    VerticalStepOne.vAux rev (w ++ [x]) c =
      VerticalStepOne.vAux rev w c ++ [(letterZTile x, lastPosOf (VerticalStepOne.vAux rev w c) + stepV rev y x)]
  | [], _, _, _, h => by simp at h
  | [a], c, x, y, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h
    simp [VerticalStepOne.vAux, lastPosOf]
  | a :: b :: rest, c, x, y, h => by
    have ih := vAux_append rev (b :: rest) (c + stepV rev a b) x y (by simpa [List.getLast?_cons_cons] using h)
    have hne : VerticalStepOne.vAux rev (b :: rest) (c + stepV rev a b) ≠ [] := by
      cases rest <;> simp [VerticalStepOne.vAux]
    rw [show (a :: b :: rest) ++ [x] = a :: b :: (rest ++ [x]) from rfl, VerticalStepOne.vAux,
      show b :: (rest ++ [x]) = (b :: rest) ++ [x] from rfl, ih, VerticalStepOne.vAux, lastPos_cons_of_ne _ _ hne]
    simp

/-- The second-to-last tile of a reversed vertical string. -/
theorem vRev_last2 (r : BinaryWord) (a b : Letter) (c : GInt) :
    (letterZTile a, lastPosOf (vRevStringAt (r ++ [a, b]) c) - vRevOffset a b) ∈ vRevStringAt (r ++ [a, b]) c := by
  rw [VerticalStepOne.vRevStringAt_eq, show r ++ [a, b] = (r ++ [a]) ++ [b] by simp,
    vAux_append true (r ++ [a]) c b a (by simp), lastPos_append_single]
  have hlast := CornerValues.vAux_last_fst true (r ++ [a]) c
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.map_some] at hlast
  have hm := JointRot.last_mem_lastPos _ _ hlast
  simp only [stepV, ↓reduceIte, add_sub_cancel_right]
  exact List.mem_append_left _ hm

/-- (s = +) The first head of the even L-correction at `2^(j+1) 3^k` starts at the tip of the copy of `T^d_{1/1}`. -/
theorem pos_tip_T (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (j k : ℕ) :
    (eHead S pO pE aO aE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true 0).off = (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).2.1)) + ((1 : ℤ), (1 : ℤ)) + ((-1 : ℤ), (1 : ℤ)) := by
  have hW2 := W1Odd_special (j + 1) k Digit.two Digit.three (by decide) (by decide)
  have hW3 := W1Odd_special (j + 1) k Digit.three Digit.two (by decide) (by decide)
  obtain ⟨htr2, hst2⟩ := trailing_special Digit.three Digit.two (by decide) j k
  obtain ⟨htr3, hst3⟩ := trailing_special Digit.two Digit.three (by decide) j k
  simp only [eHead]
  sp_pos2

/-- (s = -) The tip of the copy of `T^d_{1/1}` is the point `(d, 3d - 4)` of the first head, `d = 2j + 3`. -/
theorem pos_tip_F (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (j k : ℕ) :
    (eHead S pO pE aO aE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false 0).off + (2 * (j : ℤ) + 3, 6 * (j : ℤ) + 5) =
      (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false).2.1)) + ((1 : ℤ), (1 : ℤ)) + ((1 : ℤ), (-1 : ℤ)) := by
  have hW2 := W1Odd_special (j + 1) k Digit.two Digit.three (by decide) (by decide)
  have hW3 := W1Odd_special (j + 1) k Digit.three Digit.two (by decide) (by decide)
  obtain ⟨htr2, hst2⟩ := trailing_special Digit.three Digit.two (by decide) j k
  obtain ⟨htr3, hst3⟩ := trailing_special Digit.two Digit.three (by decide) j k
  simp only [eHead]
  sp_pos2

theorem eHead0_exc (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (w : Word) (plus : Bool) (x : Site)
    (hx : x ∈ (eHead S pO pE aO aE w plus 0).exc) :
    x - (eHead S pO pE aO aE w plus 0).off + ((0 : ℤ), (1 : ℤ)) ∈
      paperNearStairAltA (2 * ((JointFamily.stripTrailing Digit.three w).length : ℤ) + 1) := by
  simp only [eHead] at hx ⊢
  split_ifs at hx
  · exact hx.1
  · simp at hx

theorem eHead0_odo (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (j k : ℕ) (sg : Bool) :
    (eHead S pO pE aO aE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) sg 0).odo = aO (List.replicate j Digit.two) := by
  obtain ⟨-, hst2⟩ := trailing_special Digit.three Digit.two (by decide) j k
  simp only [eHead, hst2, regs_twos_fst', regOdo]

theorem near_mem (d a b : ℤ) (h : 0 ≤ a ∧ a ≤ d ∧ 1 ≤ b ∧ b ≤ 3 * d - 3 ∧ -1 ≤ b - a ∧ b - a ≤ 2 * d - 1) :
    ((a, b) : Site) ∈ paperNearStairAltTile d := by
  simp only [paperNearStairAltTile, Set.mem_union]
  exact Or.inr h

theorem near_A (d a b : ℤ) (h : ((a, b) : Site) ∈ paperNearStairAltA d) :
    (-1 ≤ a ∧ a ≤ 0 ∧ b = 2 * d) ∨ (d ≤ a ∧ a ≤ d + 1 ∧ b = d - 2) := by
  simpa [paperNearStairAltA] using h

/-- (s = +, short) The tip `(-1, 1)` of the copy of `T^d_{1/1}` lies in the first head of the even L-correction at
`2^(j+1) 3^k`, with the neighbouring point `(0, 1)` of the copy on both kept sides. -/
theorem tip_F (S : WeakData) (hone : S.oneO.dom = oneTile) (pO pE aO aE : Word → PartialOdometer) (j k : ℕ)
    (hA : ∀ x : Site, x ∈ (aO (List.replicate j Digit.two)).dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (j : ℤ) + 3)) (B : Piece) (hB : B ∈ eMid S pO pE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true) (x : Site) (hx : x ∈ B.placed)
    (hoff : ¬ OnSides (hWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false) (vWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false) (paperLSides true false false false)
      (Farey.mulI x + (texV1Odd ((parentsAt (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two)).current .odd) - ((0 : ℤ), (1 : ℤ))))) :
    x ∈ (eHead S pO pE aO aE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true 0).placed ∧ x ∉ (eHead S pO pE aO aE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true 0).exc ∧
      ∃ y ∈ (eHead S pO pE aO aE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true 0).placed, y ∉ (eHead S pO pE aO aE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true 0).exc ∧
        OnSides (hWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true) (vWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true) (paperLSides false false true false) y ∧
        OnSides (hWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false) (vWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false) (paperLSides true false false false) (Farey.mulI y + (texV1Odd ((parentsAt (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two)).current .odd) - ((0 : ℤ), (1 : ℤ)))) := by
  obtain ⟨-, hst2⟩ := trailing_special Digit.three Digit.two (by decide) j k
  have hside : ∀ y ∈ B.placed, y ≠ (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).2.1)) + ((1 : ℤ), (1 : ℤ)) + ((-1 : ℤ), (1 : ℤ)) →
      OnSides (hWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false) (vWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false) (paperLSides true false false false) (Farey.mulI y + (texV1Odd ((parentsAt (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two)).current .odd) - ((0 : ℤ), (1 : ℤ)))) :=
    fun y hy hne => ⟨.vPlus, by simp [paperLSides], cells_O_O_plus_short S hone pO pE j k B hB y hy hne⟩
  have hxt : x = (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).2.1)) + ((1 : ℤ), (1 : ℤ)) + ((-1 : ℤ), (1 : ℤ)) := by
    by_contra h; exact hoff (hside x hx h)
  have hpl : ∀ y : Site, y - (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).2.1)) - ((1 : ℤ), (1 : ℤ)) - ((-1 : ℤ), (1 : ℤ)) + ((0 : ℤ), (1 : ℤ)) ∈
      paperNearStairAltTile (2 * (j : ℤ) + 3) → y ∈ (eHead S pO pE aO aE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true 0).placed := by
    intro y hy
    rw [JointRot.mem_placed, eHead0_odo, hA, pos_tip_T]
    simpa only [sub_add_eq_sub_sub] using hy
  have hex : ∀ y : Site, y ∈ (eHead S pO pE aO aE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true 0).exc →
      y - (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).2.1)) - ((1 : ℤ), (1 : ℤ)) - ((-1 : ℤ), (1 : ℤ)) + ((0 : ℤ), (1 : ℤ)) ∈
        paperNearStairAltA (2 * (j : ℤ) + 3) := by
    intro y hy
    have h := eHead0_exc S pO pE aO aE _ true y hy
    have hd : 2 * ((JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)).length : ℤ) + 1 = 2 * (j : ℤ) + 3 := by
      rw [hst2, len_d]
    rw [pos_tip_T, hd] at h
    simpa only [sub_add_eq_sub_sub] using h
  rcases mid_mem S pO pE j k true B hB with ⟨-, hob, hoffB⟩ | ⟨hob, hoffB⟩
  · exfalso
    rw [JointRot.mem_placed, hob, hone, hoffB, hxt, mem_oneTile_iff,
      show ∀ m : Site, m + ((1 : ℤ), (1 : ℤ)) + ((-1 : ℤ), (1 : ℤ)) - m = ((0 : ℤ), (2 : ℤ)) from fun m => by pt_eq] at hx
    simp [tileShape] at hx
  · have hy : (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).2.1)) + ((1 : ℤ), (1 : ℤ)) + ((0 : ℤ), (1 : ℤ)) ∈ B.placed := by
      rw [JointRot.mem_placed, hob, hoffB, add_sub_cancel_left]
      simp [JointFamily.enlOdo, tileShape]
    have hne : (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).2.1)) + ((1 : ℤ), (1 : ℤ)) + ((0 : ℤ), (1 : ℤ)) ≠
        (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).2.1)) + ((1 : ℤ), (1 : ℤ)) + ((-1 : ℤ), (1 : ℤ)) := by
      intro h; have := congrArg Prod.fst h; simp at this
    subst hxt
    refine ⟨hpl _ ?_, fun h => ?_, _, hpl _ ?_, fun h => ?_,
      ⟨.hPlus, by simp [paperLSides], cells_O_R_plus S hone pO pE j k B hB _ hy⟩, hside _ hy hne⟩
    · rw [show ∀ m : Site, m + ((1 : ℤ), (1 : ℤ)) + ((-1 : ℤ), (1 : ℤ)) - m - ((1 : ℤ), (1 : ℤ)) - ((-1 : ℤ), (1 : ℤ)) +
        ((0 : ℤ), (1 : ℤ)) = ((0 : ℤ), (1 : ℤ)) from fun m => by pt_eq]
      exact near_mem _ _ _ (by omega)
    · have h' := hex _ h
      rw [show ∀ m : Site, m + ((1 : ℤ), (1 : ℤ)) + ((-1 : ℤ), (1 : ℤ)) - m - ((1 : ℤ), (1 : ℤ)) - ((-1 : ℤ), (1 : ℤ)) +
        ((0 : ℤ), (1 : ℤ)) = ((0 : ℤ), (1 : ℤ)) from fun m => by pt_eq] at h'
      have := near_A _ _ _ h'; omega
    · rw [show ∀ m : Site, m + ((1 : ℤ), (1 : ℤ)) + ((0 : ℤ), (1 : ℤ)) - m - ((1 : ℤ), (1 : ℤ)) - ((-1 : ℤ), (1 : ℤ)) +
        ((0 : ℤ), (1 : ℤ)) = ((1 : ℤ), (1 : ℤ)) from fun m => by pt_eq]
      exact near_mem _ _ _ (by omega)
    · have h' := hex _ h
      rw [show ∀ m : Site, m + ((1 : ℤ), (1 : ℤ)) + ((0 : ℤ), (1 : ℤ)) - m - ((1 : ℤ), (1 : ℤ)) - ((-1 : ℤ), (1 : ℤ)) +
        ((0 : ℤ), (1 : ℤ)) = ((1 : ℤ), (1 : ℤ)) from fun m => by pt_eq] at h'
      have := near_A _ _ _ h'; omega

/-- (s = -, short) The tip `(1, -1)` of the copy of `T^d_{1/1}` is the point `(d, 3d - 4)` of the first head of the even
L-correction at `2^(j+1) 3^k`, and its left neighbour in the head lies on the second-to-last tiles of both kept sides. -/
theorem tip_T (S : WeakData) (hone : S.oneO.dom = oneTile) (pO pE aO aE : Word → PartialOdometer) (j k : ℕ)
    (hA : ∀ x : Site, x ∈ (aO (List.replicate j Digit.two)).dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (j : ℤ) + 3)) (B : Piece) (hB : B ∈ eMid S pO pE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false) (x : Site) (hx : x ∈ B.placed)
    (hoff : ¬ OnSides (hWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false) (vWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false) (paperLSides true false true false)
      (Farey.mulI x + (texV1Odd ((parentsAt (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two)).current .odd) - ((0 : ℤ), (1 : ℤ))))) :
    x ∈ (eHead S pO pE aO aE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false 0).placed ∧ x ∉ (eHead S pO pE aO aE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false 0).exc ∧
      ∃ y ∈ (eHead S pO pE aO aE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false 0).placed, y ∉ (eHead S pO pE aO aE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false 0).exc ∧
        OnSides (hWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true) (vWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true) (paperLSides false false false false) y ∧
        OnSides (hWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false) (vWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false) (paperLSides true false true false) (Farey.mulI y + (texV1Odd ((parentsAt (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two)).current .odd) - ((0 : ℤ), (1 : ℤ)))) := by
  obtain ⟨-, hst2⟩ := trailing_special Digit.three Digit.two (by decide) j k
  have hxt : x = (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false).2.1)) + ((1 : ℤ), (1 : ℤ)) + ((1 : ℤ), (-1 : ℤ)) := by
    by_contra h
    exact hoff ⟨.vMinus, by simp [paperLSides], cells_O_O_minus_short S hone pO pE j k B hB x hx h⟩
  have hoff0 : (eHead S pO pE aO aE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false 0).off = (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false).2.1)) + ((1 : ℤ), (1 : ℤ)) + ((1 : ℤ), (-1 : ℤ)) - (2 * (j : ℤ) + 3, 6 * (j : ℤ) + 5) :=
    eq_sub_of_add_eq (pos_tip_F S pO pE aO aE j k)
  have hpl : ∀ y : Site, y - ((evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false).2.1)) + ((1 : ℤ), (1 : ℤ)) + ((1 : ℤ), (-1 : ℤ)) - (2 * (j : ℤ) + 3, 6 * (j : ℤ) + 5)) + ((0 : ℤ), (1 : ℤ)) ∈
      paperNearStairAltTile (2 * (j : ℤ) + 3) → y ∈ (eHead S pO pE aO aE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false 0).placed := by
    intro y hy
    rw [JointRot.mem_placed, eHead0_odo, hA, hoff0]
    exact hy
  have hex : ∀ y : Site, y ∈ (eHead S pO pE aO aE (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false 0).exc →
      y - ((evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false).2.1)) + ((1 : ℤ), (1 : ℤ)) + ((1 : ℤ), (-1 : ℤ)) - (2 * (j : ℤ) + 3, 6 * (j : ℤ) + 5)) + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltA (2 * (j : ℤ) + 3) := by
    intro y hy
    have h := eHead0_exc S pO pE aO aE _ false y hy
    have hd : 2 * ((JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)).length : ℤ) + 1 = 2 * (j : ℤ) + 3 := by
      rw [hst2, len_d]
    rw [hoff0, hd] at h
    exact h
  have e1 : ∀ m : Site, m + ((1 : ℤ), (1 : ℤ)) + ((1 : ℤ), (-1 : ℤ)) -
      (m + ((1 : ℤ), (1 : ℤ)) + ((1 : ℤ), (-1 : ℤ)) - (2 * (j : ℤ) + 3, 6 * (j : ℤ) + 5)) + ((0 : ℤ), (1 : ℤ)) =
      (2 * (j : ℤ) + 3, 6 * (j : ℤ) + 6) := fun m => by pt_eq
  have e2 : ∀ m : Site, m + ((1 : ℤ), (1 : ℤ)) + ((1 : ℤ), (-1 : ℤ)) + ((-1 : ℤ), (0 : ℤ)) -
      (m + ((1 : ℤ), (1 : ℤ)) + ((1 : ℤ), (-1 : ℤ)) - (2 * (j : ℤ) + 3, 6 * (j : ℤ) + 5)) + ((0 : ℤ), (1 : ℤ)) =
      (2 * (j : ℤ) + 2, 6 * (j : ℤ) + 6) := fun m => by pt_eq
  subst hxt
  refine ⟨hpl _ ?_, fun h => ?_, (evenLInitOff (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false + JointFamily.altOff (JointFamily.stripTrailing Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) ((JointFamily.trailingCount Digit.three (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) : ℤ) • (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false).1 + (eK (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) false).2.1)) + ((1 : ℤ), (1 : ℤ)) + ((1 : ℤ), (-1 : ℤ)) + ((-1 : ℤ), (0 : ℤ)), hpl _ ?_, fun h => ?_, ?_, ?_⟩
  · rw [e1]; exact near_mem _ _ _ (by omega)
  · have h' := hex _ h
    rw [e1] at h'
    have := near_A _ _ _ h'; omega
  · rw [e2]; exact near_mem _ _ _ (by omega)
  · have h' := hex _ h
    rw [e2] at h'
    have := near_A _ _ _ h'; omega
  · -- the second-to-last tile of the reversed horizontal string
    refine ⟨.hMinus, by simp [paperLSides], ?_⟩
    show _ ∈ placedSites (hRevStringAt (hWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).reverse (lastPosOf (vRevStringAt (vWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).reverse 0)))
    obtain ⟨r, hr⟩ := (ends_twos_threes j k).2.2.1
    have hrev : (hWordOf (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) true).reverse = r.reverse ++ [Letter.q, Letter.q] := by rw [hr]; simp
    rw [StdCornerAnchors.stdAnchorY_even]
    obtain ⟨-, pr, h0⟩ := hRev_last r.reverse Letter.q Letter.q (texV2 (fracEven (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three)) + ((1 : ℤ), (-2 : ℤ)))
    rw [← hrev, GlueStringDecomp.lp_top_even] at h0
    simp only [hRevOffset] at h0
    rw [pos_O_R_minus]
    exact mem_of_tile h0 (1, 0) (ReflectedCover.R2_sub pr _ (by simp [tileShape])) _ (by pt_eq)
  · -- the second-to-last tile of the reversed vertical string
    refine ⟨.vMinus, by simp [paperLSides], ?_⟩
    show _ ∈ placedSites (vRevStringAt (vWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false).reverse 0)
    obtain ⟨r, hr⟩ := (ends_threes_twos j k).2.2.2.2.1
    have hrev : (vWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false).reverse = r.reverse ++ [Letter.p, Letter.p] := by rw [hr]; simp
    have h2 := vRev_last2 r.reverse Letter.p Letter.p 0
    rw [← hrev, StdCornerAnchors.stdAnchorY_odd] at h2
    simp only [letterZTile, vRevOffset] at h2
    rw [z_add, z_add, pos_O_O_minus]
    exact mem_of_tile h2 (1, 2) (by simp [tileShape]) _ (by pt_eq)

/-! ### Assembling `SpecialCells` -/

open FLatticePaper.Tiles.JointFamily (JointData JSlice below EvenLDefined OddLDefined stripTrailing trailingCount paperLSides
  printedEvenSides)
open FLatticePaper.Tiles.JointRot (OnSides SpecialCells)

theorem special_form (d e : Digit) (w : Word) (hsp : stripTrailing d w ≠ [] ∧ ∀ x ∈ stripTrailing d w, x = e) :
    ∃ j k : ℕ, w = List.replicate (j + 1) e ++ List.replicate k d := by
  have hw := JointRot.strip_append_replicate d w
  have hrep : stripTrailing d w = List.replicate (stripTrailing d w).length e := List.eq_replicate_iff.mpr ⟨rfl, hsp.2⟩
  obtain ⟨j, hj⟩ : ∃ j, (stripTrailing d w).length = j + 1 :=
    ⟨(stripTrailing d w).length - 1, by have := List.length_pos_of_ne_nil hsp.1; omega⟩
  refine ⟨j, trailingCount d w, ?_⟩
  rw [hj] at hrep
  rw [← hrep]
  exact hw.symm

/-- What `SpecialCells` needs beyond the cells of the middle pieces: the correspondence of the exceptional points of the first
heads, and, for a point of a middle piece of the odd kind whose image is off the kept sides (the tip in the short case), a head of
the rotated correction through it with a point on both kept sides. -/
def SpecialRest (D : JointData) (f : Word → JSlice) (n : ℕ) : Prop :=
  ∀ w : Word, w.length = n →
    (EvenLDefined w → (stripTrailing Digit.three w ≠ [] ∧ ∀ d ∈ stripTrailing Digit.three w, d = Digit.two) →
      ∀ plus : Bool,
      let g := below f w
      let c := texV1Even ((parentsAt w).current .even) - ((0 : ℤ), (1 : ℤ))
      let s := plus != W1Odd w
      ∀ x ∈ (oHead D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd) (fun u => (g u).aEven)
          (swapW w) s 0).placed,
        x ∉ (oHead D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd) (fun u => (g u).aEven)
          (swapW w) s 0).exc →
        Farey.mulI x + c ∉ (eHead D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd)
          (fun u => (g u).aEven) w plus 0).exc) ∧
    (OddLDefined w → (stripTrailing Digit.two w ≠ [] ∧ ∀ d ∈ stripTrailing Digit.two w, d = Digit.three) →
      ∀ plus elong : Bool,
      let g := below f w
      let c := texV1Odd ((parentsAt w).current .odd) - ((0 : ℤ), (1 : ℤ))
      let s := plus == W1Odd w
      let Rs := hWordOf (swapW w) true
      let Rv := vWordOf (swapW w) true
      let sR := D.lSides false (W1Odd (swapW w)) s elong
      let sO := D.lSides true (W1Odd w) plus elong
      (∀ B ∈ eMid D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (swapW w) s, ∀ x ∈ B.placed, x ∉ B.exc →
        ¬ OnSides (hWordOf w false) (vWordOf w false) sO (Farey.mulI x + c) →
        ∃ r ∈ (List.range (2 * (trailingCount Digit.two w + 1) - (if elong then 0 else 1))).map
            (eHead D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd) (fun u => (g u).aEven)
              (swapW w) s),
          x ∈ r.placed ∧ x ∉ r.exc ∧ ∃ y ∈ r.placed, y ∉ r.exc ∧
            OnSides Rs Rv sR y ∧ OnSides (hWordOf w false) (vWordOf w false) sO (Farey.mulI y + c)) ∧
      (∀ x ∈ (eHead D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd) (fun u => (g u).aEven)
          (swapW w) s 0).placed,
        x ∉ (eHead D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd) (fun u => (g u).aEven)
          (swapW w) s 0).exc →
        Farey.mulI x + c ∉ (oHead D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd)
          (fun u => (g u).aEven) w plus 0).exc))

/-- `SpecialRest` from the base tiles below the level: the last stems are the standard tiles of `2^j` and `3^j`, and the first
heads of the even L-corrections the alternate odd tile of `2^j`. -/
theorem specialRest_of (D : JointData) (hone : D.S.oneO.dom = oneTile) (hlS : D.lSides = paperLSides)
    (f : Word → JSlice) (n : ℕ)
    (hdO : ∀ j : ℕ, j < n → (f (List.replicate j Digit.two)).tOdd.dom = nstairN (2 * (j : ℤ) + 3))
    (hdE : ∀ j : ℕ, j < n → (f (List.replicate j Digit.three)).tEven.dom = stairF (2 * (j : ℤ) + 3))
    (hdA : ∀ j : ℕ, j < n → ∀ x : Site, x ∈ (f (List.replicate j Digit.two)).aOdd.dom ↔
      x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (j : ℤ) + 3)) :
    SpecialRest D f n := by
  intro w hw
  refine ⟨fun hdef hsp plus => ?_, fun hdef hsp plus elong => ?_⟩
  · obtain ⟨j, k, rfl⟩ := special_form Digit.three Digit.two w hsp
    have hW := W1Odd_special (j + 1) k Digit.two Digit.three (by decide) (by decide)
    have hsw := swap_twos_threes (j + 1) k
    have hj : j < n := by rw [← hw]; simp; omega
    have hbel : ∀ u : Word, u.length = j → below f (List.replicate (j + 1) Digit.two ++ List.replicate k Digit.three) u = f u := fun u hu => if_pos (by simp [hu]; omega)
    simp only [hW, hsw, Bool.bne_false]
    intro x _ hx
    refine exc_E D.S _ _ _ _ j k plus ?_ ?_ x hx
    · show (below f _ _).tOdd.dom = _
      rw [hbel _ (by simp)]; exact hdO j hj
    · show (below f _ _).tEven.dom = _
      rw [hbel _ (by simp)]; exact hdE j hj
  · obtain ⟨j, k, rfl⟩ := special_form Digit.two Digit.three w hsp
    have hW := W1Odd_special (j + 1) k Digit.three Digit.two (by decide) (by decide)
    have hW' := W1Odd_special (j + 1) k Digit.two Digit.three (by decide) (by decide)
    have hsw := swap_threes_twos (j + 1) k
    have hj : j < n := by rw [← hw]; simp; omega
    have hbel : ∀ u : Word, u.length = j → below f (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) u = f u := fun u hu => if_pos (by simp [hu]; omega)
    have hO : ((fun u => (below f (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) u).tOdd) (List.replicate j Digit.two)).dom = nstairN (2 * (j : ℤ) + 3) := by
      show (below f _ _).tOdd.dom = _
      rw [hbel _ (by simp)]; exact hdO j hj
    have hE : ((fun u => (below f (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) u).tEven) (List.replicate j Digit.three)).dom = stairF (2 * (j : ℤ) + 3) := by
      show (below f _ _).tEven.dom = _
      rw [hbel _ (by simp)]; exact hdE j hj
    have hA : ∀ x : Site, x ∈ ((fun u => (below f (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) u).aOdd) (List.replicate j Digit.two)).dom ↔
        x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (j : ℤ) + 3) := by
      show ∀ x : Site, x ∈ (below f _ _).aOdd.dom ↔ _
      rw [hbel _ (by simp)]; exact hdA j hj
    have h0 : 0 ∈ List.range (2 * (JointFamily.trailingCount Digit.two (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) + 1) - (if elong then 0 else 1)) := by
      rw [List.mem_range]; split_ifs <;> omega
    cases plus <;> cases elong <;>
      simp only [hW, hW', hsw, hlS, beq_self_eq_true, beq_false, Bool.not_true] at h0 ⊢
    · refine ⟨fun B hB x hx _ hoff => ⟨_, List.mem_map.mpr ⟨0, h0, rfl⟩,
        tip_F D.S hone _ _ _ _ j k hA B hB x hx hoff⟩, fun x _ hx => exc_O D.S _ _ _ _ j k false hE hO x hx⟩
    · refine ⟨fun B hB x hx _ hoff => absurd ⟨.hPlus, by simp [paperLSides],
        cells_O_O_plus_elong D.S hone _ _ j k B hB x hx⟩ hoff, fun x _ hx => exc_O D.S _ _ _ _ j k false hE hO x hx⟩
    · refine ⟨fun B hB x hx _ hoff => ⟨_, List.mem_map.mpr ⟨0, h0, rfl⟩,
        tip_T D.S hone _ _ _ _ j k hA B hB x hx hoff⟩, fun x _ hx => exc_O D.S _ _ _ _ j k true hE hO x hx⟩
    · refine ⟨fun B hB x hx _ hoff => absurd ⟨.hMinus, by simp [paperLSides],
        cells_O_O_minus_elong D.S hone _ _ j k B hB x hx⟩ hoff, fun x _ hx => exc_O D.S _ _ _ _ j k true hE hO x hx⟩

/-- The base tiles below the level for the paper data: from the joint slices of the words shorter than `n`. -/
theorem base_doms (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (n : ℕ) (hG : JointInduction.GoodBelow D f n) (j : ℕ) (hj : j < n) :
    (f (List.replicate j Digit.two)).tOdd.dom = nstairN (2 * (j : ℤ) + 3) ∧
      (f (List.replicate j Digit.three)).tEven.dom = stairF (2 * (j : ℤ) + 3) ∧
      ∀ x : Site, x ∈ (f (List.replicate j Digit.two)).aOdd.dom ↔
        x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (j : ℤ) + 3) := by
  obtain ⟨-, hWA2, hTP2, -⟩ := (hG (List.replicate j Digit.two) (by simpa using hj)).1
  obtain ⟨-, -, hTP3, -⟩ := (hG (List.replicate j Digit.three) (by simpa using hj)).1
  have hb2 : Standard.IsBase (List.replicate j Digit.two) := Or.inr (Or.inr fun d hd => List.eq_of_mem_replicate hd)
  refine ⟨?_, ?_, ?_⟩
  · rw [hTP2.2.2.2.2.2.2.2.2.1, hS]
    exact BaseInvariant.oddTile_two j
  · rw [hTP3.2.2.2.2.2.2.2.2.2.1, hS]
    exact BaseInvariant.evenTile_three j
  · rw [(hTP2.1 hb2).2.2.1]
    have hc := hWA2.2.2.1 hb2
    rw [hA] at hc
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simpa using (hc.1 rfl).1
    · exact (hc.2.2 j hpos rfl).1

/-- **`SpecialCells` for the paper data**, given `SpecialRest`: the cells of the middle pieces lie on the kept sides (the cell
lemmas above). -/
theorem specialCells_of (D : JointData) (hz : D.S.zeroO.dom = zeroTile) (hone : D.S.oneO.dom = oneTile)
    (hlS : D.lSides = paperLSides) (f : Word → JSlice) (n : ℕ) (hrest : SpecialRest D f n) : SpecialCells D f n := by
  intro w hw
  refine ⟨fun hdef hsp plus elong => ?_, fun hdef hsp plus elong => ?_⟩
  · have hexc := (hrest w hw).1 hdef hsp plus
    obtain ⟨j, k, rfl⟩ := special_form Digit.three Digit.two w hsp
    have hW := W1Odd_special (j + 1) k Digit.two Digit.three (by decide) (by decide)
    have hW' := W1Odd_special (j + 1) k Digit.three Digit.two (by decide) (by decide)
    have hsw := swap_twos_threes (j + 1) k
    simp only [hW, hW', hsw, hlS, Bool.bne_false] at hexc ⊢
    refine ⟨fun x hx => ⟨?_, ?_⟩, hexc⟩
    · cases plus
      · exact ⟨.vPlus, by cases elong <;> simp [paperLSides], cells_E_R_minus _ hz _ _ j k x hx⟩
      · exact ⟨.vMinus, by cases elong <;> simp [paperLSides], cells_E_R_plus _ hz _ _ j k x hx⟩
    · cases plus
      · exact ⟨.hMinus, by cases elong <;> simp [paperLSides, printedEvenSides], cells_E_O_minus _ hz _ _ j k x hx⟩
      · exact ⟨.hPlus, by cases elong <;> simp [paperLSides, printedEvenSides], cells_E_O_plus _ hz _ _ j k x hx⟩
  · have hr := (hrest w hw).2 hdef hsp plus elong
    obtain ⟨j, k, rfl⟩ := special_form Digit.two Digit.three w hsp
    have hW := W1Odd_special (j + 1) k Digit.three Digit.two (by decide) (by decide)
    have hW' := W1Odd_special (j + 1) k Digit.two Digit.three (by decide) (by decide)
    have hsw := swap_threes_twos (j + 1) k
    simp only [hW, hW', hsw, hlS, beq_false] at hr ⊢
    obtain ⟨htip, hexc⟩ := hr
    refine ⟨fun B hB x hx hxe => ?_, hexc⟩
    by_cases hon : OnSides (hWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false)
      (vWordOf (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two) false)
      (paperLSides true false plus elong)
      (Farey.mulI x + (texV1Odd ((parentsAt (List.replicate (j + 1) Digit.three ++ List.replicate k Digit.two)).current .odd) -
        ((0 : ℤ), (1 : ℤ))))
    · refine Or.inl ⟨?_, hon⟩
      cases plus
      · exact ⟨.hPlus, by cases elong <;> simp [paperLSides, printedEvenSides], cells_O_R_plus _ hone _ _ j k B hB x hx⟩
      · exact ⟨.hMinus, by cases elong <;> simp [paperLSides, printedEvenSides], cells_O_R_minus _ hone _ _ j k B hB x hx⟩
    · exact Or.inr (htip B hB x hx hxe hon)

/-- **`SpecialCells` for the paper data** at every level of the induction. -/
theorem specialCells_paper (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hlS : D.lSides = paperLSides) (f : Word → JSlice) (n : ℕ) (hL : JointRot.LevelHyp D f n) : SpecialCells D f n :=
  specialCells_of D (by rw [hS]; rfl) (by rw [hS]; rfl) hlS f n
    (specialRest_of D (by rw [hS]; rfl) hlS f n (fun j hj => (base_doms D hS hA f n hL.1 j hj).1)
      (fun j hj => (base_doms D hS hA f n hL.1 j hj).2.1) (fun j hj => (base_doms D hS hA f n hL.1 j hj).2.2))

/-- The rotation step of the joint induction for the paper data, from the base rotations and the connectivity of the
alternate and L decompositions. -/
theorem rotStepInput_paper (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hlS : D.lSides = paperLSides) (hBR : JointRot.BaseRot D)
    (hconnA : ∀ (f : Word → JSlice) (n : ℕ), JointRot.LevelHyp D f n →
      ∀ w : Word, w.length = n → ¬ Standard.IsBase w → JointRot.ConnectedAlt D (below f w) w)
    (hconnL : ∀ (f : Word → JSlice) (n : ℕ), JointRot.LevelHyp D f n → ∀ w : Word, w.length = n →
      JointRot.ConnectedL D (below f w) w) :
    JointInduction.RotStepInput D :=
  JointRot.rotStepInput_of_cells D (JointRot.baseSlopes_paper D hS hA) hBR hlS hconnA hconnL
    (fun f n hL => specialCells_paper D hS hA hlS f n hL)

end FLatticePaper.Tiles.SpecialCells
