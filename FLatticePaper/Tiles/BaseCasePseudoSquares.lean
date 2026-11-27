import FLatticePaper.Tiles.PseudoSquareAlong
import FLatticePaper.Construction.BaseCaseLaplacian

/-! Base-case pseudo-squares, part A: the walk points that give the starts of the strings. For a general pair `(w1, w2)`
the walk of `pseudoBoundaryWord w1 w2` from `c` is at `c + Σw1` after the lower side and at `c + Σw2` after the top side,
so the starts of `alongStrings` are explicit in the sums of the two G-words. -/

namespace FLatticePaper.Tiles

open FLatticePaper.Construction (paperStairTile paperLadderTile paperLadderA paperLadderB paperLadderC paperLadderD innerBoundary)

theorem walk_getElem_append (u v : F2Word) (c : GInt) :
    (F2Word.walk c (u ++ v))[u.length]? = some (c + F2Word.sum u) := by
  induction u generalizing c with
  | nil => cases v <;> simp [F2Word.walk, F2Word.sum, List.scanl]
  | cons x u ih =>
    have h := ih (c + x.vec)
    simp only [F2Word.walk, List.cons_append, List.scanl_cons, List.length_cons, List.getElem?_cons_succ] at h ⊢
    simp only [F2Word.sum, List.map_cons, List.sum_cons] at h ⊢
    rw [h, add_assoc]

theorem unit4_vec_neg (x : Unit4) : x.neg.vec = -x.vec := by
  cases x <;> simp [Unit4.neg, Unit4.vec]

theorem sum_map_neg (w : F2Word) : F2Word.sum (w.map Unit4.neg) = -F2Word.sum w := by
  induction w with
  | nil => simp [F2Word.sum]
  | cons x w ih =>
    simp only [F2Word.sum, List.map_cons, List.sum_cons] at ih ⊢
    rw [unit4_vec_neg, ih, neg_add]

theorem sum_hat (w : F2Word) : F2Word.sum (F2Word.hat w) = -F2Word.sum w := by
  simp only [F2Word.hat, F2Word.sum, List.map_reverse, List.sum_reverse]
  exact sum_map_neg w

theorem sum_rev (w : F2Word) : F2Word.sum (F2Word.rev w) = F2Word.sum w := by
  unfold F2Word.rev F2Word.sum
  rw [List.map_reverse, List.sum_reverse]

theorem length_hat_rev (w : F2Word) : (F2Word.hat (F2Word.rev w)).length = w.length := by
  simp [F2Word.hat, F2Word.rev]

theorem f2sum_append (u v : F2Word) : F2Word.sum (u ++ v) = F2Word.sum u + F2Word.sum v := by
  simp [F2Word.sum, List.map_append, List.sum_append]

theorem walk_pseudo_top (c : GInt) (w1 w2 : F2Word) :
    (F2Word.walk c (pseudoBoundaryWord w1 w2)).getD (w1.length + w2.length + w1.length) c =
      c + F2Word.sum w2 := by
  have hlen : (w1 ++ w2 ++ F2Word.hat (F2Word.rev w1)).length = w1.length + w2.length + w1.length := by
    simp [length_hat_rev]
    omega
  have h := walk_getElem_append (w1 ++ w2 ++ F2Word.hat (F2Word.rev w1)) (F2Word.hat (F2Word.rev w2)) c
  rw [hlen] at h
  unfold pseudoBoundaryWord
  rw [List.getD_eq_getElem?_getD, h, Option.getD_some, f2sum_append, f2sum_append, sum_hat, sum_rev]
  abel

theorem walk_pseudo_right (c : GInt) (w1 w2 : F2Word) :
    (F2Word.walk c (pseudoBoundaryWord w1 w2)).getD w1.length c = c + F2Word.sum w1 := by
  have h := walk_getElem_append w1 (w2 ++ F2Word.hat (F2Word.rev w1) ++ F2Word.hat (F2Word.rev w2)) c
  have e : pseudoBoundaryWord w1 w2 = w1 ++ (w2 ++ F2Word.hat (F2Word.rev w1) ++ F2Word.hat (F2Word.rev w2)) := by
    simp [pseudoBoundaryWord, List.append_assoc]
  rw [e, List.getD_eq_getElem?_getD, h, Option.getD_some]

/-- The walk point after the lower side is `c + Σw1`. -/
theorem walkAt_right (c : GInt) (wh wv : BinaryWord) :
    walkAt c wh wv (gPseudo wh wv).1.length = c + F2Word.sum (gPseudo wh wv).1 := by
  unfold walkAt boundaryWalk
  exact walk_pseudo_right c _ _

/-- The walk point after the top side is `c + Σw2`. -/
theorem walkAt_top (c : GInt) (wh wv : BinaryWord) :
    walkAt c wh wv ((gPseudo wh wv).1.length + (gPseudo wh wv).2.length + (gPseudo wh wv).1.length) =
      c + F2Word.sum (gPseudo wh wv).2 := by
  unfold walkAt boundaryWalk
  exact walk_pseudo_top c _ _

/-! ### The G-sums of the stair words -/

/-- The sum of `gPair` on a pair of tiles. -/
def pairSum (a b : ZTile) : GInt := F2Word.sum (gPair a b)

theorem pairSum_zz : pairSum ZTile.zero ZTile.zero = (2, 0) := by decide
theorem pairSum_oz : pairSum ZTile.one ZTile.zero = (2, 0) := by decide
theorem pairSum_od : pairSum ZTile.one ZTile.oneD = (2, 0) := by decide
theorem pairSum_dd : pairSum ZTile.oneD ZTile.oneD = (1, 1) := by decide
theorem pairSum_dz : pairSum ZTile.oneD ZTile.zero = (1, 1) := by decide

theorem sum_flatMap_gPair (L : List (ZTile × ZTile)) :
    F2Word.sum (L.flatMap fun ab => gPair ab.1 ab.2) = (L.map fun ab => pairSum ab.1 ab.2).sum := by
  induction L with
  | nil => rfl
  | cons ab L ih => simp only [List.flatMap_cons, List.map_cons, List.sum_cons, f2sum_append, ih, pairSum]

theorem sum_gH_eq (w : BinaryWord) :
    F2Word.sum (gH w) = (((tileSeq w).zip (tileSeq w).tail).map fun ab => pairSum ab.1 ab.2).sum + (1, 0) := by
  unfold gH
  rw [f2sum_append, sum_flatMap_gPair, show F2Word.sum [Unit4.one] = (1, 0) by decide]

theorem tileSeqAux_p_rep (prev : Option Letter) (n : ℕ) :
    tileSeqAux prev (List.replicate n Letter.p) = List.replicate n ZTile.zero := by
  induction n generalizing prev with
  | zero => simp [tileSeqAux]
  | succ n ih => simp [List.replicate_succ, tileSeqAux, ih]

theorem tileSeq_q_rep_p (n : ℕ) :
    tileSeq (Letter.q :: List.replicate n Letter.p) = ZTile.one :: List.replicate n ZTile.zero := by
  simp [tileSeq, tileSeqAux, tileSeqAux_p_rep]

theorem zeroRun_sum (n : ℕ) :
    (((List.replicate (n + 1) ZTile.zero).zip (List.replicate n ZTile.zero)).map
      fun ab => pairSum ab.1 ab.2).sum = ((n : ℤ) * 2, 0) := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [List.replicate_succ, List.zip_cons_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, pairSum_zz]
    refine Prod.ext (by simp; try ring) (by simp; try ring)

theorem oneDZero_sum (n : ℕ) :
    (((List.replicate (n + 1) ZTile.oneD ++ [ZTile.zero]).zip (List.replicate n ZTile.oneD ++ [ZTile.zero])).map
      fun ab => pairSum ab.1 ab.2).sum = ((n : ℤ) + 1, (n : ℤ) + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, List.zip_cons_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, pairSum_dd]
    refine Prod.ext (by simp; try ring) (by simp; try ring)

theorem tileSeqAux_q_oneD (m : ℕ) :
    tileSeqAux (some Letter.q) (List.replicate m Letter.q ++ [Letter.p]) =
      List.replicate m ZTile.oneD ++ [ZTile.zero] := by
  induction m with
  | zero => simp [tileSeqAux]
  | succ m ih => simp [List.replicate_succ, tileSeqAux, ih]

theorem tileSeq_flip (m : ℕ) :
    tileSeq (List.replicate (m + 1) Letter.q ++ [Letter.p]) =
      ZTile.one :: (List.replicate m ZTile.oneD ++ [ZTile.zero]) := by
  rw [List.replicate_succ, List.cons_append]
  simp only [tileSeq, tileSeqAux]
  rw [tileSeqAux_q_oneD]

theorem f2sum_mulI (l : F2Word) :
    F2Word.sum (l.map Unit4.mulI) = (-(F2Word.sum l).2, (F2Word.sum l).1) := by
  induction l with
  | nil => decide
  | cons x l ih =>
    have hx : (x.mulI).vec = (-(x.vec).2, (x.vec).1) := by cases x <;> decide
    simp only [F2Word.sum, List.map_cons, List.sum_cons] at ih ⊢
    rw [hx, ih]
    refine Prod.ext (by simp; try ring) (by simp; try ring)

theorem sum_gH_stair (k : ℕ) :
    F2Word.sum (gH (Letter.q :: List.replicate (k + 1) Letter.p)) = (2 * (k : ℤ) + 3, 0) := by
  rw [sum_gH_eq, tileSeq_q_rep_p, List.tail_cons]
  have e : (ZTile.one :: List.replicate (k + 1) ZTile.zero).zip (List.replicate (k + 1) ZTile.zero) =
      (ZTile.one, ZTile.zero) :: (List.replicate (k + 1) ZTile.zero).zip (List.replicate k ZTile.zero) := by
    simp [List.replicate_succ]
  rw [e]
  simp only [List.map_cons, List.sum_cons, pairSum_oz]
  rw [zeroRun_sum]
  refine Prod.ext (by simp; try ring) (by simp; try ring)

theorem sum_gV_stair (k : ℕ) :
    F2Word.sum (gV (List.replicate (2 * k + 2) Letter.p ++ [Letter.q])) =
      (-(2 * (k : ℤ) + 1), 2 * (k : ℤ) + 4) := by
  have hf : flipW (List.replicate (2 * k + 2) Letter.p ++ [Letter.q]) =
      List.replicate (2 * k + 1 + 1) Letter.q ++ [Letter.p] := by
    simp only [flipW, List.map_append, List.map_replicate, flipLetter, List.map_cons, List.map_nil]
  unfold gV
  rw [hf, f2sum_mulI, sum_gH_eq, tileSeq_flip, List.tail_cons]
  have e : (ZTile.one :: (List.replicate (2 * k + 1) ZTile.oneD ++ [ZTile.zero])).zip
      (List.replicate (2 * k + 1) ZTile.oneD ++ [ZTile.zero]) =
      (ZTile.one, ZTile.oneD) :: ((List.replicate (2 * k + 1) ZTile.oneD ++ [ZTile.zero]).zip
        (List.replicate (2 * k) ZTile.oneD ++ [ZTile.zero])) := by
    simp [List.replicate_succ]
  rw [e]
  simp only [List.map_cons, List.sum_cons, pairSum_od]
  rw [oneDZero_sum]
  refine Prod.ext (by simp; try ring) (by simp; try ring)

/-! ### Membership of the placed rectangles (part B) -/

/-- The rectangle of a zero-one tile of type `zero` at `p`: columns `p.1, p.1+1`, rows `p.2, p.2+1, p.2+2`. -/
def zeroAt (p x : GInt) : Prop := p.1 ≤ x.1 ∧ x.1 ≤ p.1 + 1 ∧ p.2 ≤ x.2 ∧ x.2 ≤ p.2 + 2

/-- The rectangle of a zero-one tile of type `one` at `p`: columns `p.1, p.1+1`, rows `p.2, p.2+1`. -/
def oneAt (p x : GInt) : Prop := p.1 ≤ x.1 ∧ x.1 ≤ p.1 + 1 ∧ p.2 ≤ x.2 ∧ x.2 ≤ p.2 + 1

theorem mem_shape_zero (c x : GInt) : x ∈ (tileShape ZTile.zero).map (· + c) ↔ zeroAt c x := by
  unfold zeroAt
  simp only [tileShape, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false,
    Prod.ext_iff, Prod.fst_add, Prod.snd_add]
  constructor <;> intro h <;> omega

theorem mem_shape_one (c x : GInt) : x ∈ (tileShape ZTile.one).map (· + c) ↔ oneAt c x := by
  unfold oneAt
  simp only [tileShape, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false,
    Prod.ext_iff, Prod.fst_add, Prod.snd_add]
  constructor <;> intro h <;> omega

theorem placedSites_cons_zero (c : GInt) (ts : List (ZTile × GInt)) :
    placedSites ((ZTile.zero, c) :: ts) = (tileShape ZTile.zero).map (· + c) ++ placedSites ts := by
  simp [placedSites]

theorem placedSites_cons_one (c : GInt) (ts : List (ZTile × GInt)) :
    placedSites ((ZTile.one, c) :: ts) = (tileShape ZTile.one).map (· + c) ++ placedSites ts := by
  simp [placedSites]

theorem placedSites_nil : placedSites ([] : List (ZTile × GInt)) = [] := rfl

theorem tileSeqAux_some_p (w : BinaryWord) : tileSeqAux (some Letter.p) w = tileSeqAux none w := by
  induction w with
  | nil => rfl
  | cons x w _ => cases x <;> simp [tileSeqAux]

theorem tileSeq_p_cons (b : Letter) (v : BinaryWord) :
    tileSeq (Letter.p :: b :: v) = ZTile.zero :: tileSeq (b :: v) := by
  show ZTile.zero :: tileSeqAux (some Letter.p) (b :: v) = ZTile.zero :: tileSeqAux none (b :: v)
  rw [tileSeqAux_some_p]

theorem hOffset_p : hOffset Letter.p = (2, 0) := rfl

theorem hStringAt_cons_p (b : Letter) (v : BinaryWord) (c : GInt) :
    hStringAt (Letter.p :: b :: v) c = (ZTile.zero, c) :: hStringAt (b :: v) (c + hOffset b) := by
  unfold hStringAt
  rw [tileSeq_p_cons]
  simp [List.scanl_cons]

theorem hStringAt_cons_q_p (v : BinaryWord) (c : GInt) :
    hStringAt (Letter.q :: Letter.p :: v) c =
      (ZTile.one, c) :: hStringAt (Letter.p :: v) (c + hOffset Letter.p) := by
  unfold hStringAt
  simp [tileSeq, tileSeqAux, List.scanl_cons]

theorem vStringAt_cons (a b : Letter) (v : BinaryWord) (c : GInt) :
    vStringAt (a :: b :: v) c = (letterZTile a, c) :: vStringAt (b :: v) (c + vOffset b) := by
  simp [vStringAt, List.scanl_cons]

theorem hRevStringAt_cons (a b : Letter) (v : BinaryWord) (c : GInt) (h : a = Letter.p ∨ b = Letter.p) :
    hRevStringAt (a :: b :: v) c = (letterZTile a, c) :: hRevStringAt (b :: v) (c + hRevOffset a b) := by
  have ht : tileSeq (a :: b :: v) = letterZTile a :: tileSeq (b :: v) := by
    rcases h with rfl | rfl
    · unfold tileSeq
      rw [tileSeqAux_none_eq (b :: v)]
      rfl
    · cases a <;> rfl
  unfold hRevStringAt
  rw [ht]
  simp [List.scanl_cons]

theorem vRevStringAt_cons (a b : Letter) (v : BinaryWord) (c : GInt) :
    vRevStringAt (a :: b :: v) c = (letterZTile a, c) :: vRevStringAt (b :: v) (c + vRevOffset a b) := by
  simp [vRevStringAt, List.scanl_cons]

theorem hStringAt_p_single (c : GInt) : hStringAt [Letter.p] c = [(ZTile.zero, c)] := by
  simp [hStringAt, tileSeq, tileSeqAux]

theorem mem_hRun (n : ℕ) (c x : GInt) :
    x ∈ placedSites (hStringAt (List.replicate (n + 1) Letter.p) c) ↔
      ∃ j : ℕ, j ≤ n ∧ zeroAt (c.1 + (j : ℤ) * 2, c.2) x := by
  induction n generalizing c with
  | zero =>
    rw [show List.replicate (0 + 1) Letter.p = [Letter.p] from rfl, hStringAt_p_single,
      placedSites_cons_zero, placedSites_nil, List.append_nil, mem_shape_zero]
    constructor
    · intro h
      exact ⟨0, le_refl 0, by unfold zeroAt at h ⊢; dsimp only at h ⊢; simp only [Nat.cast_zero, zero_mul, add_zero]; exact h⟩
    · rintro ⟨j, hj, h⟩
      have : j = 0 := by omega
      subst this
      unfold zeroAt at h ⊢
      dsimp only at h ⊢
      simp only [Nat.cast_zero, zero_mul, add_zero] at h
      exact h
  | succ n ih =>
    have e : hStringAt (List.replicate (n + 1 + 1) Letter.p) c =
        (ZTile.zero, c) :: hStringAt (List.replicate (n + 1) Letter.p) (c + hOffset Letter.p) :=
      hStringAt_cons_p Letter.p (List.replicate n Letter.p) c
    rw [e, placedSites_cons_zero, List.mem_append, mem_shape_zero, ih, hOffset_p]
    constructor
    · rintro (h | ⟨j, hj, h⟩)
      · refine ⟨0, by omega, ?_⟩
        unfold zeroAt at h ⊢
        dsimp only at h ⊢
        simp only [Nat.cast_zero, zero_mul, add_zero]
        exact h
      · refine ⟨j + 1, by omega, ?_⟩
        unfold zeroAt at h ⊢
        dsimp only at h ⊢
        simp only [Prod.fst_add, Prod.snd_add] at h ⊢
        push_cast
        omega
    · rintro ⟨j, hj, h⟩
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · left
        subst h0
        unfold zeroAt at h ⊢
        dsimp only at h ⊢
        simp only [Nat.cast_zero, zero_mul, add_zero] at h
        exact h
      · right
        refine ⟨j - 1, by omega, ?_⟩
        unfold zeroAt at h ⊢
        dsimp only at h ⊢
        simp only [Prod.fst_add, Prod.snd_add]
        have hc : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
        rw [hc]
        omega

/-! ### The other three strings -/

theorem letterZTile_p : letterZTile Letter.p = ZTile.zero := rfl

theorem hRevOffset_pp : hRevOffset Letter.p Letter.p = (2, 0) := rfl
theorem hRevOffset_pq : hRevOffset Letter.p Letter.q = (2, 1) := rfl
theorem vOffset_p : vOffset Letter.p = (-1, 1) := rfl
theorem vOffset_q : vOffset Letter.q = (0, 2) := rfl
theorem vRevOffset_pp : vRevOffset Letter.p Letter.p = (-1, 1) := rfl
theorem vRevOffset_qp : vRevOffset Letter.q Letter.p = (0, 1) := rfl

theorem hRevStringAt_single_q (c : GInt) : hRevStringAt [Letter.q] c = [(ZTile.one, c)] := by
  simp [hRevStringAt, tileSeq, tileSeqAux]

theorem vStringAt_single_q (c : GInt) : vStringAt [Letter.q] c = [(ZTile.one, c)] := by
  simp [vStringAt, letterZTile]

theorem vRevStringAt_single_p (c : GInt) : vRevStringAt [Letter.p] c = [(ZTile.zero, c)] := by
  simp [vRevStringAt, letterZTile]

theorem mem_hRevRun (n : ℕ) (c x : GInt) :
    x ∈ placedSites (hRevStringAt (List.replicate (n + 1) Letter.p ++ [Letter.q]) c) ↔
      (∃ j : ℕ, j ≤ n ∧ zeroAt (c.1 + (j : ℤ) * 2, c.2) x) ∨ oneAt (c.1 + (n : ℤ) * 2 + 2, c.2 + 1) x := by
  induction n generalizing c with
  | zero =>
    rw [show List.replicate (0 + 1) Letter.p ++ [Letter.q] = [Letter.p, Letter.q] from rfl,
      hRevStringAt_cons Letter.p Letter.q [] c (Or.inl rfl), letterZTile_p, hRevStringAt_single_q, hRevOffset_pq, placedSites_cons_zero, placedSites_cons_one,
      placedSites_nil, List.append_nil, List.mem_append, mem_shape_zero, mem_shape_one]
    constructor
    · rintro (h | h)
      · left
        exact ⟨0, le_refl 0, by unfold zeroAt at h ⊢; dsimp only at h ⊢; simp only [Nat.cast_zero, zero_mul, add_zero]; exact h⟩
      · right
        unfold oneAt at h ⊢
        dsimp only at h ⊢
        simp only [Nat.cast_zero, zero_mul, add_zero]
        exact h
    · rintro (⟨j, hj, h⟩ | h)
      · have : j = 0 := by omega
        subst this
        left
        unfold zeroAt at h ⊢
        dsimp only at h ⊢
        simp only [Nat.cast_zero, zero_mul, add_zero] at h
        exact h
      · right
        unfold oneAt at h ⊢
        dsimp only at h ⊢
        simp only [Nat.cast_zero, zero_mul, add_zero] at h
        simp only [Prod.fst_add, Prod.snd_add] at h ⊢
        exact h
  | succ n ih =>
    have e : hRevStringAt (List.replicate (n + 1 + 1) Letter.p ++ [Letter.q]) c =
        (ZTile.zero, c) :: hRevStringAt (List.replicate (n + 1) Letter.p ++ [Letter.q]) (c + hRevOffset Letter.p Letter.p) :=
      hRevStringAt_cons Letter.p Letter.p (List.replicate n Letter.p ++ [Letter.q]) c (Or.inl rfl)
    rw [e, placedSites_cons_zero, List.mem_append, mem_shape_zero, ih, hRevOffset_pp]
    constructor
    · rintro (h | (⟨j, hj, h⟩ | h))
      · left
        exact ⟨0, by omega, by unfold zeroAt at h ⊢; dsimp only at h ⊢; simp only [Nat.cast_zero, zero_mul, add_zero]; exact h⟩
      · refine Or.inl ⟨j + 1, by omega, ?_⟩
        unfold zeroAt at h ⊢
        dsimp only at h ⊢
        simp only [Prod.fst_add, Prod.snd_add] at h
        push_cast
        omega
      · right
        unfold oneAt at h ⊢
        dsimp only at h ⊢
        simp only [Prod.fst_add, Prod.snd_add] at h
        push_cast
        omega
    · rintro (⟨j, hj, h⟩ | h)
      · rcases Nat.eq_zero_or_pos j with h0 | hpos
        · left
          subst h0
          unfold zeroAt at h ⊢
          dsimp only at h ⊢
          simp only [Nat.cast_zero, zero_mul, add_zero] at h
          exact h
        · right
          left
          refine ⟨j - 1, by omega, ?_⟩
          unfold zeroAt at h ⊢
          dsimp only at h ⊢
          simp only [Prod.fst_add, Prod.snd_add]
          have hc : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
          rw [hc]
          omega
      · right
        right
        unfold oneAt at h ⊢
        dsimp only at h ⊢
        simp only [Prod.fst_add, Prod.snd_add]
        push_cast at h
        omega

theorem mem_vRun (n : ℕ) (c x : GInt) :
    x ∈ placedSites (vStringAt (List.replicate (n + 1) Letter.p ++ [Letter.q]) c) ↔
      (∃ j : ℕ, j ≤ n ∧ zeroAt (c.1 - (j : ℤ), c.2 + (j : ℤ)) x) ∨ oneAt (c.1 - (n : ℤ), c.2 + (n : ℤ) + 2) x := by
  induction n generalizing c with
  | zero =>
    rw [show List.replicate (0 + 1) Letter.p ++ [Letter.q] = [Letter.p, Letter.q] from rfl,
      vStringAt_cons, letterZTile_p, vStringAt_single_q, vOffset_q, placedSites_cons_zero, placedSites_cons_one,
      placedSites_nil, List.append_nil, List.mem_append, mem_shape_zero, mem_shape_one]
    constructor
    · rintro (h | h)
      · left
        exact ⟨0, le_refl 0, by unfold zeroAt at h ⊢; dsimp only at h ⊢; simp only [Nat.cast_zero, add_zero, sub_zero]; exact h⟩
      · right
        unfold oneAt at h ⊢
        dsimp only at h ⊢
        simp only [Nat.cast_zero, add_zero, sub_zero] at h ⊢
        simp only [Prod.fst_add, Prod.snd_add] at h ⊢
        omega
    · rintro (⟨j, hj, h⟩ | h)
      · have : j = 0 := by omega
        subst this
        left
        unfold zeroAt at h ⊢
        dsimp only at h ⊢
        simp only [Nat.cast_zero, add_zero, sub_zero] at h
        exact h
      · right
        unfold oneAt at h ⊢
        dsimp only at h ⊢
        simp only [Nat.cast_zero, add_zero, sub_zero] at h
        simp only [Prod.fst_add, Prod.snd_add] at h ⊢
        omega
  | succ n ih =>
    have e : vStringAt (List.replicate (n + 1 + 1) Letter.p ++ [Letter.q]) c =
        (ZTile.zero, c) :: vStringAt (List.replicate (n + 1) Letter.p ++ [Letter.q]) (c + vOffset Letter.p) :=
      vStringAt_cons Letter.p Letter.p (List.replicate n Letter.p ++ [Letter.q]) c
    rw [e, placedSites_cons_zero, List.mem_append, mem_shape_zero, ih, vOffset_p]
    constructor
    · rintro (h | (⟨j, hj, h⟩ | h))
      · left
        exact ⟨0, by omega, by unfold zeroAt at h ⊢; dsimp only at h ⊢; simp only [Nat.cast_zero, add_zero, sub_zero]; exact h⟩
      · refine Or.inl ⟨j + 1, by omega, ?_⟩
        unfold zeroAt at h ⊢
        dsimp only at h ⊢
        simp only [Prod.fst_add, Prod.snd_add] at h
        push_cast
        omega
      · right
        unfold oneAt at h ⊢
        dsimp only at h ⊢
        simp only [Prod.fst_add, Prod.snd_add] at h
        push_cast
        omega
    · rintro (⟨j, hj, h⟩ | h)
      · rcases Nat.eq_zero_or_pos j with h0 | hpos
        · left
          subst h0
          unfold zeroAt at h ⊢
          dsimp only at h ⊢
          simp only [Nat.cast_zero, add_zero, sub_zero] at h
          exact h
        · right
          left
          refine ⟨j - 1, by omega, ?_⟩
          unfold zeroAt at h ⊢
          dsimp only at h ⊢
          simp only [Prod.fst_add, Prod.snd_add]
          have hc : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
          rw [hc]
          omega
      · right
        right
        unfold oneAt at h ⊢
        dsimp only at h ⊢
        simp only [Prod.fst_add, Prod.snd_add]
        push_cast at h
        omega

/-! ### The stair words and the membership of the four strings -/

/-- The horizontal word of the stair tile `paperStairTile (2k+3)`: `q p^{k+1}` (table, line 1912). -/
def stairH (k : ℕ) : BinaryWord := Letter.q :: List.replicate (k + 1) Letter.p

/-- The vertical word of the stair tile: `p^{2k+2} q`. -/
def stairV (k : ℕ) : BinaryWord := List.replicate (2 * k + 1 + 1) Letter.p ++ [Letter.q]

theorem stairH_reverse (k : ℕ) : (stairH k).reverse = List.replicate (k + 1) Letter.p ++ [Letter.q] := by
  simp [stairH, List.reverse_replicate]

theorem stairV_reverse (k : ℕ) : (stairV k).reverse = Letter.q :: List.replicate (2 * k + 1 + 1) Letter.p := by
  simp [stairV, List.reverse_replicate]

theorem letterZTile_q : letterZTile Letter.q = ZTile.one := rfl

theorem vRevStringAt_zeros (n : ℕ) (c x : GInt) :
    x ∈ placedSites (vRevStringAt (List.replicate (n + 1) Letter.p) c) ↔
      ∃ j : ℕ, j ≤ n ∧ zeroAt (c.1 - (j : ℤ), c.2 + (j : ℤ)) x := by
  induction n generalizing c with
  | zero =>
    rw [show List.replicate (0 + 1) Letter.p = [Letter.p] from rfl, vRevStringAt_single_p,
      placedSites_cons_zero, placedSites_nil, List.append_nil, mem_shape_zero]
    constructor
    · intro h
      exact ⟨0, le_refl 0, by unfold zeroAt at h ⊢; dsimp only at h ⊢; simp only [Nat.cast_zero, add_zero, sub_zero]; exact h⟩
    · rintro ⟨j, hj, h⟩
      have : j = 0 := by omega
      subst this
      unfold zeroAt at h ⊢
      dsimp only at h ⊢
      simp only [Nat.cast_zero, add_zero, sub_zero] at h
      exact h
  | succ n ih =>
    have e : vRevStringAt (List.replicate (n + 1 + 1) Letter.p) c =
        (ZTile.zero, c) :: vRevStringAt (List.replicate (n + 1) Letter.p) (c + vRevOffset Letter.p Letter.p) :=
      vRevStringAt_cons Letter.p Letter.p (List.replicate n Letter.p) c
    rw [e, placedSites_cons_zero, List.mem_append, mem_shape_zero, ih, vRevOffset_pp]
    constructor
    · rintro (h | ⟨j, hj, h⟩)
      · exact ⟨0, by omega, by unfold zeroAt at h ⊢; dsimp only at h ⊢; simp only [Nat.cast_zero, add_zero, sub_zero]; exact h⟩
      · refine ⟨j + 1, by omega, ?_⟩
        unfold zeroAt at h ⊢
        dsimp only at h ⊢
        simp only [Prod.fst_add, Prod.snd_add] at h
        push_cast
        omega
    · rintro ⟨j, hj, h⟩
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · left
        subst h0
        unfold zeroAt at h ⊢
        dsimp only at h ⊢
        simp only [Nat.cast_zero, add_zero, sub_zero] at h
        exact h
      · right
        refine ⟨j - 1, by omega, ?_⟩
        unfold zeroAt at h ⊢
        dsimp only at h ⊢
        simp only [Prod.fst_add, Prod.snd_add]
        have hc : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
        rw [hc]
        omega

theorem mem_hLower (k : ℕ) (c x : GInt) :
    x ∈ placedSites (hStringAt (stairH k) c) ↔
      oneAt c x ∨ ∃ j : ℕ, j ≤ k ∧ zeroAt (c.1 + 2 + (j : ℤ) * 2, c.2) x := by
  have e : hStringAt (stairH k) c = (ZTile.one, c) :: hStringAt (List.replicate (k + 1) Letter.p) (c + hOffset Letter.p) :=
    hStringAt_cons_q_p (List.replicate k Letter.p) c
  rw [e, placedSites_cons_one, List.mem_append, mem_shape_one, mem_hRun, hOffset_p]
  simp only [Prod.fst_add, Prod.snd_add, add_zero]

theorem mem_vLeft (k : ℕ) (c x : GInt) :
    x ∈ placedSites (vRevStringAt (stairV k).reverse c) ↔
      oneAt c x ∨ ∃ j : ℕ, j ≤ 2 * k + 1 ∧ zeroAt (c.1 - (j : ℤ), c.2 + 1 + (j : ℤ)) x := by
  rw [stairV_reverse]
  have e : vRevStringAt (Letter.q :: List.replicate (2 * k + 1 + 1) Letter.p) c =
      (ZTile.one, c) :: vRevStringAt (List.replicate (2 * k + 1 + 1) Letter.p) (c + vRevOffset Letter.q Letter.p) :=
    vRevStringAt_cons Letter.q Letter.p (List.replicate (2 * k + 1) Letter.p) c
  rw [e, placedSites_cons_one, List.mem_append, mem_shape_one, vRevStringAt_zeros, vRevOffset_qp]
  simp only [Prod.fst_add, Prod.snd_add, add_zero]

theorem placedSites_append (A B : List (ZTile × GInt)) :
    placedSites (A ++ B) = placedSites A ++ placedSites B := by
  simp [placedSites, List.flatMap_append]

/-- The membership of the four placed strings of the stair tile, with the starts `c` (lower and left), `s` (top),
`r` (right), as the four rectangle families. -/
theorem mem_stair_strings (k : ℕ) (c s r x : GInt) :
    x ∈ placedSites (hStringAt (stairH k) c ++ hRevStringAt (stairH k).reverse s ++
        vRevStringAt (stairV k).reverse c ++ vStringAt (stairV k) r) ↔
      ((((oneAt c x ∨ ∃ j : ℕ, j ≤ k ∧ zeroAt (c.1 + 2 + (j : ℤ) * 2, c.2) x) ∨
          ((∃ j : ℕ, j ≤ k ∧ zeroAt (s.1 + (j : ℤ) * 2, s.2) x) ∨ oneAt (s.1 + (k : ℤ) * 2 + 2, s.2 + 1) x)) ∨
        (oneAt c x ∨ ∃ j : ℕ, j ≤ 2 * k + 1 ∧ zeroAt (c.1 - (j : ℤ), c.2 + 1 + (j : ℤ)) x)) ∨
      ((∃ j : ℕ, j ≤ 2 * k + 1 ∧ zeroAt (r.1 - (j : ℤ), r.2 + (j : ℤ)) x) ∨
        oneAt (r.1 - ((2 * k + 1 : ℕ) : ℤ), r.2 + ((2 * k + 1 : ℕ) : ℤ) + 2) x)) := by
  simp only [placedSites_append, List.mem_append]
  rw [stairH_reverse, mem_hLower, mem_hRevRun, mem_vLeft,
    show vStringAt (stairV k) r = vStringAt (List.replicate (2 * k + 1 + 1) Letter.p ++ [Letter.q]) r from rfl,
    mem_vRun (2 * k + 1)]

/-! ### The four strings of the stair tile, with the starts from the walk -/

/-- The starts of the four strings of `alongStrings` for the stair words, with `c = (0,0)`: the right string at
`c + Σw1 - (1,0) = (2k+2, 0)` and the top string at `c + Σw2 - (0,2) = (-(2k+1), 2k+2)`. -/
theorem mem_alongStrings_stair (k : ℕ) (x : GInt) :
    x ∈ placedSites (alongStrings (stairH k) (stairV k) (0, 0)) ↔
      x ∈ placedSites (hStringAt (stairH k) (0, 0) ++
        hRevStringAt (stairH k).reverse (-(2 * (k : ℤ) + 1), 2 * (k : ℤ) + 2) ++
        vRevStringAt (stairV k).reverse (0, 0) ++ vStringAt (stairV k) (2 * (k : ℤ) + 2, 0)) := by
  have hH : F2Word.sum (gPseudo (stairH k) (stairV k)).1 = (2 * (k : ℤ) + 3, 0) := sum_gH_stair k
  have hV : F2Word.sum (gPseudo (stairH k) (stairV k)).2 = (-(2 * (k : ℤ) + 1), 2 * (k : ℤ) + 4) :=
    sum_gV_stair k
  have hs : (((0, 0) : GInt) + (-(2 * (k : ℤ) + 1), 2 * (k : ℤ) + 4) + (0, -2)) =
      (-(2 * (k : ℤ) + 1), 2 * (k : ℤ) + 2) :=
    Prod.ext (by simp; try ring) (by simp; try ring)
  have hr : (((0, 0) : GInt) + (2 * (k : ℤ) + 3, 0) + (-1, 0)) = (2 * (k : ℤ) + 2, 0) :=
    Prod.ext (by simp; try ring) (by simp; try ring)
  simp only [alongStrings]
  rw [walkAt_top, walkAt_right, hV, hH, hs, hr]

/-! ### Containment and covering for the stair family -/

theorem mem_stairT_disj (d : ℤ) (x : GInt) :
    x ∈ paperStairTile d ↔
      (2 - d ≤ x.1 ∧ x.1 ≤ d ∧ 0 ≤ x.2 ∧ x.2 ≤ d + 1 ∧ 1 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ d + 2) ∨
        (x.1 = 0 ∧ x.2 = 0) ∨ (x.1 = 2 ∧ x.2 = d + 1) := by
  unfold paperStairTile
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]

theorem exists_nat_of_int (t : ℤ) (h0 : 0 ≤ t) : ∃ j : ℕ, (j : ℤ) = t :=
  ⟨t.toNat, Int.toNat_of_nonneg h0⟩

/-- Containment (clause 1) for the stair family: every placed rectangle lies in `paperStairTile (2k+3)`. -/
theorem stair_contain (k : ℕ) (x : GInt)
    (hx : x ∈ placedSites (alongStrings (stairH k) (stairV k) (0, 0))) :
    x ∈ paperStairTile (2 * (k : ℤ) + 3) := by
  rw [mem_alongStrings_stair, mem_stair_strings] at hx
  rw [mem_stairT_disj]
  rcases hx with ((((h | ⟨j, hj, h⟩) | (⟨j, hj, h⟩ | h)) | (h | ⟨j, hj, h⟩)) | (⟨j, hj, h⟩ | h))
  all_goals (simp only [oneAt, zeroAt] at *; omega)

/-- The lower-left vertex `c(T) = (0,0)` of the stair tile (line 1099). -/
theorem stair_lowerLeft (k : ℕ) :
    (0 : GInt) ∈ paperStairTile (2 * (k : ℤ) + 3) ∧
      ∀ y ∈ paperStairTile (2 * (k : ℤ) + 3),
        (0 : GInt).2 < y.2 ∨ ((0 : GInt).2 = y.2 ∧ (0 : GInt).1 ≤ y.1) := by
  refine ⟨?_, ?_⟩
  · rw [mem_stairT_disj]
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · intro y hy
    rw [mem_stairT_disj] at hy
    simp only [Prod.fst_zero, Prod.snd_zero]
    rcases hy with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- Covering (clause 2) for the stair family: every site of `∂⁻T` is covered by the placed rectangles. -/
theorem stair_cover (k : ℕ) (x : GInt)
    (hT : x ∈ paperStairTile (2 * (k : ℤ) + 3))
    (hB : (x.1 + 1, x.2) ∉ paperStairTile (2 * (k : ℤ) + 3) ∨ (x.1 - 1, x.2) ∉ paperStairTile (2 * (k : ℤ) + 3) ∨
      (x.1, x.2 + 1) ∉ paperStairTile (2 * (k : ℤ) + 3) ∨ (x.1, x.2 - 1) ∉ paperStairTile (2 * (k : ℤ) + 3)) :
    x ∈ placedSites (alongStrings (stairH k) (stairV k) (0, 0)) := by
  rw [mem_alongStrings_stair, mem_stair_strings]
  rw [mem_stairT_disj] at hT
  simp only [mem_stairT_disj] at hB
  have hlines : x.2 = 0 ∨ x.1 = -(2 * (k : ℤ) + 1) ∨ x.2 = 2 * (k : ℤ) + 4 ∨ x.1 = 2 * (k : ℤ) + 3 ∨
      x.1 + x.2 = 1 ∨ x.1 + x.2 = 2 * (k : ℤ) + 5 := by
    omega
  rcases hlines with h1 | h2 | h3 | h4 | h5 | h6
  · rcases le_or_gt x.1 1 with ha | ha
    · exact Or.inl (Or.inl (Or.inl (Or.inl (by simp only [oneAt]; omega))))
    · obtain ⟨j, hj⟩ := exists_nat_of_int ((x.1 - 2) / 2) (by omega)
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨j, by omega, by simp only [zeroAt]; omega⟩)))
  · obtain ⟨j, hj⟩ := exists_nat_of_int ((x.1 + 2 * (k : ℤ) + 1) / 2) (by omega)
    exact Or.inl (Or.inl (Or.inr (Or.inl ⟨j, by omega, by simp only [zeroAt]; omega⟩)))
  · rcases le_or_gt x.1 0 with ha | ha
    · obtain ⟨j, hj⟩ := exists_nat_of_int ((x.1 + 2 * (k : ℤ) + 1) / 2) (by omega)
      exact Or.inl (Or.inl (Or.inr (Or.inl ⟨j, by omega, by simp only [zeroAt]; omega⟩)))
    · exact Or.inl (Or.inl (Or.inr (Or.inr (by simp only [oneAt]; omega))))
  · obtain ⟨j, hj⟩ := exists_nat_of_int ((x.1 - 2) / 2) (by omega)
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨j, by omega, by simp only [zeroAt]; omega⟩)))
  · rcases (show x.2 = 0 ∨ 1 ≤ x.2 by omega) with hb | hb
    · exact Or.inl (Or.inl (Or.inl (Or.inl (by simp only [oneAt]; omega))))
    · obtain ⟨j, hj⟩ := exists_nat_of_int (x.2 - 1) (by omega)
      exact Or.inl (Or.inr (Or.inr ⟨j, by omega, by simp only [zeroAt]; omega⟩))
  · rcases (show x.2 = 2 * (k : ℤ) + 4 ∨ x.2 ≤ 2 * (k : ℤ) + 3 by omega) with hb | hb
    · exact Or.inr (Or.inr (by simp only [oneAt]; omega))
    · obtain ⟨j, hj⟩ := exists_nat_of_int (x.2 - 2) (by omega)
      exact Or.inr (Or.inl ⟨j, by omega, by simp only [zeroAt]; omega⟩)

/-! ### The predicate on sets and the stair family -/

/-- `c` is the lower-left vertex `c(T)` of a set `T` (line 1099): smallest imaginary part, then smallest real part. -/
def IsLowerLeftVertex (T : Set GInt) (c : GInt) : Prop :=
  c ∈ T ∧ ∀ y ∈ T, c.2 < y.2 ∨ (c.2 = y.2 ∧ c.1 ≤ y.1)

/-- The walk-placement pseudo-square clauses for a set `T` at the corner `c`: the placed strings lie in `T`
and cover `∂⁻T` (`innerBoundary`, the paper's line 2312). -/
def IsPseudoSquareAlongSet (T : Set GInt) (c : GInt) (wh wv : BinaryWord) : Prop :=
  (∀ x ∈ placedSites (alongStrings wh wv c), x ∈ T) ∧
    (∀ x ∈ innerBoundary T, x ∈ placedSites (alongStrings wh wv c))

/-- The walk-placement pseudo-square predicate for a set `T`: at its lower-left vertex, the clauses hold. -/
def IsPseudoSquareAlongT (T : Set GInt) (wh wv : BinaryWord) : Prop :=
  ∃ c, IsLowerLeftVertex T c ∧ IsPseudoSquareAlongSet T c wh wv

/-- The stair family of `prop:base_cases` (d) for every `k`: `paperStairTile (2k+3)` is a
`(q p^{k+1}, p^{2k+2} q)`-pseudo-square under the walk placement. -/
theorem stair_isPseudoSquareAlongT (k : ℕ) :
    IsPseudoSquareAlongT (paperStairTile (2 * (k : ℤ) + 3)) (stairH k) (stairV k) :=
  ⟨(0, 0), ⟨(stair_lowerLeft k).1, (stair_lowerLeft k).2⟩,
    fun x hx => stair_contain k x hx, fun x hx => stair_cover k x hx.1 hx.2⟩

/-! ### The ladder family: words and G-sums -/

/-- The horizontal word of the doubled staircase `paperLadderTile (2k+2)`: `q p^k q p^{k+1}` (table, line 1912). -/
def ladderH (k : ℕ) : BinaryWord :=
  Letter.q :: (List.replicate k Letter.p ++ Letter.q :: List.replicate (k + 1) Letter.p)

/-- The vertical word of the doubled staircase: `p^{2k+1} q`. -/
def ladderV (k : ℕ) : BinaryWord := List.replicate (2 * k + 1) Letter.p ++ [Letter.q]

/-- The sum of `pairSum` over the consecutive pairs of a tile list. -/
def pairChain : List ZTile → GInt
  | [] => 0
  | [_] => 0
  | a :: b :: L => pairSum a b + pairChain (b :: L)

theorem pairChain_cons_cons (a b : ZTile) (L : List ZTile) :
    pairChain (a :: b :: L) = pairSum a b + pairChain (b :: L) := rfl

theorem pairSum_zo : pairSum ZTile.zero ZTile.one = (1, 1) := by decide

theorem zip_tail_pairChain (ts : List ZTile) :
    ((ts.zip ts.tail).map fun ab => pairSum ab.1 ab.2).sum = pairChain ts := by
  induction ts with
  | nil => rfl
  | cons a L ih =>
    cases L with
    | nil => rfl
    | cons b L' =>
      simp only [List.tail_cons] at ih ⊢
      rw [List.zip_cons_cons, List.map_cons, List.sum_cons, pairChain_cons_cons, ih]

theorem sum_gH_chain (w : BinaryWord) : F2Word.sum (gH w) = pairChain (tileSeq w) + (1, 0) := by
  rw [sum_gH_eq, zip_tail_pairChain]

/-- A run of `n+1` zero tiles followed by `T`, with the chain sum. -/
theorem pc_zrun (n : ℕ) (T : List ZTile) :
    pairChain (List.replicate (n + 1) ZTile.zero ++ T) =
      ((n : ℤ) * 2, 0) + pairChain (ZTile.zero :: T) := by
  induction n with
  | zero =>
    show pairChain (ZTile.zero :: T) = (((0 : ℕ) : ℤ) * 2, 0) + pairChain (ZTile.zero :: T)
    simp
  | succ n ih =>
    have e : List.replicate (n + 1 + 1) ZTile.zero ++ T =
        ZTile.zero :: ZTile.zero :: (List.replicate n ZTile.zero ++ T) := by
      simp [List.replicate_succ]
    have e2 : ZTile.zero :: (List.replicate n ZTile.zero ++ T) = List.replicate (n + 1) ZTile.zero ++ T := by
      simp [List.replicate_succ]
    rw [e, pairChain_cons_cons, pairSum_zz, e2, ih]
    refine Prod.ext (by simp; try ring) (by simp; try ring)

theorem pc_zrun_nil (n : ℕ) : pairChain (List.replicate (n + 1) ZTile.zero) = ((n : ℤ) * 2, 0) := by
  have h := pc_zrun n []
  simp only [List.append_nil] at h
  rw [h]
  simp [pairChain]

theorem pc_oneD (n : ℕ) :
    pairChain (List.replicate (n + 1) ZTile.oneD ++ [ZTile.zero]) = ((n : ℤ) + 1, (n : ℤ) + 1) := by
  rw [← zip_tail_pairChain]
  rw [show (List.replicate (n + 1) ZTile.oneD ++ [ZTile.zero]).tail =
      List.replicate n ZTile.oneD ++ [ZTile.zero] by simp [List.replicate_succ]]
  exact oneDZero_sum n

theorem pc_one_head (n : ℕ) :
    pairChain (ZTile.one :: (List.replicate (n + 1) ZTile.oneD ++ [ZTile.zero])) =
      pairSum ZTile.one ZTile.oneD + pairChain (List.replicate (n + 1) ZTile.oneD ++ [ZTile.zero]) := by
  rw [show List.replicate (n + 1) ZTile.oneD ++ [ZTile.zero] =
      ZTile.oneD :: (List.replicate n ZTile.oneD ++ [ZTile.zero]) by simp [List.replicate_succ]]
  rw [pairChain_cons_cons]

theorem tileSeqAux_rep_p_append (prev : Option Letter) (n : ℕ) (w : BinaryWord) :
    tileSeqAux prev (List.replicate (n + 1) Letter.p ++ w) =
      List.replicate (n + 1) ZTile.zero ++ tileSeqAux none w := by
  induction n generalizing prev with
  | zero => simp [List.replicate_succ, tileSeqAux, tileSeqAux_some_p]
  | succ n ih =>
    have e : List.replicate (n + 1 + 1) Letter.p ++ w = Letter.p :: (List.replicate (n + 1) Letter.p ++ w) := by
      simp [List.replicate_succ]
    rw [e]
    simp only [tileSeqAux]
    rw [tileSeqAux_some_p, ih none]
    simp [List.replicate_succ]

theorem tileSeq_ladderH (m : ℕ) :
    tileSeq (ladderH (m + 1)) =
      ZTile.one :: (List.replicate (m + 1) ZTile.zero ++ ZTile.one :: List.replicate (m + 2) ZTile.zero) := by
  have e : ladderH (m + 1) = Letter.q :: (List.replicate (m + 1) Letter.p ++ Letter.q :: List.replicate (m + 2) Letter.p) :=
    rfl
  rw [e]
  simp only [tileSeq, tileSeqAux]
  rw [tileSeqAux_rep_p_append]
  simp [tileSeqAux, tileSeqAux_p_rep]

theorem sum_gH_ladder (m : ℕ) : F2Word.sum (gH (ladderH (m + 1))) = (4 * (m : ℤ) + 8, 1) := by
  rw [sum_gH_chain, tileSeq_ladderH]
  have e1 : List.replicate (m + 1) ZTile.zero ++ (ZTile.one :: List.replicate (m + 2) ZTile.zero) =
      ZTile.zero :: (List.replicate m ZTile.zero ++ (ZTile.one :: List.replicate (m + 2) ZTile.zero)) := by
    simp [List.replicate_succ]
  have e3 : ZTile.one :: List.replicate (m + 2) ZTile.zero =
      ZTile.one :: ZTile.zero :: List.replicate (m + 1) ZTile.zero := by
    simp [List.replicate_succ]
  have e4 : ZTile.zero :: List.replicate (m + 1) ZTile.zero = List.replicate (m + 2) ZTile.zero := by
    simp [List.replicate_succ]
  have h5 : pairChain (ZTile.one :: List.replicate (m + 2) ZTile.zero) = (2, 0) + ((((m : ℤ) + 1) * 2), 0) := by
    rw [e3, pairChain_cons_cons, pairSum_oz, e4]
    have h := pc_zrun_nil (m + 1)
    push_cast at h
    rw [h]
  rw [e1, pairChain_cons_cons, ← e1, pc_zrun m, pairChain_cons_cons, pairSum_zo, h5, pairSum_oz]
  refine Prod.ext (by simp; try ring) (by simp; try ring)

theorem sum_gV_ladder (m : ℕ) :
    F2Word.sum (gV (ladderV (m + 1))) = (-(2 * (m : ℤ) + 2), 2 * (m : ℤ) + 5) := by
  have hf : flipW (ladderV (m + 1)) = List.replicate (2 * m + 1 + 1 + 1) Letter.q ++ [Letter.p] := by
    simp only [ladderV, flipW, flipLetter, List.map_append, List.map_replicate, List.map_cons, List.map_nil]
    rfl
  unfold gV
  rw [hf, f2sum_mulI, sum_gH_chain, tileSeq_flip (2 * m + 1 + 1), pc_one_head, pc_oneD (2 * m + 1),
    pairSum_od]
  refine Prod.ext (by simp; try ring) (by simp; try ring)

/-! ### The ladder family: placed rectangles -/

theorem hOffset_q : hOffset Letter.q = (1, 1) := rfl
theorem hRevOffset_qp : hRevOffset Letter.q Letter.p = (1, 0) := rfl

theorem ladderV_reverse (k : ℕ) : (ladderV k).reverse = Letter.q :: List.replicate (2 * k + 1) Letter.p := by
  simp [ladderV, List.reverse_replicate]

theorem ladderH_reverse (m : ℕ) :
    (ladderH (m + 1)).reverse =
      List.replicate (m + 1 + 1) Letter.p ++ Letter.q :: (List.replicate (m + 1) Letter.p ++ [Letter.q]) := by
  simp [ladderH, List.reverse_append, List.reverse_replicate, List.append_assoc]

theorem hStringAt_cons_pq (v : BinaryWord) (c : GInt) :
    hStringAt (Letter.p :: Letter.q :: v) c = (ZTile.zero, c) :: hStringAt (Letter.q :: v) (c + hOffset Letter.q) := by
  unfold hStringAt
  simp [tileSeq, tileSeqAux, List.scanl_cons]

/-- The lower string of a `p^{n+1}`-run followed by `q` and `rest`: the zeros at `c + (2j, 0)`, then the `q` tile
at `c + (2n, 0) + (1,1)`, where the tail is placed by its own cons decomposition. -/
theorem mem_lowRun (n : ℕ) (c : GInt) (rest : BinaryWord) (x : GInt) :
    x ∈ placedSites (hStringAt (List.replicate (n + 1) Letter.p ++ Letter.q :: rest) c) ↔
      (∃ j : ℕ, j ≤ n ∧ zeroAt (c.1 + (j : ℤ) * 2, c.2) x) ∨
        x ∈ placedSites (hStringAt (Letter.q :: rest) (c.1 + (n : ℤ) * 2 + 1, c.2 + 1)) := by
  induction n generalizing c with
  | zero =>
    have e : hStringAt (List.replicate (0 + 1) Letter.p ++ Letter.q :: rest) c =
        (ZTile.zero, c) :: hStringAt (Letter.q :: rest) (c + hOffset Letter.q) :=
      hStringAt_cons_pq rest c
    have hq : c + hOffset Letter.q = (c.1 + ((0 : ℕ) : ℤ) * 2 + 1, c.2 + 1) := by
      rw [hOffset_q]
      exact Prod.ext (by simp) (by simp)
    rw [e, placedSites_cons_zero, List.mem_append, mem_shape_zero, hq]
    constructor
    · rintro (h | h)
      · exact Or.inl ⟨0, le_refl 0, by unfold zeroAt at h ⊢; simpa using h⟩
      · exact Or.inr h
    · rintro (⟨j, hj, h⟩ | h)
      · have hj0 : j = 0 := by omega
        subst hj0
        left
        unfold zeroAt at h ⊢
        simpa using h
      · exact Or.inr h
  | succ n ih =>
    have e : hStringAt (List.replicate (n + 1 + 1) Letter.p ++ Letter.q :: rest) c =
        (ZTile.zero, c) :: hStringAt (List.replicate (n + 1) Letter.p ++ Letter.q :: rest) (c + hOffset Letter.p) :=
      hStringAt_cons_p Letter.p (List.replicate n Letter.p ++ Letter.q :: rest) c
    have hpos : ((c + hOffset Letter.p).1 + (n : ℤ) * 2 + 1, (c + hOffset Letter.p).2 + 1) =
        (c.1 + ((n + 1 : ℕ) : ℤ) * 2 + 1, c.2 + 1) := by
      rw [hOffset_p]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]
        push_cast
        ring
      · simp only [Prod.snd_add]
        ring
    rw [e, placedSites_cons_zero, List.mem_append, mem_shape_zero, ih (c + hOffset Letter.p), hpos]
    constructor
    · rintro (h | ⟨j, hj, h⟩ | h)
      · exact Or.inl ⟨0, by omega, by unfold zeroAt at h ⊢; simpa using h⟩
      · refine Or.inl ⟨j + 1, by omega, ?_⟩
        unfold zeroAt at h ⊢
        simp only [Prod.fst_add, Prod.snd_add, hOffset_p] at h ⊢
        push_cast
        omega
      · exact Or.inr h
    · rintro (⟨j, hj, h⟩ | h)
      · rcases Nat.eq_zero_or_pos j with h0 | hpos'
        · left
          subst h0
          unfold zeroAt at h ⊢
          simpa using h
        · right
          left
          refine ⟨j - 1, by omega, ?_⟩
          unfold zeroAt at h ⊢
          simp only [Prod.fst_add, Prod.snd_add, hOffset_p]
          have hc : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
          rw [hc]
          push_cast at h
          omega
      · exact Or.inr (Or.inr h)

/-- The reversed top string of a `p^{n+1}`-run followed by `q` and `rest`: zeros at `s + (2j, 0)`, then the `q` tile
at `s + (2n, 0) + (2, 1)`. -/
theorem mem_topRun (n : ℕ) (s : GInt) (rest : BinaryWord) (x : GInt) :
    x ∈ placedSites (hRevStringAt (List.replicate (n + 1) Letter.p ++ Letter.q :: rest) s) ↔
      (∃ j : ℕ, j ≤ n ∧ zeroAt (s.1 + (j : ℤ) * 2, s.2) x) ∨
        x ∈ placedSites (hRevStringAt (Letter.q :: rest) (s.1 + (n : ℤ) * 2 + 2, s.2 + 1)) := by
  induction n generalizing s with
  | zero =>
    have e : hRevStringAt (List.replicate (0 + 1) Letter.p ++ Letter.q :: rest) s =
        (ZTile.zero, s) :: hRevStringAt (Letter.q :: rest) (s + hRevOffset Letter.p Letter.q) :=
      hRevStringAt_cons Letter.p Letter.q rest s (Or.inl rfl)
    have hq : s + hRevOffset Letter.p Letter.q = (s.1 + ((0 : ℕ) : ℤ) * 2 + 2, s.2 + 1) := by
      rw [hRevOffset_pq]
      exact Prod.ext (by simp) (by simp)
    rw [e, placedSites_cons_zero, List.mem_append, mem_shape_zero, hq]
    constructor
    · rintro (h | h)
      · exact Or.inl ⟨0, le_refl 0, by unfold zeroAt at h ⊢; simpa using h⟩
      · exact Or.inr h
    · rintro (⟨j, hj, h⟩ | h)
      · have hj0 : j = 0 := by omega
        subst hj0
        left
        unfold zeroAt at h ⊢
        simpa using h
      · exact Or.inr h
  | succ n ih =>
    have e : hRevStringAt (List.replicate (n + 1 + 1) Letter.p ++ Letter.q :: rest) s =
        (ZTile.zero, s) :: hRevStringAt (List.replicate (n + 1) Letter.p ++ Letter.q :: rest) (s + hRevOffset Letter.p Letter.p) :=
      hRevStringAt_cons Letter.p Letter.p (List.replicate n Letter.p ++ Letter.q :: rest) s (Or.inl rfl)
    have hpos : ((s + hRevOffset Letter.p Letter.p).1 + (n : ℤ) * 2 + 2, (s + hRevOffset Letter.p Letter.p).2 + 1) =
        (s.1 + ((n + 1 : ℕ) : ℤ) * 2 + 2, s.2 + 1) := by
      rw [hRevOffset_pp]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]
        push_cast
        ring
      · simp only [Prod.snd_add]
        ring
    rw [e, placedSites_cons_zero, List.mem_append, mem_shape_zero, ih (s + hRevOffset Letter.p Letter.p), hpos]
    constructor
    · rintro (h | ⟨j, hj, h⟩ | h)
      · exact Or.inl ⟨0, by omega, by unfold zeroAt at h ⊢; simpa using h⟩
      · refine Or.inl ⟨j + 1, by omega, ?_⟩
        unfold zeroAt at h ⊢
        simp only [Prod.fst_add, Prod.snd_add, hRevOffset_pp] at h ⊢
        push_cast
        omega
      · exact Or.inr h
    · rintro (⟨j, hj, h⟩ | h)
      · rcases Nat.eq_zero_or_pos j with h0 | hpos'
        · left
          subst h0
          unfold zeroAt at h ⊢
          simpa using h
        · right
          left
          refine ⟨j - 1, by omega, ?_⟩
          unfold zeroAt at h ⊢
          simp only [Prod.fst_add, Prod.snd_add, hRevOffset_pp]
          have hc : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
          rw [hc]
          push_cast at h
          omega
      · exact Or.inr (Or.inr h)

theorem mem_hRevStringAt_qp (v : BinaryWord) (t x : GInt) :
    x ∈ placedSites (hRevStringAt (Letter.q :: Letter.p :: v) t) ↔
      oneAt t x ∨ x ∈ placedSites (hRevStringAt (Letter.p :: v) (t + (1, 0))) := by
  have e : hRevStringAt (Letter.q :: Letter.p :: v) t =
      (ZTile.one, t) :: hRevStringAt (Letter.p :: v) (t + hRevOffset Letter.q Letter.p) :=
    hRevStringAt_cons Letter.q Letter.p v t (Or.inr rfl)
  rw [e, hRevOffset_qp, placedSites_cons_one, List.mem_append, mem_shape_one]

theorem mem_vLeftGen (n : ℕ) (c x : GInt) :
    x ∈ placedSites (vRevStringAt (Letter.q :: List.replicate (n + 1) Letter.p) c) ↔
      oneAt c x ∨ ∃ j : ℕ, j ≤ n ∧ zeroAt (c.1 - (j : ℤ), c.2 + 1 + (j : ℤ)) x := by
  have e : vRevStringAt (Letter.q :: List.replicate (n + 1) Letter.p) c =
      (ZTile.one, c) :: vRevStringAt (List.replicate (n + 1) Letter.p) (c + vRevOffset Letter.q Letter.p) :=
    vRevStringAt_cons Letter.q Letter.p (List.replicate n Letter.p) c
  have hv : c + vRevOffset Letter.q Letter.p = (c.1, c.2 + 1) := by
    rw [vRevOffset_qp]
    exact Prod.ext (by simp) (by simp)
  rw [e, placedSites_cons_one, List.mem_append, mem_shape_one, hv, vRevStringAt_zeros]

/-! ### The four strings of the ladder tile -/

/-- The lower string of the ladder: one tile at `c`, then the zeros and the `q` tile of `mem_lowRun`, with the tail
placed as the stair lower string `stairH m`. -/
theorem piece_lower (m : ℕ) (c : GInt) (x : GInt) :
    x ∈ placedSites (hStringAt (ladderH (m + 1)) c) ↔
      oneAt c x ∨
        ((∃ j : ℕ, j ≤ m ∧ zeroAt ((c + hOffset Letter.p).1 + (j : ℤ) * 2, (c + hOffset Letter.p).2) x) ∨
          (oneAt ((c + hOffset Letter.p).1 + (m : ℤ) * 2 + 1, (c + hOffset Letter.p).2 + 1) x ∨
            ∃ j : ℕ, j ≤ m + 1 ∧
              zeroAt ((c + hOffset Letter.p).1 + (m : ℤ) * 2 + 1 + 2 + (j : ℤ) * 2, (c + hOffset Letter.p).2 + 1) x)) := by
  have e : hStringAt (ladderH (m + 1)) c =
      (ZTile.one, c) :: hStringAt (List.replicate (m + 1) Letter.p ++ Letter.q :: List.replicate (m + 1 + 1) Letter.p)
        (c + hOffset Letter.p) :=
    hStringAt_cons_q_p (List.replicate m Letter.p ++ Letter.q :: List.replicate (m + 1 + 1) Letter.p) c
  rw [e, placedSites_cons_one, List.mem_append, mem_shape_one, mem_lowRun m (c + hOffset Letter.p)
    (List.replicate (m + 1 + 1) Letter.p) x,
    show (Letter.q :: List.replicate (m + 1 + 1) Letter.p) = stairH (m + 1) from rfl, mem_hLower (m + 1)]

/-- The top string of the ladder, through the reversed word `p^{m+2} q p^{m+1} q`. -/
theorem piece_top (m : ℕ) (s : GInt) (x : GInt) :
    x ∈ placedSites (hRevStringAt (ladderH (m + 1)).reverse s) ↔
      (∃ j : ℕ, j ≤ m + 1 ∧ zeroAt (s.1 + (j : ℤ) * 2, s.2) x) ∨
        (oneAt (s.1 + ((m + 1 : ℕ) : ℤ) * 2 + 2, s.2 + 1) x ∨
          ((∃ j : ℕ, j ≤ m ∧ zeroAt (s.1 + ((m + 1 : ℕ) : ℤ) * 2 + 2 + 1 + (j : ℤ) * 2, s.2 + 1) x) ∨
            oneAt (s.1 + ((m + 1 : ℕ) : ℤ) * 2 + 2 + 1 + (m : ℤ) * 2 + 2, s.2 + 1 + 1) x)) := by
  rw [ladderH_reverse, mem_topRun (m + 1) s (List.replicate (m + 1) Letter.p ++ [Letter.q]) x,
    show (Letter.q :: (List.replicate (m + 1) Letter.p ++ [Letter.q])) =
      Letter.q :: Letter.p :: (List.replicate m Letter.p ++ [Letter.q]) by simp [List.replicate_succ],
    mem_hRevStringAt_qp,
    show (Letter.p :: (List.replicate m Letter.p ++ [Letter.q])) = List.replicate (m + 1) Letter.p ++ [Letter.q]
      by simp [List.replicate_succ],
    mem_hRevRun m]
  simp only [Prod.fst_add, Prod.snd_add, add_zero]

/-- The left string of the ladder: the reversed vertical string of `q p^{2m+3}`. -/
theorem piece_left (m : ℕ) (c : GInt) (x : GInt) :
    x ∈ placedSites (vRevStringAt (ladderV (m + 1)).reverse c) ↔
      oneAt c x ∨ ∃ j : ℕ, j ≤ 2 * (m + 1) ∧ zeroAt (c.1 - (j : ℤ), c.2 + 1 + (j : ℤ)) x := by
  rw [ladderV_reverse]
  exact mem_vLeftGen (2 * (m + 1)) c x

/-- The right string of the ladder: the vertical string of `p^{2m+3} q`. -/
theorem piece_right (m : ℕ) (r : GInt) (x : GInt) :
    x ∈ placedSites (vStringAt (ladderV (m + 1)) r) ↔
      (∃ j : ℕ, j ≤ 2 * (m + 1) ∧ zeroAt (r.1 - (j : ℤ), r.2 + (j : ℤ)) x) ∨
        oneAt (r.1 - ((2 * (m + 1) : ℕ) : ℤ), r.2 + ((2 * (m + 1) : ℕ) : ℤ) + 2) x :=
  mem_vRun (2 * (m + 1)) r x

theorem sum_gV_ladder_eq (m : ℕ) :
    F2Word.sum (gPseudo (ladderH (m + 1)) (ladderV (m + 1))).2 = (-(2 * (m : ℤ) + 2), 2 * (m : ℤ) + 5) :=
  sum_gV_ladder m

/-- The four strings of the ladder tile for `c = (0,0)`, with the walk starts `(-(2m+2), 2m+3)` (top) and
`(4m+7, 1)` (right). -/
theorem mem_alongStrings_ladder (m : ℕ) (x : GInt) :
    x ∈ placedSites (alongStrings (ladderH (m + 1)) (ladderV (m + 1)) (0, 0)) ↔
      x ∈ placedSites (hStringAt (ladderH (m + 1)) (0, 0) ++
        hRevStringAt (ladderH (m + 1)).reverse (-(2 * (m : ℤ) + 2), 2 * (m : ℤ) + 3) ++
        vRevStringAt (ladderV (m + 1)).reverse (0, 0) ++ vStringAt (ladderV (m + 1)) (4 * (m : ℤ) + 7, 1)) := by
  have hH : F2Word.sum (gPseudo (ladderH (m + 1)) (ladderV (m + 1))).1 = (4 * (m : ℤ) + 8, 1) :=
    sum_gH_ladder m
  have hV : F2Word.sum (gPseudo (ladderH (m + 1)) (ladderV (m + 1))).2 = (-(2 * (m : ℤ) + 2), 2 * (m : ℤ) + 5) :=
    sum_gV_ladder m
  have hs : (((0, 0) : GInt) + (-(2 * (m : ℤ) + 2), 2 * (m : ℤ) + 5) + (0, -2)) =
      (-(2 * (m : ℤ) + 2), 2 * (m : ℤ) + 3) :=
    Prod.ext (by simp; try ring) (by simp; try ring)
  have hr : (((0, 0) : GInt) + (4 * (m : ℤ) + 8, 1) + (-1, 0)) = (4 * (m : ℤ) + 7, 1) :=
    Prod.ext (by simp; try ring) (by simp; try ring)
  simp only [alongStrings]
  rw [walkAt_top, walkAt_right, hV, hH, hs, hr]

/-- The membership of the ladder tile `(A ∪ B ∪ C) \ D` (lines 59-75 of `BaseCaseRecurrence`). -/
theorem mem_ladderT_disj (d : ℤ) (x : GInt) :
    x ∈ paperLadderTile d ↔
      (((x.1 = 0 ∧ x.2 = 0) ∨ (x.1 = d + 2 ∧ x.2 = d + 2) ∨
          (x.1 + x.2 = d + 2 ∧ 1 < x.2 ∧ x.2 < d + 1) ∨
          (-d + 2 ≤ x.1 ∧ x.1 ≤ 2 * d ∧ 0 ≤ x.2 ∧ x.2 ≤ d + 2 ∧ 1 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ 2 * d + 3)) ∧
        ¬((d ≤ x.1 ∧ x.2 = 0) ∨ (x.1 ≤ 2 ∧ x.2 = d + 2))) := by
  unfold paperLadderTile paperLadderA paperLadderB paperLadderC paperLadderD
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.ext_iff]
  constructor <;> intro h <;> tauto

/-! ### Containment, the corner and the boundary lines for the ladder tile (d = 2m+4) -/

theorem ladder_contain (m : ℕ) (x : GInt)
    (hx : x ∈ placedSites (alongStrings (ladderH (m + 1)) (ladderV (m + 1)) (0, 0))) :
    x ∈ paperLadderTile (2 * (m : ℤ) + 4) := by
  rw [mem_alongStrings_ladder] at hx
  simp only [placedSites_append, List.mem_append] at hx
  rw [piece_lower, piece_top, piece_left, piece_right] at hx
  rw [mem_ladderT_disj]
  rcases hx with (((h1 | ⟨j1, hj1, h2⟩ | h3 | ⟨j2, hj2, h4⟩) | (⟨j3, hj3, h5⟩ | h6 | ⟨j4, hj4, h7⟩ | h8)) |
    (h9 | ⟨j5, hj5, h10⟩)) | (⟨j6, hj6, h11⟩ | h12)
  all_goals (simp only [oneAt, zeroAt, hOffset_p, Prod.fst_add, Prod.snd_add] at *; try push_cast at *; omega)

theorem ladder_lowerLeft (m : ℕ) :
    (0 : GInt) ∈ paperLadderTile (2 * (m : ℤ) + 4) ∧
      ∀ y ∈ paperLadderTile (2 * (m : ℤ) + 4), (0 : GInt).2 < y.2 ∨ ((0 : GInt).2 = y.2 ∧ (0 : GInt).1 ≤ y.1) := by
  refine ⟨?_, ?_⟩
  · rw [mem_ladderT_disj]
    refine ⟨Or.inl ⟨rfl, rfl⟩, ?_⟩
    rintro (⟨h1, _⟩ | ⟨_, h2⟩)
    · simp only [Prod.fst_zero] at h1
      omega
    · simp only [Prod.snd_zero] at h2
      omega
  · intro y hy
    rw [mem_ladderT_disj] at hy
    simp only [Prod.fst_zero, Prod.snd_zero]
    omega

/-- The boundary lines of `T = paperLadderTile (2m+4)` in one-sided form: `x.2 ≤ 0` (the bottom side), `x.1 ≤ -(2m+2)`
(the left side), `4m+8 ≤ x.1` (the right side), `2m+6 ≤ x.2` (the top side), `x.1+x.2 ≤ 1` and `4m+11 ≤ x.1+x.2`
(the two diagonals), the cut `x.2 ≤ 1 ∧ 2m+4 ≤ x.1` of the bottom row, and the cut `2m+5 ≤ x.2 ∧ x.1 ≤ 2` of the top row. -/
def LadderBL (m : ℤ) (x : GInt) : Prop :=
  x.2 ≤ 0 ∨ x.1 ≤ -(2 * m + 2) ∨ 4 * m + 8 ≤ x.1 ∨ 2 * m + 6 ≤ x.2 ∨ x.1 + x.2 ≤ 1 ∨ 4 * m + 11 ≤ x.1 + x.2 ∨
    (x.2 ≤ 1 ∧ 2 * m + 4 ≤ x.1) ∨ (2 * m + 5 ≤ x.2 ∧ x.1 ≤ 2)

/-- The neighbours of a point of `T` off the lines `LadderBL` lie in `T`. -/
theorem ladder_nbrs (m : ℕ) (x : GInt) (hT : x ∈ paperLadderTile (2 * (m : ℤ) + 4))
    (hne : ¬ LadderBL (m : ℤ) x) :
    (x.1 + 1, x.2) ∈ paperLadderTile (2 * (m : ℤ) + 4) ∧ (x.1 - 1, x.2) ∈ paperLadderTile (2 * (m : ℤ) + 4) ∧
      (x.1, x.2 + 1) ∈ paperLadderTile (2 * (m : ℤ) + 4) ∧ (x.1, x.2 - 1) ∈ paperLadderTile (2 * (m : ℤ) + 4) := by
  unfold LadderBL at hne
  have hT' := (mem_ladderT_disj (2 * (m : ℤ) + 4) x).1 hT
  have hin : 0 < x.2 ∧ x.2 < 2 * (m : ℤ) + 6 ∧ -(2 * (m : ℤ) + 2) < x.1 ∧ x.1 < 4 * (m : ℤ) + 8 ∧
      1 < x.1 + x.2 ∧ x.1 + x.2 < 4 * (m : ℤ) + 11 ∧ ¬(x.2 ≤ 1 ∧ 2 * (m : ℤ) + 4 ≤ x.1) ∧
        ¬(2 * (m : ℤ) + 5 ≤ x.2 ∧ x.1 ≤ 2) := by
    omega
  obtain ⟨hy1, hy2, hy3, hy4, hy5, hy6, hy7, hy8⟩ := hin
  clear hT' hne hT
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [mem_ladderT_disj] <;> dsimp only <;> omega

/-- The boundary lines: every point of `∂⁻T` lies on one of them. -/
theorem ladder_bl (m : ℕ) (x : GInt) (hT : x ∈ paperLadderTile (2 * (m : ℤ) + 4))
    (hB : (x.1 + 1, x.2) ∉ paperLadderTile (2 * (m : ℤ) + 4) ∨ (x.1 - 1, x.2) ∉ paperLadderTile (2 * (m : ℤ) + 4) ∨
      (x.1, x.2 + 1) ∉ paperLadderTile (2 * (m : ℤ) + 4) ∨ (x.1, x.2 - 1) ∉ paperLadderTile (2 * (m : ℤ) + 4)) :
    LadderBL (m : ℤ) x := by
  by_contra hne
  obtain ⟨n1, n2, n3, n4⟩ := ladder_nbrs m x hT hne
  rcases hB with h | h | h | h
  · exact h n1
  · exact h n2
  · exact h n3
  · exact h n4

/-- Covering (clause 2) for the ladder family: every site of `∂⁻T` is covered by the placed rectangles. -/
theorem ladder_cover (m : ℕ) (x : GInt)
    (hT : x ∈ paperLadderTile (2 * (m : ℤ) + 4))
    (hB : (x.1 + 1, x.2) ∉ paperLadderTile (2 * (m : ℤ) + 4) ∨ (x.1 - 1, x.2) ∉ paperLadderTile (2 * (m : ℤ) + 4) ∨
      (x.1, x.2 + 1) ∉ paperLadderTile (2 * (m : ℤ) + 4) ∨ (x.1, x.2 - 1) ∉ paperLadderTile (2 * (m : ℤ) + 4)) :
    x ∈ placedSites (alongStrings (ladderH (m + 1)) (ladderV (m + 1)) (0, 0)) := by
  have hL := ladder_bl m x hT hB
  unfold LadderBL at hL
  rw [mem_alongStrings_ladder]
  simp only [placedSites_append, List.mem_append]
  rw [piece_lower, piece_top, piece_left, piece_right]
  rw [mem_ladderT_disj] at hT
  rcases hL with h1 | h2 | h3 | h4 | h5 | h6 | ⟨h7a, h7b⟩ | ⟨h8a, h8b⟩
  · -- the bottom row x.2 = 0
    rcases le_or_gt x.1 1 with ha | ha
    · exact Or.inl (Or.inl (Or.inl (Or.inl (by simp only [oneAt]; omega))))
    · obtain ⟨j, hj⟩ := exists_nat_of_int ((x.1 - 2) / 2) (by omega)
      exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨j, by omega,
        by simp only [zeroAt, hOffset_p, Prod.fst_add, Prod.snd_add]; omega⟩))))
  · -- the left side x.1 = -(2m+2): the top zeros with j = 0
    exact Or.inl (Or.inl (Or.inr (Or.inl ⟨0, by omega, by simp only [zeroAt]; omega⟩)))
  · -- the right side x.1 = 4m+8: the second lower zeros
    obtain ⟨j, hj⟩ := exists_nat_of_int ((x.1 - 2 * (m : ℤ) - 5) / 2) (by omega)
    exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr ⟨j, by omega,
      by simp only [zeroAt, hOffset_p, Prod.fst_add, Prod.snd_add]; omega⟩)))))
  · -- the top side x.2 = 2m+6
    rcases le_or_gt (2 * (m : ℤ) + 5) x.1 with ha | ha
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (by simp only [oneAt]; omega))))))
    · obtain ⟨j, hj⟩ := exists_nat_of_int ((x.1 - 3) / 2) (by omega)
      exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, by omega, by simp only [zeroAt]; omega⟩)))))
  · -- the lower-left diagonal x.1 + x.2 = 1
    by_cases hb : x.2 ≤ 0
    · exact Or.inl (Or.inl (Or.inl (Or.inl (by simp only [oneAt]; omega))))
    · obtain ⟨j, hj⟩ := exists_nat_of_int (x.2 - 1) (by omega)
      exact Or.inl (Or.inr (Or.inr ⟨j, by omega, by simp only [zeroAt]; omega⟩))
  · -- the upper-right diagonal x.1 + x.2 = 4m+11
    by_cases hb : x.2 = 2 * (m : ℤ) + 6
    · exact Or.inr (Or.inr (by simp only [oneAt]; omega))
    · obtain ⟨j, hj⟩ := exists_nat_of_int (x.2 - 3) (by omega)
      exact Or.inr (Or.inl ⟨j, by omega, by simp only [zeroAt]; omega⟩)
  · -- the bottom row cut x.2 ≤ 1 with x.1 ≥ d
    by_cases ha : x.1 = 2 * (m : ℤ) + 4
    · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (by simp only [oneAt, hOffset_p, Prod.fst_add, Prod.snd_add]; omega))))))
    · obtain ⟨j, hj⟩ := exists_nat_of_int ((x.1 - 2 * (m : ℤ) - 5) / 2) (by omega)
      exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr ⟨j, by omega,
        by simp only [zeroAt, hOffset_p, Prod.fst_add, Prod.snd_add]; omega⟩)))))
  · -- the top row cut x.2 ≥ 2m+5 with x.1 ≤ 2
    by_cases ha : x.1 = 2
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (by simp only [oneAt]; omega)))))
    · obtain ⟨j, hj⟩ := exists_nat_of_int ((x.1 + 2 * (m : ℤ) + 2) / 2) (by omega)
      exact Or.inl (Or.inl (Or.inr (Or.inl ⟨j, by omega, by simp only [zeroAt]; omega⟩)))

/-- The doubled staircase family of `prop:base_cases` (d) for every `k ≥ 1`: `paperLadderTile (2k+2)` is a
`(q p^k q p^{k+1}, p^{2k+1} q)`-pseudo-square under the walk placement, with `c(T) = (0,0)`. -/
theorem ladder_isPseudoSquareAlongT (k : ℕ) (hk : 1 ≤ k) :
    IsPseudoSquareAlongT (paperLadderTile (2 * (k : ℤ) + 2)) (ladderH k) (ladderV k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hd : (2 * ((m + 1 : ℕ) : ℤ) + 2) = 2 * (m : ℤ) + 4 := by push_cast; ring
  rw [hd]
  obtain ⟨hz, hll⟩ := ladder_lowerLeft m
  exact ⟨(0, 0), ⟨hz, hll⟩, fun x hx => ladder_contain m x hx, fun x hx => ladder_cover m x hx.1 hx.2⟩

end FLatticePaper.Tiles
