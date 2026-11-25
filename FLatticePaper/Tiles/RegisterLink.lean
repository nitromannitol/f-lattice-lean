import FLatticePaper.Tiles.GHJoin
import FLatticePaper.Tiles.RecursionIdentity
import FLatticePaper.Tiles.StandardBaseWords
import FLatticePaper.Tiles.BinaryWords

/-! Task Q25 (c), the register link: the bottom edges of a word are the pseudo-square map of its child words.

`quadAt [] u` is the word quadruple of the prefix `u` (`childP`, `childQ`, `parentP`, `parentQ`). Its child words are the
child operator at the parent pair (`childPQ_eq`). The odd (even) parent word is the odd (even) child word of the prefix
before the last letter `1` or `2` (`1` or `3`) (`parentP_eq_childP_srcOf`, `parentQ_eq_childQ_srcOf`). The base words
`2^k` and `3^k` have explicit quadruples (`quad_twos`, `quad_threes`). -/

namespace FLatticePaper.Tiles.RegisterLink

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.RecursionIdentity

/-- The join rule for a word ending in `p` followed by a word starting with `q`. -/
theorem gH_append_of_ends (X Y : BinaryWord) (hX : X.getLast? = some Letter.p)
    (hY : Y.head? = some Letter.q) : gH (X ++ Y) = gH X ++ [Unit4.i] ++ gH Y := by
  induction X using List.reverseRecOn with
  | nil => simp at hX
  | append_singleton X' x _ =>
    have hx : x = Letter.p := by simpa using hX
    subst hx
    cases Y with
    | nil => simp at hY
    | cons y Y' =>
      have hy : y = Letter.q := by simpa using hY
      subst hy
      exact GHJoin.gH_join X' Y'

/-- The child words of the quadruple of `u` are the child operator at its parent pair. -/
theorem childPQ_eq (u : Word) :
    (quadAt [] u).childP = (childWords u (quadAt [] u).parentP (quadAt [] u).parentQ).1 ∧
    (quadAt [] u).childQ = (childWords u (quadAt [] u).parentP (quadAt [] u).parentQ).2 := by
  induction u using List.reverseRecOn with
  | nil => simp [quadAt_nil, initialQuad]
  | append_singleton v d _ =>
    rw [quadAt_append_singleton]
    cases d <;> simp [WordQuad.step]

/-- The odd parent word of `u` is the odd child word of the prefix before the last letter `1` or `2`. -/
theorem parentP_eq_childP_srcOf (u : Word) (h : ∃ y ∈ u, y = Digit.one ∨ y = Digit.two) :
    (quadAt [] u).parentP = (quadAt [] (srcOf u).1).childP := by
  induction u using List.reverseRecOn with
  | nil => exact absurd h (by simp)
  | append_singleton v x ih =>
    have hsrc : (srcOf (v ++ [x])).1 = if x = Digit.one ∨ x = Digit.two then v else (srcOf v).1 := by
      unfold srcOf
      rw [srcFrom_snoc]
      simp
    cases x with
    | one => rw [hsrc]; simp [quadAt_append_singleton, WordQuad.step]
    | two => rw [hsrc]; simp [quadAt_append_singleton, WordQuad.step]
    | three =>
      have h' : ∃ y ∈ v, y = Digit.one ∨ y = Digit.two := by
        obtain ⟨y, hy, hy'⟩ := h
        rcases List.mem_append.1 hy with hy | hy
        · exact ⟨y, hy, hy'⟩
        · simp at hy
          subst hy
          simp at hy'
      rw [hsrc, quadAt_append_singleton]
      simp only [WordQuad.step, if_neg (show ¬(Digit.three = Digit.one ∨ Digit.three = Digit.two) by decide)]
      exact ih h'

/-- The even parent word of `u` is the even child word of the prefix before the last letter `1` or `3`. -/
theorem parentQ_eq_childQ_srcOf (u : Word) (h : ∃ y ∈ u, y = Digit.one ∨ y = Digit.three) :
    (quadAt [] u).parentQ = (quadAt [] (srcOf u).2).childQ := by
  induction u using List.reverseRecOn with
  | nil => exact absurd h (by simp)
  | append_singleton v x ih =>
    have hsrc : (srcOf (v ++ [x])).2 = if x = Digit.one ∨ x = Digit.three then v else (srcOf v).2 := by
      unfold srcOf
      rw [srcFrom_snoc]
      simp
    cases x with
    | one => rw [hsrc]; simp [quadAt_append_singleton, WordQuad.step]
    | three => rw [hsrc]; simp [quadAt_append_singleton, WordQuad.step]
    | two =>
      have h' : ∃ y ∈ v, y = Digit.one ∨ y = Digit.three := by
        obtain ⟨y, hy, hy'⟩ := h
        rcases List.mem_append.1 hy with hy | hy
        · exact ⟨y, hy, hy'⟩
        · simp at hy
          subst hy
          simp at hy'
      rw [hsrc, quadAt_append_singleton]
      simp only [WordQuad.step, if_neg (show ¬(Digit.two = Digit.one ∨ Digit.two = Digit.three) by decide)]
      exact ih h'

/-- The child operator on an even count of `1`s. -/
theorem childWords_of_even (w : Word) (pw qw : BinaryWord) (h : w.count Digit.one % 2 = 0) :
    childWords w pw qw = (qw ++ qw ++ pw, qw ++ pw) := by
  unfold childWords
  rw [if_pos h]

/-- The child operator on an odd count of `1`s. -/
theorem childWords_of_odd (w : Word) (pw qw : BinaryWord) (h : w.count Digit.one % 2 = 1) :
    childWords w pw qw = (pw ++ qw ++ qw, pw ++ qw) := by
  unfold childWords
  rw [if_neg (by omega)]

/-- The quad step by a final letter `2`, at the prefix `v`. -/
theorem quad_step_two (v : Word) : quadAt [] (v ++ [Digit.two]) =
    ⟨(childWords (v ++ [Digit.two]) (quadAt [] v).childP (quadAt [] v).parentQ).1,
     (childWords (v ++ [Digit.two]) (quadAt [] v).childP (quadAt [] v).parentQ).2,
     (quadAt [] v).childP, (quadAt [] v).parentQ⟩ := by
  rw [quadAt_append_singleton]
  rfl

/-- The quad step by a final letter `3`, at the prefix `v`. -/
theorem quad_step_three (v : Word) : quadAt [] (v ++ [Digit.three]) =
    ⟨(childWords (v ++ [Digit.three]) (quadAt [] v).parentP (quadAt [] v).childQ).1,
     (childWords (v ++ [Digit.three]) (quadAt [] v).parentP (quadAt [] v).childQ).2,
     (quadAt [] v).parentP, (quadAt [] v).childQ⟩ := by
  rw [quadAt_append_singleton]
  rfl

/-- The quadruple of `2^k`: `childP = q^{2k+2} p`, `childQ = q^{2k+1} p`, `parentQ = q`. -/
theorem quad_twos (k : ℕ) :
    (quadAt [] (List.replicate k Digit.two)).childP = List.replicate (2 * k + 2) Letter.q ++ [Letter.p] ∧
    (quadAt [] (List.replicate k Digit.two)).childQ = List.replicate (2 * k + 1) Letter.q ++ [Letter.p] ∧
    (quadAt [] (List.replicate k Digit.two)).parentQ = [Letter.q] := by
  induction k with
  | zero => simp [quadAt_nil, initialQuad, childWords]
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hn : Digit.one ∉ List.replicate k Digit.two := fun h => by
      have := List.eq_of_mem_replicate h
      cases this
    have hc : (List.replicate k Digit.two ++ [Digit.two]).count Digit.one % 2 = 0 := by
      rw [List.count_append, List.count_eq_zero.2 hn]
      simp
    rw [List.replicate_succ', quad_step_two, childWords_of_even _ _ _ hc, h1, h3]
    refine ⟨?_, ?_, ?_⟩
    · dsimp only
      rw [show 2 * (k + 1) + 2 = 2 + (2 * k + 2) by ring, List.replicate_add 2 (2 * k + 2)]
      rfl
    · dsimp only
      rw [show 2 * (k + 1) + 1 = 1 + (2 * k + 2) by ring, List.replicate_add 1 (2 * k + 2)]
      rfl
    · simp

/-- The quadruple of `3^k`: `childP = q p^k q p^{k+1}`, `childQ = q p^{k+1}`, `parentP = p`. -/
theorem quad_threes (k : ℕ) :
    (quadAt [] (List.replicate k Digit.three)).childP =
        [Letter.q] ++ List.replicate k Letter.p ++ [Letter.q] ++ List.replicate (k + 1) Letter.p ∧
    (quadAt [] (List.replicate k Digit.three)).childQ = [Letter.q] ++ List.replicate (k + 1) Letter.p ∧
    (quadAt [] (List.replicate k Digit.three)).parentP = [Letter.p] := by
  induction k with
  | zero => simp [quadAt_nil, initialQuad, childWords]
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hn : Digit.one ∉ List.replicate k Digit.three := fun h => by
      have := List.eq_of_mem_replicate h
      cases this
    have hc : (List.replicate k Digit.three ++ [Digit.three]).count Digit.one % 2 = 0 := by
      rw [List.count_append, List.count_eq_zero.2 hn]
      simp
    rw [List.replicate_succ', quad_step_three, childWords_of_even _ _ _ hc, h2, h3]
    refine ⟨?_, ?_, ?_⟩
    · dsimp only
      simp [List.append_assoc, List.replicate_succ']
    · dsimp only
      simp [List.append_assoc, List.replicate_succ']
    · simp

/-! ### The pseudo-square map on the base words -/

theorem tileSeqAux_p_rep (j : ℕ) (prev : Option Letter) (X : BinaryWord) :
    tileSeqAux prev (List.replicate (j + 1) Letter.p ++ X) =
      List.replicate (j + 1) ZTile.zero ++ tileSeqAux (some Letter.p) X := by
  induction j generalizing prev with
  | zero => simp [tileSeqAux]
  | succ j ih =>
    rw [List.replicate_succ, List.cons_append]
    simp only [tileSeqAux]
    rw [ih (some Letter.p)]
    simp [List.replicate_succ]

theorem tileSeqAux_qrun (j : ℕ) :
    tileSeqAux (some Letter.q) (List.replicate j Letter.q ++ [Letter.p]) =
      List.replicate j ZTile.oneD ++ [ZTile.zero] := by
  induction j with
  | zero => simp [tileSeqAux]
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, tileSeqAux]
    rw [ih]

theorem tileSeq_q_run (j : ℕ) :
    tileSeq (List.replicate (j + 1) Letter.q ++ [Letter.p]) =
      ZTile.one :: (List.replicate j ZTile.oneD ++ [ZTile.zero]) := by
  unfold tileSeq
  simp only [List.replicate_succ, List.cons_append, tileSeqAux]
  rw [tileSeqAux_qrun j]

theorem G_zeros (m : ℕ) : GHJoin.G (List.replicate (m + 1) ZTile.zero) =
    (List.replicate m [Unit4.one, Unit4.one]).flatten := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have e : List.replicate (m + 1 + 1) ZTile.zero = ZTile.zero :: ZTile.zero :: List.replicate m ZTile.zero := rfl
    have e2 : GHJoin.G (ZTile.zero :: List.replicate m ZTile.zero) =
        GHJoin.G (List.replicate (m + 1) ZTile.zero) := rfl
    rw [e, GHJoin.G_cons_cons, e2, ih]
    simp [List.replicate_succ, List.flatten_cons, gPair]

theorem G_one_zeros (m : ℕ) : GHJoin.G (ZTile.one :: List.replicate m ZTile.zero) =
    (List.replicate m [Unit4.one, Unit4.one]).flatten := by
  induction m with
  | zero => rfl
  | succ m _ =>
    have e : List.replicate (m + 1) ZTile.zero = ZTile.zero :: List.replicate m ZTile.zero := rfl
    have e2 : GHJoin.G (ZTile.zero :: List.replicate m ZTile.zero) =
        GHJoin.G (List.replicate (m + 1) ZTile.zero) := rfl
    rw [e, GHJoin.G_cons_cons, e2, G_zeros m]
    simp [List.replicate_succ, List.flatten_cons, gPair]

theorem G_oneD (j : ℕ) : GHJoin.G (List.replicate (j + 1) ZTile.oneD ++ [ZTile.zero]) =
    (List.replicate (j + 1) [Unit4.i, Unit4.one]).flatten := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have e : List.replicate (j + 1 + 1) ZTile.oneD ++ [ZTile.zero] =
        ZTile.oneD :: ZTile.oneD :: (List.replicate j ZTile.oneD ++ [ZTile.zero]) := rfl
    have e2 : GHJoin.G (ZTile.oneD :: (List.replicate j ZTile.oneD ++ [ZTile.zero])) =
        GHJoin.G (List.replicate (j + 1) ZTile.oneD ++ [ZTile.zero]) := rfl
    rw [e, GHJoin.G_cons_cons, e2, ih]
    simp [List.replicate_succ, List.flatten_cons, gPair]

theorem G_one_oneD (j : ℕ) : GHJoin.G (ZTile.one :: (List.replicate j ZTile.oneD ++ [ZTile.zero])) =
    [Unit4.one, Unit4.one] ++ (List.replicate j [Unit4.i, Unit4.one]).flatten := by
  cases j with
  | zero => rfl
  | succ j =>
    have e : ZTile.one :: (List.replicate (j + 1) ZTile.oneD ++ [ZTile.zero]) =
        ZTile.one :: ZTile.oneD :: (List.replicate j ZTile.oneD ++ [ZTile.zero]) := rfl
    have e2 : GHJoin.G (ZTile.oneD :: (List.replicate j ZTile.oneD ++ [ZTile.zero])) =
        GHJoin.G (List.replicate (j + 1) ZTile.oneD ++ [ZTile.zero]) := rfl
    rw [e, GHJoin.G_cons_cons, e2, G_oneD j]
    simp [gPair]

/-- The pair map of a zero run followed by the odd tile and a zero run. -/
theorem G_W (n m : ℕ) : GHJoin.G (List.replicate (n + 1) ZTile.zero ++ ZTile.one :: List.replicate m ZTile.zero) =
    (List.replicate n [Unit4.one, Unit4.one]).flatten ++ [Unit4.one, Unit4.i] ++
      (List.replicate m [Unit4.one, Unit4.one]).flatten := by
  induction n with
  | zero =>
    have e : List.replicate 1 ZTile.zero ++ ZTile.one :: List.replicate m ZTile.zero =
        ZTile.zero :: ZTile.one :: List.replicate m ZTile.zero := rfl
    rw [e, GHJoin.G_cons_cons, G_one_zeros m]
    simp [gPair]
  | succ n ih =>
    have e : List.replicate (n + 1 + 1) ZTile.zero ++ ZTile.one :: List.replicate m ZTile.zero =
        ZTile.zero :: ZTile.zero :: (List.replicate n ZTile.zero ++ ZTile.one :: List.replicate m ZTile.zero) := rfl
    have e2 : GHJoin.G (ZTile.zero :: (List.replicate n ZTile.zero ++ ZTile.one :: List.replicate m ZTile.zero)) =
        GHJoin.G (List.replicate (n + 1) ZTile.zero ++ ZTile.one :: List.replicate m ZTile.zero) := rfl
    rw [e, GHJoin.G_cons_cons, e2, ih]
    simp [List.replicate_succ, List.flatten_cons, gPair, List.append_assoc]

/-- The identity between the base edges `(1 i)`-runs and the `(i 1)`-runs. -/
theorem runs_identity (n : ℕ) : (List.replicate n [Unit4.one, Unit4.i]).flatten ++ [Unit4.one, Unit4.one] =
    Unit4.one :: ((List.replicate n [Unit4.i, Unit4.one]).flatten ++ [Unit4.one]) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, List.flatten_cons, ih]

/-! ### The base identities -/

theorem oneOne_flatten (m : ℕ) :
    (List.replicate m [Unit4.one, Unit4.one]).flatten = List.replicate (2 * m) Unit4.one := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, ih, show 2 * (m + 1) = 2 + 2 * m by ring,
      List.replicate_add 2 (2 * m)]
    rfl

theorem gH_two_odd (k : ℕ) :
    gH (List.replicate (2 * k + 2) Letter.q ++ [Letter.p]) = (baseTwoEdges k).1 := by
  rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, GHJoin.gH_eq, tileSeq_q_run (2 * k + 1),
    G_one_oneD (2 * k + 1)]
  simp [baseTwoEdges, oneI, runs_identity]

theorem gH_two_even (k : ℕ) :
    gH (List.replicate (2 * k + 1) Letter.q ++ [Letter.p]) = (baseTwoEdges k).2 := by
  rw [GHJoin.gH_eq, tileSeq_q_run (2 * k), G_one_oneD (2 * k)]
  simp [baseTwoEdges, oneI, runs_identity]

theorem gH_three_odd (j : ℕ) :
    gH ([Letter.q] ++ List.replicate (j + 1) Letter.p ++ [Letter.q] ++ List.replicate (j + 1 + 1) Letter.p) =
      (baseThreeEdges (j + 1)).1 := by
  have h1 : tileSeqAux (some Letter.q) (List.replicate (j + 1) Letter.p ++
      (Letter.q :: List.replicate (j + 1 + 1) Letter.p)) =
      List.replicate (j + 1) ZTile.zero ++ ZTile.one :: List.replicate (j + 1 + 1) ZTile.zero := by
    rw [tileSeqAux_p_rep j (some Letter.q) (Letter.q :: List.replicate (j + 1 + 1) Letter.p)]
    congr 1
    simp only [tileSeqAux]
    congr 1
    have h2 := tileSeqAux_p_rep (j + 1) (some Letter.q) []
    simpa [tileSeqAux] using h2
  have hts : tileSeq ([Letter.q] ++ List.replicate (j + 1) Letter.p ++ [Letter.q] ++
      List.replicate (j + 1 + 1) Letter.p) =
      ZTile.one :: (List.replicate (j + 1) ZTile.zero ++ ZTile.one :: List.replicate (j + 1 + 1) ZTile.zero) := by
    unfold tileSeq
    simp only [List.append_assoc, List.cons_append, List.nil_append, tileSeqAux]
    rw [h1]
  have hG : GHJoin.G (ZTile.one :: (List.replicate (j + 1) ZTile.zero ++
      ZTile.one :: List.replicate (j + 1 + 1) ZTile.zero)) =
      [Unit4.one, Unit4.one] ++ ((List.replicate j [Unit4.one, Unit4.one]).flatten ++ [Unit4.one, Unit4.i] ++
        (List.replicate (j + 1 + 1) [Unit4.one, Unit4.one]).flatten) := by
    have e : ZTile.one :: (List.replicate (j + 1) ZTile.zero ++ ZTile.one :: List.replicate (j + 1 + 1) ZTile.zero) =
        ZTile.one :: ZTile.zero :: (List.replicate j ZTile.zero ++ ZTile.one :: List.replicate (j + 1 + 1) ZTile.zero) :=
      rfl
    have e2 : GHJoin.G (ZTile.zero :: (List.replicate j ZTile.zero ++ ZTile.one :: List.replicate (j + 1 + 1) ZTile.zero)) =
        GHJoin.G (List.replicate (j + 1) ZTile.zero ++ ZTile.one :: List.replicate (j + 1 + 1) ZTile.zero) := rfl
    rw [e, GHJoin.G_cons_cons, e2, G_W j (j + 1 + 1)]
    simp [gPair]
  rw [GHJoin.gH_eq, hts, hG]
  simp [baseThreeEdges, oneOne, List.replicate_succ, List.flatten_cons]

theorem gH_three_even (j : ℕ) :
    gH ([Letter.q] ++ List.replicate (j + 1 + 1) Letter.p) = (baseThreeEdges (j + 1)).2 := by
  have hts : tileSeq ([Letter.q] ++ List.replicate (j + 1 + 1) Letter.p) =
      ZTile.one :: List.replicate (j + 1 + 1) ZTile.zero := by
    have h2 := tileSeqAux_p_rep (j + 1) (some Letter.q) []
    unfold tileSeq
    simp only [List.singleton_append, tileSeqAux]
    simpa [tileSeqAux] using h2
  rw [GHJoin.gH_eq, hts, G_one_zeros (j + 1 + 1)]
  show (List.replicate (j + 1 + 1) [Unit4.one, Unit4.one]).flatten ++ [Unit4.one] =
    [Unit4.one] ++ (List.replicate (j + 1 + 1) [Unit4.one, Unit4.one]).flatten
  rw [oneOne_flatten (j + 1 + 1), List.singleton_append, ← List.replicate_succ', ← List.replicate_succ]

/-! ### The source lengths -/

theorem srcOf_fst_snoc (v : Word) (x : Digit) :
    (srcOf (v ++ [x])).1 = if x = Digit.one ∨ x = Digit.two then v else (srcOf v).1 := by
  unfold srcOf
  rw [srcFrom_snoc]
  simp

theorem srcOf_snd_snoc (v : Word) (x : Digit) :
    (srcOf (v ++ [x])).2 = if x = Digit.one ∨ x = Digit.three then v else (srcOf v).2 := by
  unfold srcOf
  rw [srcFrom_snoc]
  simp

theorem srcOf_length_le (v : Word) : (srcOf v).1.length ≤ v.length ∧ (srcOf v).2.length ≤ v.length := by
  induction v using List.reverseRecOn with
  | nil => simp [srcOf, srcFrom]
  | append_singleton v x ih =>
    constructor
    · rw [srcOf_fst_snoc]
      split_ifs
      · simp
      · have := ih.1
        simp only [List.length_append, List.length_singleton]
        omega
    · rw [srcOf_snd_snoc]
      split_ifs
      · simp
      · have := ih.2
        simp only [List.length_append, List.length_singleton]
        omega

theorem srcOf_fst_length_lt (u : Word) (hu : u ≠ []) : (srcOf u).1.length < u.length := by
  induction u using List.reverseRecOn with
  | nil => exact absurd rfl hu
  | append_singleton v x _ =>
    rw [srcOf_fst_snoc]
    split_ifs
    · simp
    · have := (srcOf_length_le v).1
      simp only [List.length_append, List.length_singleton]
      omega

theorem srcOf_snd_length_lt (u : Word) (hu : u ≠ []) : (srcOf u).2.length < u.length := by
  induction u using List.reverseRecOn with
  | nil => exact absurd rfl hu
  | append_singleton v x _ =>
    rw [srcOf_snd_snoc]
    split_ifs
    · simp
    · have := (srcOf_length_le v).2
      simp only [List.length_append, List.length_singleton]
      omega

theorem getLast?_rep_p_tail (w : BinaryWord) (n : ℕ) :
    (w ++ List.replicate (n + 1) Letter.p).getLast? = some Letter.p := by
  rw [List.replicate_succ', ← List.append_assoc]
  simp

/-! ### The main identity -/

/-- The bottom edges of `u` are the pseudo-square map of its child words, and the child words start with `q` and end
with `p`. -/
def BottomQ (u : Word) : Prop :=
  (bottomEdges u).1 = gH (quadAt [] u).childP ∧ (bottomEdges u).2 = gH (quadAt [] u).childQ ∧
    (quadAt [] u).childP.head? = some Letter.q ∧ (quadAt [] u).childP.getLast? = some Letter.p ∧
    (quadAt [] u).childQ.head? = some Letter.q ∧ (quadAt [] u).childQ.getLast? = some Letter.p

theorem bottomQ_twos (u : Word) (hT : allTwos u = true) : BottomQ u := by
  obtain ⟨k, rfl⟩ : ∃ k, u = List.replicate k Digit.two := by
    refine ⟨u.length, List.eq_replicate_iff.2 ⟨rfl, fun b hb => ?_⟩⟩
    unfold allTwos at hT
    have := List.all_eq_true.1 hT b hb
    simpa using this
  have hb := StandardBaseWords.bottomEdges_two k
  have hq := quad_twos k
  unfold BottomQ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb, hq.1, gH_two_odd]
  · rw [hb, hq.2.1, gH_two_even]
  · rw [hq.1]; simp [List.replicate_succ]
  · rw [hq.1]; simp [List.getLast?_append]
  · rw [hq.2.1]; simp [List.replicate_succ]
  · rw [hq.2.1]; simp [List.getLast?_append]

theorem bottomQ_threes (u : Word) (hH : allThrees u = true) : BottomQ u := by
  have hne : u ≠ [] := by
    rintro rfl
    simp [allThrees] at hH
  have hlen : 1 ≤ u.length := List.length_pos_iff.2 hne
  obtain ⟨k, hk, rfl⟩ : ∃ k, 1 ≤ k ∧ u = List.replicate k Digit.three := by
    unfold allThrees at hH
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hH
    refine ⟨u.length, hlen, List.eq_replicate_iff.2 ⟨rfl, fun b hb => ?_⟩⟩
    have := List.all_eq_true.1 hH.2 b hb
    simpa using this
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hb := StandardBaseWords.bottomEdges_three (j + 1) (by omega)
  have hq := quad_threes (j + 1)
  unfold BottomQ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb, hq.1, gH_three_odd]
  · rw [hb, hq.2.1, gH_three_even]
  · rw [hq.1]; simp [List.replicate_succ]
  · rw [hq.1]; exact getLast?_rep_p_tail _ (j + 1)
  · rw [hq.2.1]; simp [List.replicate_succ]
  · rw [hq.2.1]; exact getLast?_rep_p_tail _ (j + 1)

/-- The main identity: the bottom edges of every word are the pseudo-square map of its child words. -/
theorem bottomQ_all (u : Word) : BottomQ u := by
  suffices h : ∀ n : ℕ, ∀ v : Word, v.length ≤ n → BottomQ v from h _ u le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    by_cases hT : allTwos v = true
    · exact bottomQ_twos v hT
    by_cases hH : allThrees v = true
    · exact bottomQ_threes v hH
    have hT' : allTwos v = false := by simpa using hT
    have hH' : allThrees v = false := by simpa using hH
    have hne : v ≠ [] := by
      rintro rfl
      simp [allTwos] at hT
    have hs1 := srcOf_fst_length_lt v hne
    have hs2 := srcOf_snd_length_lt v hne
    obtain ⟨I1a, I1b, I1c, I1d, I1e, I1f⟩ := ih (srcOf v).1.length (by omega) (srcOf v).1 le_rfl
    obtain ⟨I2a, I2b, I2c, I2d, I2e, I2f⟩ := ih (srcOf v).2.length (by omega) (srcOf v).2 le_rfl
    have hP := parentP_eq_childP_srcOf v (exists_one_or_two v hT' hH')
    have hQ := parentQ_eq_childQ_srcOf v (exists_one_or_three v hT')
    unfold BottomQ
    rw [bottomEdges_rec v hT' hH']
    by_cases hodd : v.count Digit.one % 2 = 1
    · have hb : (v.count Digit.one % 2 == 1) = true := by simp [hodd]
      have hCP : (quadAt [] v).childP = (quadAt [] (srcOf v).1).childP ++
          ((quadAt [] (srcOf v).2).childQ ++ (quadAt [] (srcOf v).2).childQ) := by
        rw [(childPQ_eq v).1, childWords_of_odd v _ _ hodd, hP, hQ]
        simp [List.append_assoc]
      have hCQ : (quadAt [] v).childQ = (quadAt [] (srcOf v).1).childP ++ (quadAt [] (srcOf v).2).childQ := by
        rw [(childPQ_eq v).2, childWords_of_odd v _ _ hodd, hP, hQ]
      simp only [edgeStep, hb, ite_true]
      rw [I1a, I2b]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hCP, gH_append_of_ends _ _ I1d (by simp [I2e]), gH_append_of_ends _ _ I2f I2e]
        simp [List.append_assoc]
      · rw [hCQ, gH_append_of_ends _ _ I1d I2e]
      · rw [hCP]; simp [I1c]
      · rw [hCP]; simp [List.getLast?_append, I2f]
      · rw [hCQ]; simp [I1c]
      · rw [hCQ]; simp [List.getLast?_append, I2f]
    · have hodd0 : v.count Digit.one % 2 = 0 := by omega
      have hb : (v.count Digit.one % 2 == 1) = false := by simp [hodd0]
      have hCP : (quadAt [] v).childP = (quadAt [] (srcOf v).2).childQ ++
          ((quadAt [] (srcOf v).2).childQ ++ (quadAt [] (srcOf v).1).childP) := by
        rw [(childPQ_eq v).1, childWords_of_even v _ _ hodd0, hP, hQ]
        simp [List.append_assoc]
      have hCQ : (quadAt [] v).childQ = (quadAt [] (srcOf v).2).childQ ++ (quadAt [] (srcOf v).1).childP := by
        rw [(childPQ_eq v).2, childWords_of_even v _ _ hodd0, hP, hQ]
      simp only [edgeStep, hb, Bool.false_eq_true, ite_false]
      rw [I1a, I2b]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hCP, gH_append_of_ends _ _ I2f (by simp [I2e]), gH_append_of_ends _ _ I2f I1c]
        simp [List.append_assoc]
      · rw [hCQ, gH_append_of_ends _ _ I2f I1c]
      · rw [hCP]; simp [I2e]
      · rw [hCP]; simp [List.getLast?_append, I1d]
      · rw [hCQ]; simp [I2e]
      · rw [hCQ]; simp [List.getLast?_append, I1d]

/-- The odd bottom edge of `u` is the pseudo-square map of the odd child word of `u`. -/
theorem oddBottom_eq_gH (u : Word) : (bottomEdges u).1 = gH (quadAt [] u).childP := (bottomQ_all u).1

/-- The even bottom edge of `u` is the pseudo-square map of the even child word of `u`. -/
theorem evenBottom_eq_gH (u : Word) : (bottomEdges u).2 = gH (quadAt [] u).childQ := (bottomQ_all u).2.1

end FLatticePaper.Tiles.RegisterLink
