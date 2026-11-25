import FLatticePaper.Tiles.GHJoin
import FLatticePaper.Tiles.WalkRows
import FLatticePaper.Tiles.SubCeilOdd
import FLatticePaper.Tiles.CeilWords

/-! Task Q25 (sub), the odd bottom walk: the blocks of the pseudo-square word.

For a binary word `x`, the tile of its letter `j` depends on the letter and its predecessor (`tileNew`). The tile sequence of
the prefix `x.take (m + 1)` is that of `x.take m` followed by the tile of letter `m` (`tileSeq_take_succ`), and the pair map
`G` of the prefix is a concatenation of blocks, one per pair of consecutive letters (`prefixG_succ`). Each block is one of
the words `[1, 1]` (EE), `[1, i]` (EN), `[i, 1]` (NE) (`block_EE`, `block_EN`, `block_NE`). -/

namespace FLatticePaper.Tiles.SubWalkOdd

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SubCeilOdd

/-- The tile of a letter given the previous letter (`p ↦ zero`, `q` after `q` is `oneD`, else `one`). -/
def tileNew (prev : Option Letter) (a : Letter) : ZTile :=
  match a, prev with
  | .p, _ => .zero
  | .q, some .q => .oneD
  | .q, _ => .one

theorem getLast_or_cons (a : Letter) (X : BinaryWord) (prev : Option Letter) :
    ((a :: X).getLast?).or prev = (X.getLast?).or (some a) := by
  cases X with
  | nil => simp
  | cons b Y =>
    have h1 : (a :: b :: Y).getLast? = (b :: Y).getLast? := by simp
    rw [h1]
    cases hY : (b :: Y).getLast? with
    | none => simp at hY
    | some z => simp

theorem tileSeqAux_snoc2 (prev : Option Letter) (X : BinaryWord) (a : Letter) :
    tileSeqAux prev (X ++ [a]) = tileSeqAux prev X ++ [tileNew (X.getLast?.or prev) a] := by
  induction X generalizing prev with
  | nil =>
    cases a <;> cases prev with
    | none => rfl
    | some b => cases b <;> rfl
  | cons x X ih => simp [tileSeqAux, ih, getLast_or_cons]

/-- The tile of letter `j` of `x`, with its predecessor. -/
def tl (x : BinaryWord) (j : ℕ) : ZTile := tileNew ((x.take j).getLast?) (x.getD j .p)

theorem tileSeq_take_succ (x : BinaryWord) (m : ℕ) (hm : m < x.length) :
    tileSeq (x.take (m + 1)) = tileSeq (x.take m) ++ [tl x m] := by
  have e : x.take (m + 1) = x.take m ++ [x.getD m .p] := by
    rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
    simp
  rw [e]
  unfold tileSeq tl
  rw [tileSeqAux_snoc2]
  simp

/-- The pair map of the prefix grows by the block of the two letters `j` and `j + 1`. -/
theorem prefixG_succ (x : BinaryWord) (j : ℕ) (hj : j + 2 ≤ x.length) :
    GHJoin.G (tileSeq (x.take (j + 2))) =
      GHJoin.G (tileSeq (x.take (j + 1))) ++ gPair (tl x j) (tl x (j + 1)) := by
  rw [tileSeq_take_succ x (j + 1) (by omega), tileSeq_take_succ x j (by omega)]
  have e2 : tileSeq (x.take j) ++ [tl x j] ++ [tl x (j + 1)] = tileSeq (x.take j) ++ tl x j :: [tl x (j + 1)] := by
    simp
  rw [e2, GHJoin.G_split, GHJoin.G_cons_cons, GHJoin.G_singleton, List.append_nil]

/-- The three block words, from the tile of the letter and the tile after it. -/
theorem block_pair (p0 : Option Letter) (a b : Letter) :
    gPair (tileNew p0 a) (tileNew (some a) b) =
      if a = .p ∧ b = .q then [Unit4.one, Unit4.i]
      else if a = .q ∧ p0 = some .q then [Unit4.i, Unit4.one]
      else [Unit4.one, Unit4.one] := by
  rcases p0 with _ | ⟨_ | _⟩ <;> cases a <;> cases b <;> simp [tileNew, gPair]

/-! ### The letters of a binary word and the ceiling package -/

/-- The indicator of a `q` letter at position `j` of `x`. -/
def epsOf (x : BinaryWord) (j : ℕ) : ℤ := if x.getD j .p = .q then 1 else 0

/-- The ceiling values `L · qPrefix j − 2N j`. -/
def gVal (N : ℤ) (x : BinaryWord) (j : ℕ) : ℤ := (x.length : ℤ) * CeilWords.qPrefix x j - 2 * N * j

theorem take_succ_eq (x : BinaryWord) (m : ℕ) (hm : m < x.length) :
    x.take (m + 1) = x.take m ++ [x.getD m .p] := by
  rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
  simp

theorem getLast_take_succ (x : BinaryWord) (m : ℕ) (hm : m < x.length) :
    (x.take (m + 1)).getLast? = some (x.getD m .p) := by
  rw [take_succ_eq x m hm]
  simp

theorem tY_epsOf (x : BinaryWord) (k : ℕ) (hk : k ≤ x.length) :
    tY (epsOf x) k = if (x.take k).getLast? = some .q then 1 else 0 := by
  cases k with
  | zero => simp [tY]
  | succ m =>
    rw [tY_succ, getLast_take_succ x m (by omega)]
    simp [epsOf]

theorem qPrefix_succ (x : BinaryWord) (j : ℕ) (hj : j < x.length) :
    CeilWords.qPrefix x (j + 1) = CeilWords.qPrefix x j + epsOf x j := by
  unfold CeilWords.qPrefix epsOf
  rw [take_succ_eq x j hj, List.count_append]
  rcases hx : x.getD j .p with _ | _ <;> simp

theorem ceilPack_of (N C : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ C) (x : BinaryWord)
    (hx : CeilWords.CeilWord x (2 * N) (2 * N + C)) :
    SubCeilOdd.CeilPack N C x.length (epsOf x) (gVal N x) := by
  have hL : (x.length : ℤ) = 2 * N + C := hx.1
  refine ⟨?_, ?_, ?_, ?_, ?_, hL⟩
  · intro j
    unfold epsOf
    split_ifs <;> simp
  · unfold gVal CeilWords.qPrefix
    simp
  · intro j hj
    unfold gVal
    rw [qPrefix_succ x j hj]
    push_cast
    ring
  · intro j hj
    have hj' : (j : ℤ) ≤ x.length := by exact_mod_cast hj
    have hb := hx.2 j (by linarith)
    unfold gVal
    rw [hL]
    constructor <;> nlinarith [hb.1, hb.2]
  · unfold gVal
    rw [CeilWords.ceil_total x (2 * N) (2 * N + C) hx (by omega)]
    rw [hx.1]
    ring

end FLatticePaper.Tiles.SubWalkOdd
