import FLatticePaper.Graph
import FLatticePaper.Tiles.BinaryWords
import Mathlib.Tactic.Abel
import Mathlib.Data.List.GetD

namespace FLatticePaper.Tiles

/-- A letter of a binary word at an index in range, read through the total accessor `getD`. -/
theorem getD_eq_getElem_of_lt {w : BinaryWord} {i : ℕ} {d : Letter} (h : i < w.length) :
    w.getD i d = w[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- The first letter of a word with a given head. -/
theorem getD_zero_of_head? {w : BinaryWord} {a : Letter} (h : w.head? = some a) :
    w.getD 0 .p = a := by
  rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, h]
  rfl

/-- The letter at the last position of a word with a given last letter. -/
theorem getD_last_of_getLast? {w : BinaryWord} {b : Letter} (h : w.getLast? = some b) :
    w.getD (w.length - 1) .p = b := by
  rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, h]
  rfl

/-- Telescoping induction: an offset `D` whose first value and whose successive increments agree with a target
`f` agrees with `f` at every index below `m`. Every boundary identity below reduces to this helper. -/
theorem offset_induction {D f : ℕ → Site} {m : ℕ} (hbase : 1 < m → D 1 = f 1)
    (hstep : ∀ j, 1 ≤ j → j + 1 < m → D (j + 1) - D j = f (j + 1) - f j) :
    ∀ i, 1 ≤ i → i < m → D i = f i := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => exact fun hm => hbase hm
  | succ k hk ih =>
    intro hkm
    have hD : D k = f k := ih (by omega)
    have hs := hstep k hk (by omega)
    calc D (k + 1) = (D (k + 1) - D k) + D k := by abel
      _ = (f (k + 1) - f k) + f k := by rw [hs, hD]
      _ = f (k + 1) := by abel

/-- In an almost palindrome, the letters away from both ends agree with those of the reversed word. -/
theorem IsAlmostPalindrome.getD_eq_reverse {w : BinaryWord} (hw : IsAlmostPalindrome w) {j : ℕ}
    (hj : 1 ≤ j) (hj' : j + 1 < w.length) : w.getD j .p = w.reverse.getD j .p := by
  obtain ⟨first, last, middle, hmid, rfl⟩ := hw
  have hrev : (first :: (middle ++ [last])).reverse = last :: (middle ++ [first]) := by
    simp [List.reverse_cons, List.reverse_append, hmid]
  rw [hrev]
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hk : k < middle.length := by simp at hj'; omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, hk]

/-- The two ends of an almost palindrome: the reversed word has the last letter first and the first letter last. -/
theorem IsAlmostPalindrome.two_le_length_and_ends {w : BinaryWord} (hw : IsAlmostPalindrome w) :
    2 ≤ w.length ∧ w.reverse.getD 0 .p = w.getD (w.length - 1) .p ∧
      w.reverse.getD (w.length - 1) .p = w.getD 0 .p := by
  obtain ⟨first, last, middle, hmid, rfl⟩ := hw
  have hrev : (first :: (middle ++ [last])).reverse = last :: (middle ++ [first]) := by
    simp [List.reverse_cons, List.reverse_append, hmid]
  have hlen : (first :: (middle ++ [last])).length - 1 = middle.length + 1 := by
    simp
  rw [hrev, hlen]
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.length_cons, List.length_append]
    omega
  · simp [List.getD_eq_getElem?_getD]
  · simp [List.getD_eq_getElem?_getD]

/-- Shared offset argument for the zero-one strings. The corner offset at each interior position is the target
value of its letter, and the offset at the last position is the fixed value `F`. -/
theorem zeroOne_offsets {w : BinaryWord} (hw : IsAlmostPalindrome w) (first last : Letter)
    (hfirst : w.getD 0 .p = first) (hlast : w.getD (w.length - 1) .p = last)
    (S : Letter → Site) (R : Letter → Letter → Site) (T : Letter → Site) (D0 F : Site)
    (hcompat : ∀ a b, S b - R a b = T b - T a)
    (hbase : ∀ b, D0 + S b - R last b = T b)
    (hend : D0 + S last - R last first = F)
    (hfin : ∀ c, T c + S last - R c first = F)
    (plus minus : ℕ → Site)
    (hplus : ∀ i, i + 1 < w.length → plus (i + 1) - plus i = S (w.getD (i + 1) .p))
    (hminus : ∀ i, i + 1 < w.length →
      minus (i + 1) - minus i = R (w.reverse.getD i .p) (w.reverse.getD (i + 1) .p))
    (hstack : plus 0 - minus 0 = D0) :
    (∀ i, i + 1 < w.length → 0 < i → plus i - minus i = T (w.getD i .p)) ∧
      plus (w.length - 1) - minus (w.length - 1) = F := by
  obtain ⟨hlen, hrev0, hrevEnd⟩ := hw.two_le_length_and_ends
  have hrev0' : w.reverse.getD 0 .p = last := hrev0.trans hlast
  have hrevEnd' : w.reverse.getD (w.length - 1) .p = first := hrevEnd.trans hfirst
  have hstepD : ∀ j (h : j + 1 < w.length),
      (plus (j + 1) - minus (j + 1)) - (plus j - minus j) =
        S (w.getD (j + 1) .p) - R (w.reverse.getD j .p) (w.reverse.getD (j + 1) .p) := by
    intro j h
    have e : (plus (j + 1) - minus (j + 1)) - (plus j - minus j) =
        (plus (j + 1) - plus j) - (minus (j + 1) - minus j) := by abel
    rw [e, hplus j h, hminus j h]
  have hbase1 : 1 < w.length - 1 → plus 1 - minus 1 = T (w.getD 1 .p) := by
    intro hm
    have e1 : plus 1 - plus 0 = S (w.getD 1 .p) := hplus 0 (by omega)
    have e2 : minus 1 - minus 0 = R (w.reverse.getD 0 .p) (w.reverse.getD 1 .p) := hminus 0 (by omega)
    have hr1 : w.reverse.getD 1 .p = w.getD 1 .p := (hw.getD_eq_reverse le_rfl (by omega)).symm
    have e : plus 1 - minus 1 = (plus 1 - plus 0) - (minus 1 - minus 0) + (plus 0 - minus 0) := by abel
    rw [e, e1, e2, hstack, hr1, hrev0']
    rw [← hbase (w.getD 1 .p)]
    abel
  have hstep' : ∀ j, 1 ≤ j → j + 1 < w.length - 1 →
      (plus (j + 1) - minus (j + 1)) - (plus j - minus j) = T (w.getD (j + 1) .p) - T (w.getD j .p) := by
    intro j hj hj'
    rw [hstepD j (by omega), ← hw.getD_eq_reverse hj (by omega),
      ← hw.getD_eq_reverse (j := j + 1) (by omega) (by omega), hcompat]
  have hmain := offset_induction (D := fun i => plus i - minus i) (f := fun i => T (w.getD i .p))
    (m := w.length - 1) (fun hm => hbase1 hm) (fun j hj hj' => hstep' j hj hj')
  refine ⟨fun i h hi => hmain i (by omega) (by omega), ?_⟩
  obtain ⟨k, hk⟩ : ∃ k, w.length = k + 2 := ⟨w.length - 2, by omega⟩
  have hn1 : w.length - 1 = k + 1 := by omega
  rw [hn1]
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    show plus 1 - minus 1 = F
    have e : (plus 1 - minus 1) - (plus 0 - minus 0) =
        S (w.getD 1 .p) - R (w.reverse.getD 0 .p) (w.reverse.getD 1 .p) :=
      hstepD 0 (by omega)
    have hlast1 : w.getD 1 .p = last := by
      have h := hlast
      rwa [show w.length - 1 = 1 by omega] at h
    have hfirst1 : w.reverse.getD 1 .p = first := by
      have h := hrevEnd'
      rwa [show w.length - 1 = 1 by omega] at h
    calc plus 1 - minus 1 = (plus 0 - minus 0) + ((plus 1 - minus 1) - (plus 0 - minus 0)) := by abel
      _ = D0 + (S last - R last first) := by rw [e, hstack, hlast1, hrev0', hfirst1]
      _ = F := by rw [← hend]; abel
  · have hmk : plus k - minus k = T (w.getD k .p) := hmain k hkpos (by omega)
    have e : (plus (k + 1) - minus (k + 1)) - (plus k - minus k) =
        S (w.getD (k + 1) .p) - R (w.reverse.getD k .p) (w.reverse.getD (k + 1) .p) :=
      hstepD k (by omega)
    have hwk : w.reverse.getD k .p = w.getD k .p := (hw.getD_eq_reverse hkpos (by omega)).symm
    have hwk1 : w.getD (k + 1) .p = last := by
      have h := hlast
      rwa [hn1] at h
    have hrk1 : w.reverse.getD (k + 1) .p = first := by
      have h := hrevEnd'
      rwa [hn1] at h
    calc plus (k + 1) - minus (k + 1)
        = (plus k - minus k) + ((plus (k + 1) - minus (k + 1)) - (plus k - minus k)) := by abel
      _ = T (w.getD k .p) + (S last - R (w.getD k .p) first) := by
          rw [e, hmk, hwk, hwk1, hrk1]
      _ = F := by rw [← hfin (w.getD k .p)]; abel

/-- Corner steps of a horizontal zero-one string (`eq:zero-one-bs`), indexed by the new tile. -/
def zeroOneHorizontalStep : Letter → Site
  | .q => (1, 1)
  | .p => (2, 0)

/-- Corner steps of a reversed horizontal zero-one string (`eq:zero-one-bs-reversed`), by the tile pair. -/
def zeroOneHorizontalReversedStep : Letter → Letter → Site
  | .p, .q => (2, 1)
  | .p, .p => (2, 0)
  | .q, .p => (1, 0)
  | .q, .q => (1, 1)

def zeroOneVerticalStep : Letter → Site
  | .q => (0, 2)
  | .p => (-1, 1)

def zeroOneVerticalReversedStep : Letter → Letter → Site
  | .p, .q => (-1, 2)
  | .p, .p => (-1, 1)
  | .q, .p => (0, 1)
  | .q, .q => (0, 2)

/-- The target offsets of the horizontal zero-one string, indexed by the letter of the interior position. -/
def zeroOneHorizontalTarget : Letter → Site
  | .q => (-2, 2)
  | .p => (-1, 2)

/-- The target offsets of the vertical zero-one string, indexed by the letter of the interior position. -/
def zeroOneVerticalTarget : Letter → Site
  | .q => (-1, -1)
  | .p => (-2, -1)

/-- `lemma:almost_palindrome_offset`. `along s = v_{s,j}`, `across s = v_{s,j'}`. `plus` are the corners of the
string `B_w`, `minus` those of the reversed string `B^r_{rev w}`. -/
theorem almost_palindrome_offset (along across : Letter → Site) (w : BinaryWord)
    (hw : IsAlmostPalindrome w) (plus minus : ℕ → Site)
    (hplus : ∀ i (h : i + 1 < w.length), plus (i + 1) - plus i = along w[i])
    (hminus : ∀ i (h : i + 1 < w.length), minus (i + 1) - minus i =
      along (w.reverse[i]'(by simp; omega)) + (across (w.reverse[i]'(by simp; omega)) -
        across (w.reverse[i + 1]'(by simp; omega))))
    (hstack : ∀ h : 0 < w.length, plus 0 - minus 0 = across (w.reverse[0]'(by simp; omega))) :
    ∀ i (h : i < w.length), 0 < i →
      plus i - minus i = across (w.reverse[i]'(by simp; omega)) +
        (along (w[0]'(by omega)) - along (w.reverse[0]'(by simp; omega))) := by
  intro i h hi
  have hn0 : 0 < w.length := by omega
  have hstack' : plus 0 - minus 0 = across (w.reverse.getD 0 .p) := by
    rw [hstack hn0, getD_eq_getElem_of_lt (show 0 < w.reverse.length by simp; omega)]
  have hplus' : ∀ j (h' : j + 1 < w.length),
      plus (j + 1) - plus j = along (w.getD j .p) := by
    intro j h'
    rw [hplus j h', getD_eq_getElem_of_lt (show j < w.length by omega)]
  have hminus' : ∀ j (h' : j + 1 < w.length),
      minus (j + 1) - minus j =
        along (w.reverse.getD j .p) + (across (w.reverse.getD j .p) - across (w.reverse.getD (j + 1) .p)) := by
    intro j h'
    rw [hminus j h', getD_eq_getElem_of_lt (show j < w.reverse.length by simp; omega),
      getD_eq_getElem_of_lt (show j + 1 < w.reverse.length by simp; omega)]
  have hbase : 1 < w.length → plus 1 - minus 1 =
      across (w.reverse.getD 1 .p) + (along (w.getD 0 .p) - along (w.reverse.getD 0 .p)) := by
    intro h1
    have e1 : plus 1 - plus 0 = along (w.getD 0 .p) := hplus' 0 h1
    have e2 : minus 1 - minus 0 =
        along (w.reverse.getD 0 .p) + (across (w.reverse.getD 0 .p) - across (w.reverse.getD 1 .p)) :=
      hminus' 0 h1
    have e : plus 1 - minus 1 = (plus 1 - plus 0) - (minus 1 - minus 0) + (plus 0 - minus 0) := by abel
    rw [e, e1, e2, hstack']
    abel
  have hstep : ∀ j, 1 ≤ j → j + 1 < w.length →
      (plus (j + 1) - minus (j + 1)) - (plus j - minus j) =
        (across (w.reverse.getD (j + 1) .p) + (along (w.getD 0 .p) - along (w.reverse.getD 0 .p))) -
          (across (w.reverse.getD j .p) + (along (w.getD 0 .p) - along (w.reverse.getD 0 .p))) := by
    intro j hj hj'
    have e : (plus (j + 1) - minus (j + 1)) - (plus j - minus j) =
        (plus (j + 1) - plus j) - (minus (j + 1) - minus j) := by abel
    rw [e, hplus' j hj', hminus' j hj', ← hw.getD_eq_reverse hj hj']
    abel
  have hmain := offset_induction (D := fun k => plus k - minus k)
    (f := fun k => across (w.reverse.getD k .p) + (along (w.getD 0 .p) - along (w.reverse.getD 0 .p)))
    (m := w.length) hbase hstep
  have key : plus i - minus i =
      across (w.reverse.getD i .p) + (along (w.getD 0 .p) - along (w.reverse.getD 0 .p)) :=
    hmain i hi h
  rw [getD_eq_getElem_of_lt (show i < w.reverse.length by simp; omega),
    getD_eq_getElem_of_lt hn0, getD_eq_getElem_of_lt (show 0 < w.reverse.length by simp; omega)] at key
  exact key

/-- `lemma:zero-one-fixed-offsets`, horizontal case. -/
theorem zeroOne_fixed_offsets_horizontal (w : BinaryWord) (hw : IsAlmostPalindrome w)
    (hfirst : w.head? = some .q) (hlast : w.getLast? = some .p) (plus minus : ℕ → Site)
    (hplus : ∀ i (h : i + 1 < w.length), plus (i + 1) - plus i = zeroOneHorizontalStep w[i + 1])
    (hminus : ∀ i (h : i + 1 < w.length), minus (i + 1) - minus i =
      zeroOneHorizontalReversedStep (w.reverse[i]'(by simp; omega)) (w.reverse[i + 1]'(by simp; omega)))
    (hstack : plus 0 - minus 0 = (-1, 2)) :
    (∀ i (h : i + 1 < w.length), 0 < i → w[i] = .q → plus i - minus i = (-2, 2)) ∧
    (∀ i (h : i + 1 < w.length), 0 < i → w[i] = .p → plus i - minus i = (-1, 2)) ∧
    plus (w.length - 1) - minus (w.length - 1) = (-1, 1) := by
  have key := zeroOne_offsets hw .q .p (getD_zero_of_head? hfirst) (getD_last_of_getLast? hlast)
    zeroOneHorizontalStep zeroOneHorizontalReversedStep zeroOneHorizontalTarget (-1, 2) (-1, 1)
    (by intro a b; cases a <;> cases b <;> decide)
    (by intro b; cases b <;> decide)
    (by decide)
    (by intro c; cases c <;> decide)
    plus minus
    (fun i h => by rw [hplus i h, getD_eq_getElem_of_lt h])
    (fun i h => by
      rw [hminus i h, getD_eq_getElem_of_lt (show i < w.reverse.length by simp; omega),
        getD_eq_getElem_of_lt (show i + 1 < w.reverse.length by simp; omega)])
    hstack
  obtain ⟨hmain, hend⟩ := key
  refine ⟨fun i h hi hq => ?_, fun i h hi hp => ?_, hend⟩
  · rw [hmain i h hi, (getD_eq_getElem_of_lt (show i < w.length by omega)).trans hq]
    rfl
  · rw [hmain i h hi, (getD_eq_getElem_of_lt (show i < w.length by omega)).trans hp]
    rfl

/-- `lemma:zero-one-fixed-offsets`, vertical case. -/
theorem zeroOne_fixed_offsets_vertical (w : BinaryWord) (hw : IsAlmostPalindrome w)
    (hfirst : w.head? = some .p) (hlast : w.getLast? = some .q) (plus minus : ℕ → Site)
    (hplus : ∀ i (h : i + 1 < w.length), plus (i + 1) - plus i = zeroOneVerticalStep w[i + 1])
    (hminus : ∀ i (h : i + 1 < w.length), minus (i + 1) - minus i =
      zeroOneVerticalReversedStep (w.reverse[i]'(by simp; omega)) (w.reverse[i + 1]'(by simp; omega)))
    (hstack : plus 0 - minus 0 = (-1, -1)) :
    (∀ i (h : i + 1 < w.length), 0 < i → w[i] = .q → plus i - minus i = (-1, -1)) ∧
    (∀ i (h : i + 1 < w.length), 0 < i → w[i] = .p → plus i - minus i = (-2, -1)) ∧
    plus (w.length - 1) - minus (w.length - 1) = (-1, 0) := by
  have key := zeroOne_offsets hw .p .q (getD_zero_of_head? hfirst) (getD_last_of_getLast? hlast)
    zeroOneVerticalStep zeroOneVerticalReversedStep zeroOneVerticalTarget (-1, -1) (-1, 0)
    (by intro a b; cases a <;> cases b <;> decide)
    (by intro b; cases b <;> decide)
    (by decide)
    (by intro c; cases c <;> decide)
    plus minus
    (fun i h => by rw [hplus i h, getD_eq_getElem_of_lt h])
    (fun i h => by
      rw [hminus i h, getD_eq_getElem_of_lt (show i < w.reverse.length by simp; omega),
        getD_eq_getElem_of_lt (show i + 1 < w.reverse.length by simp; omega)])
    hstack
  obtain ⟨hmain, hend⟩ := key
  refine ⟨fun i h hi hq => ?_, fun i h hi hp => ?_, hend⟩
  · rw [hmain i h hi, (getD_eq_getElem_of_lt (show i < w.length by omega)).trans hq]
    rfl
  · rw [hmain i h hi, (getD_eq_getElem_of_lt (show i < w.length by omega)).trans hp]
    rfl

end FLatticePaper.Tiles
