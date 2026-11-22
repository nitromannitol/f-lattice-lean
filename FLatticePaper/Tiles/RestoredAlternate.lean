import FLatticePaper.Tiles.AlternateOrdinary

/-! # The restored alternate tiles `TA` (task 45, step 1)

The literal alternate recursion `altChildren`, `altStep`, `altRun`, `altState` (AlternateTiles.lean) with the head restoration
built in: the alternate piece of the children of a non-base word `pre` is placed at its literal offset plus
`alternateRestoration pre` (the odd child takes the even alternate retained tile restored by `alternateRestoration pre .even`,
the even child takes the odd alternate retained tile restored by `alternateRestoration pre .odd`). The base words keep the
literal base tiles `altBase`. The recursion is the literal one with the restored children in place of the literal children;
the alternate retained tiles are the restored children of the birth words, unrestored (as the constructor stores them).

The base words take the constructor's own base masks (`BaseRun.registers` of the pure run, normalised, alternate current
tiles), not the PROVISIONAL TeX alternate base tiles `altBase`: the constructor's alternate base registers are explicit Lean
objects (the masks `stairOddAlt`, `stairEvenAlt`, `ladderOddAlt`, `ladderEvenAlt` of BaseMasks.lean). Numerically they agree
with the TeX alternate base tiles for the pure words of length at most 3 (the native logs, task 43).

`restoredChildren_fst`, `restoredChildren_snd` unfold the definition on non-base words. The structural lemma of
AlternateOrdinary.lean, applied to a state whose registers are the parents' registers, is then the statement that the
ordinary alternate schedule of a word has the sites of `restoredChildren` of that word. -/

namespace FLatticePaper.Tiles.RestoredAlternate

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.Alternate FLatticePaper.Tiles.AlternateOrdinary FLatticePaper.Construction

/-- The base run of a pure word (`[]` for the empty word; `twos` or `threes` of the length minus one otherwise). -/
def pureRun : Word → BaseRun
  | [] => .empty
  | .one :: _ => .empty
  | .two :: rest => .twos rest.length
  | .three :: rest => .threes rest.length

/-- The alternate children of a base word: the constructor's own normalised alternate current tiles of its base run. -/
def baseAltChildren (pre : Word) : Tile × Tile :=
  (((pureRun pre).registers.llCenter).alternate.currentOdd.val.sites,
    ((pureRun pre).registers.llCenter).alternate.currentEven.val.sites)

/-- The restored alternate children of the prefix `pre` from its state `s`. -/
def restoredChildren (pre : Word) (s : AState) : Tile × Tile :=
  if IsBase pre then baseAltChildren pre
  else altPair (phase pre == 1) (lastDigit pre) s.std.tOdd s.std.tEven
    (shift s.aOdd (alternateRestoration pre .odd)) (shift s.aEven (alternateRestoration pre .even))
    s.std.par.odd s.std.par.even

/-- One letter of the restored recursion (the standard registers advance as in `stepState`). -/
def restoredStep (pre : Word) (s : AState) (d : Digit) : AState :=
  let c := restoredChildren pre s
  let std' := stepState pre s.std d
  match d with
  | .one => ⟨std', c.1, c.2⟩
  | .two => ⟨std', c.1, s.aEven⟩
  | .three => ⟨std', s.aOdd, c.2⟩

/-- Reads the letters of a word after the prefix `pre`, in the restored recursion. -/
def restoredRun (pre : Word) : Word → AState → AState
  | [], s => s
  | d :: rest, s => restoredRun (pre ++ [d]) rest (restoredStep pre s d)

/-- The state after reading a word in the restored recursion. -/
def restoredState (w : Word) : AState :=
  restoredRun [] w ⟨initState, zeroTile, oneTile⟩

/-- The restored alternate odd tile of the word `w` (the output of the ordinary schedule of `w`). -/
def restoredOddTile (w : Word) : Tile := (restoredChildren w (restoredState w)).1

/-- The restored alternate even tile of the word `w`. -/
def restoredEvenTile (w : Word) : Tile := (restoredChildren w (restoredState w)).2

theorem restoredChildren_fst (w : Word) (hw : ¬ IsBase w) (s : AState) :
    (restoredChildren w s).1 =
      (altPair (phase w == 1) (lastDigit w) s.std.tOdd s.std.tEven
        (shift s.aOdd (alternateRestoration w .odd)) (shift s.aEven (alternateRestoration w .even))
        s.std.par.odd s.std.par.even).1 := by
  unfold restoredChildren
  rw [if_neg hw]

theorem restoredChildren_snd (w : Word) (hw : ¬ IsBase w) (s : AState) :
    (restoredChildren w s).2 =
      (altPair (phase w == 1) (lastDigit w) s.std.tOdd s.std.tEven
        (shift s.aOdd (alternateRestoration w .odd)) (shift s.aEven (alternateRestoration w .even))
        s.std.par.odd s.std.par.even).2 := by
  unfold restoredChildren
  rw [if_neg hw]

/-- The base run of a pure word has that word. -/
theorem pureRun_word (w : Word) (hw : IsBase w) : (pureRun w).word = w := by
  rcases w with _ | ⟨d, rest⟩
  · rfl
  · rcases hw with h | h | h
    · simp at h
    · have hd : d = Digit.three := h _ (by simp)
      subst hd
      have hr : rest = List.replicate rest.length Digit.three := by
        rw [List.eq_replicate_iff]
        exact ⟨rfl, fun b hb => h b (by simp [hb])⟩
      simp only [pureRun, BaseRun.word]
      rw [List.replicate_succ, ← hr]
    · have hd : d = Digit.two := h _ (by simp)
      subst hd
      have hr : rest = List.replicate rest.length Digit.two := by
        rw [List.eq_replicate_iff]
        exact ⟨rfl, fun b hb => h b (by simp [hb])⟩
      simp only [pureRun, BaseRun.word]
      rw [List.replicate_succ, ← hr]

/-- The last letter of a word extended by one letter. -/
theorem lastDigit_snoc (w : Word) (d : Digit) : lastDigit (w ++ [d]) = d := by
  simp [lastDigit]

/-- **The ordinary odd alternate schedule is the restored odd child.** For a non-base word `w = beforePush ++ [digit]`
with `digit` of type `1` or `3`, and a state whose standard and alternate registers are the parents' registers, the raw
sites of the ordinary schedule are the sites of `restoredChildren w s`. -/
theorem ordinaryAlternate_odd_eq_restored (parents : TileParents) (beforePush : Word) (digit : Digit)
    (hd : digit = Digit.one ∨ digit = Digit.three) (hw : ¬ IsBase (beforePush ++ [digit]))
    (s : AState) (h1 : s.std.tOdd = parents.odd.val.sites) (h2 : s.std.tEven = parents.even.val.sites)
    (h3 : s.aOdd = parents.alternateOdd.val.sites) (h4 : s.aEven = parents.alternateEven.val.sites)
    (h5 : s.std.par = parentsAt (beforePush ++ [digit]))
    (contacts : HeightTile.OrderedContacts (ordinaryAlternateSchedule parents beforePush digit .odd).first.val.sites
      (ordinaryAlternateSchedule parents beforePush digit .odd).copies) (v : Site) :
    v ∈ ((ordinaryAlternateSchedule parents beforePush digit .odd).first.val.insertAll
        (ordinaryAlternateSchedule parents beforePush digit .odd).copies contacts).sites ↔
      v ∈ (restoredChildren (beforePush ++ [digit]) s).1 := by
  rw [restoredChildren_fst _ hw, ordinaryAlternate_odd_structure parents beforePush digit hd contacts v,
    h1, h2, h3, h4, h5, lastDigit_snoc]

/-- **The ordinary even alternate schedule is the restored even child**, for digits `1` and `2`. -/
theorem ordinaryAlternate_even_eq_restored (parents : TileParents) (beforePush : Word) (digit : Digit)
    (hd : digit = Digit.one ∨ digit = Digit.two) (hw : ¬ IsBase (beforePush ++ [digit]))
    (s : AState) (h1 : s.std.tOdd = parents.odd.val.sites) (h2 : s.std.tEven = parents.even.val.sites)
    (h3 : s.aOdd = parents.alternateOdd.val.sites) (h4 : s.aEven = parents.alternateEven.val.sites)
    (h5 : s.std.par = parentsAt (beforePush ++ [digit]))
    (contacts : HeightTile.OrderedContacts (ordinaryAlternateSchedule parents beforePush digit .even).first.val.sites
      (ordinaryAlternateSchedule parents beforePush digit .even).copies) (v : Site) :
    v ∈ ((ordinaryAlternateSchedule parents beforePush digit .even).first.val.insertAll
        (ordinaryAlternateSchedule parents beforePush digit .even).copies contacts).sites ↔
      v ∈ (restoredChildren (beforePush ++ [digit]) s).2 := by
  rw [restoredChildren_snd _ hw, ordinaryAlternate_even_structure parents beforePush digit hd contacts v,
    h1, h2, h3, h4, h5, lastDigit_snoc]

end FLatticePaper.Tiles.RestoredAlternate
