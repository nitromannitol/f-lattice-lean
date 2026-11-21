import FLatticePaper.Tiles.ZeroOneOdometers
import FLatticePaper.Tiles.ZeroOneStringPositions

open FLatticePaper.Tiles

-- diagnostics: base slopes of the zero-odometer on T_{0/1} and of the one-odometer on T_{1/1}
#eval slopeOf zeroOdometer zeroTileSites
#eval slopeOf oneOdometer oneTileSites
#eval zeroOneWordCount 6

-- all words of length 1 to 6 pass, in both orientations, for the string and for its reversal
example : zeroOneWordCount 6 = 126 := by decide +kernel
example : zeroOneFailures 6 = [] := by decide +kernel

-- sensitivity: a family built for the horizontal string is rejected by the vertical checks
example : (buildFamily .horizontal false [.p, .q]).respectsB .vertical = false := by decide +kernel
example : (buildFamily .horizontal false [.p, .q]).respectsB .horizontal = true := by decide +kernel

-- the test words, and the decided checks on them
def zeroOneTestWords : List BinaryWord := (List.range 6).flatMap fun k => wordsOfLength (k + 1)

theorem zeroOne_checks_upTo_six :
    ∀ o ∈ [Orientation.horizontal, Orientation.vertical], ∀ rev ∈ [false, true],
      ∀ w ∈ zeroOneTestWords,
        (buildFamily o rev w).respectsB o = true ∧ (buildFamily o rev w).commonB = true := by
  decide +kernel

theorem mem_wordsOfLength (w : BinaryWord) : w ∈ wordsOfLength w.length := by
  induction w with
  | nil => simp [wordsOfLength]
  | cons l w ih =>
    simp only [wordsOfLength, List.length_cons, List.mem_flatMap]
    exact ⟨w, ih, by cases l <;> simp⟩

/-- `lemma:stacked_zero_one_string`, first sentence, for every binary word of length at most 6: the family
built from the word is a zero-one family respecting its horizontal string (or vertical string) and its reversal,
with a common extension. -/
theorem zeroOneFirstSentence_upTo_six (o : Orientation) (rev : Bool) (w : BinaryWord)
    (h1 : 1 ≤ w.length) (h6 : w.length ≤ 6) : ZeroOneFirstSentence o rev w := by
  have ho : o ∈ [Orientation.horizontal, Orientation.vertical] := by cases o <;> simp
  have hr : rev ∈ [false, true] := by cases rev <;> simp
  have hw : w ∈ zeroOneTestWords := by
    unfold zeroOneTestWords
    refine List.mem_flatMap.mpr ⟨w.length - 1, List.mem_range.mpr (by omega), ?_⟩
    rw [show w.length - 1 + 1 = w.length by omega]
    exact mem_wordsOfLength w
  obtain ⟨h, h'⟩ := zeroOne_checks_upTo_six o ho rev hr w hw
  exact zeroOneFirstSentence_of_checks o rev w h h'

example : ZeroOneFirstSentence .horizontal false [.p, .q] := zeroOneFirstSentence_upTo_six _ _ _ (by decide +kernel) (by decide +kernel)

#print axioms zeroOneFirstSentence_upTo_six
#print axioms FLatticePaper.Tiles.zeroOneFirstSentence_of_checks
#print axioms zeroOne_checks_upTo_six

-- the general theorem: the first sentence of lemma:stacked_zero_one_string for every binary word
#print axioms FLatticePaper.Tiles.zeroOneFirstSentence_all
