import FLatticePaper.Farey.Birth
import Mathlib.Data.List.Induction

namespace FLatticePaper.Farey

/-- A retained register is either the corresponding endpoint atom or the
current register of a strict prefix of the same word. -/
theorem retained_eq_endpoint_or_prefix (word : Word) (parity : Parity) :
    (parentsAt word).retained parity = root.retained parity ∨
      ∃ earlier : Word, ∃ next : Digit, ∃ rest : Word, word = earlier ++ next :: rest ∧
        Birth.fraction (earlier, parity) = (parentsAt word).retained parity := by
  induction word using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton word digit ih =>
    have hupdate (h : ((parentsAt word).step digit).retained parity =
        (parentsAt word).current parity) :
        ((parentsAt word).step digit).retained parity = root.retained parity ∨
          ∃ earlier : Word, ∃ next : Digit, ∃ rest : Word,
            word ++ [digit] = earlier ++ next :: rest ∧
              Birth.fraction (earlier, parity) = ((parentsAt word).step digit).retained parity :=
      Or.inr ⟨word, digit, [], rfl, h.symm⟩
    have hkeep (h : ((parentsAt word).step digit).retained parity =
        (parentsAt word).retained parity) :
        ((parentsAt word).step digit).retained parity = root.retained parity ∨
          ∃ earlier : Word, ∃ next : Digit, ∃ rest : Word,
            word ++ [digit] = earlier ++ next :: rest ∧
              Birth.fraction (earlier, parity) = ((parentsAt word).step digit).retained parity := by
      rw [h]
      rcases ih with hend | ⟨earlier, next, rest, heq, hbirth⟩
      · exact Or.inl hend
      · exact Or.inr ⟨earlier, next, rest ++ [digit], by rw [heq, List.append_assoc]; rfl, hbirth⟩
    rw [parentsAt_append_singleton]
    cases parity <;> cases digit
    · exact hupdate rfl
    · exact hupdate rfl
    · exact hkeep rfl
    · exact hupdate rfl
    · exact hkeep rfl
    · exact hupdate rfl

/-- The inverse search for a non-endpoint retained tile stays on the lineage.
Its uniquely determined birth can therefore replace the prefix scan. -/
theorem retained_birth_prefix (word : Word) (parity : Parity)
    (hne : (parentsAt word).retained parity ≠ root.retained parity) :
    ∃ earlier : Word, ∃ next : Digit, ∃ rest : Word, word = earlier ++ next :: rest ∧
      ∀ (hinterior : ((parentsAt word).retained parity).Interior)
        (hreduced : ((parentsAt word).retained parity).Reduced),
        birthOf ((parentsAt word).retained parity) hinterior hreduced = (earlier, parity) := by
  rcases retained_eq_endpoint_or_prefix word parity with hend | ⟨earlier, next, rest, hword, hbirth⟩
  · exact False.elim (hne hend)
  · refine ⟨earlier, next, rest, hword, fun hinterior hreduced => ?_⟩
    apply Birth.fraction_injective
    exact (fraction_birthOf _ hinterior hreduced).trans hbirth.symm

theorem retained_interior_of_ne_endpoint (word : Word) (parity : Parity)
    (hne : (parentsAt word).retained parity ≠ root.retained parity) :
    ((parentsAt word).retained parity).Interior := by
  rcases retained_eq_endpoint_or_prefix word parity with hend | ⟨earlier, _, _, _, hbirth⟩
  · exact False.elim (hne hend)
  · rw [← hbirth]
    exact Birth.interior (earlier, parity)

theorem retained_reduced (word : Word) (parity : Parity) :
    ((parentsAt word).retained parity).Reduced :=
  match parity with
  | .odd => (parentsAt_valid word).odd_reduced
  | .even => (parentsAt_valid word).even_reduced

/-- The exact retained birth used for alternate restoration. Endpoint atoms
have no creation word. -/
def retainedBirth? (word : Word) (parity : Parity) : Option Birth :=
  if h : (parentsAt word).retained parity = root.retained parity then none
  else some (birthOf ((parentsAt word).retained parity)
    (retained_interior_of_ne_endpoint word parity h) (retained_reduced word parity))

theorem retainedBirth?_eq_some_of_ne_endpoint (word : Word) (parity : Parity)
    (hne : (parentsAt word).retained parity ≠ root.retained parity) :
    ∃ earlier : Word, ∃ next : Digit, ∃ rest : Word, word = earlier ++ next :: rest ∧
      retainedBirth? word parity = some (earlier, parity) := by
  obtain ⟨earlier, next, rest, hword, hbirth⟩ := retained_birth_prefix word parity hne
  exact ⟨earlier, next, rest, hword, by simp [retainedBirth?, hne, hbirth]⟩

end FLatticePaper.Farey
