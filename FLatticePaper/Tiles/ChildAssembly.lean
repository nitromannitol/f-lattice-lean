import FLatticePaper.Tiles.SurgicalOdometerStep
import FLatticePaper.Tiles.ChildGlue

/-! The existence assembly of the odd (and even) standard step, with the three inputs named.

The step `IsStdStepP0` has four pieces: two copies of the odd register (flag `false`, pieces `0`, `1`) and two doubled copies
of the even register (flag `true`, pieces `2`, `3`, each a single subodometer on its doubled domain). A parent odometer
places all four pieces if the placed values agree on the overlaps, with the three inputs:

* `PlacedMixed` (H1, claim (d), OPEN): placed pieces of different parents meet only inside their marks;
* `PlacedMarksAgree` (H2, OPEN): placed pieces of different parents agree at the sites of both marks
  (`lemma:stacked_zero_one_string`, i.e. Moreover + (a) + (b) at the interface);
* `PlacedSameAgree` (H3, OPEN): placed pieces of one parent agree on their whole overlap (the operator's (c) at the lower
  depth). Only the pairs that overlap need it (see the numerics in the report).

The conclusion is one parent odometer that places every piece (`placed_step_exists`); this is the existence content of
`IsStdStepP0`, with the glued values on the union of the placed domains. -/

namespace FLatticePaper.Tiles.ChildAssembly

open FLatticePaper.Tiles.ChildGlue

/-- The placed domain of piece `i`: its domain translated by its offset. -/
def placedSet (ch : ℕ → PartialOdometer) (off : ℕ → ℤ × ℤ) (i : ℕ) : Set (ℤ × ℤ) :=
  ((ch i).dom.image (· + off i) : Finset (ℤ × ℤ))

/-- The value of piece `i` placed in the parent: its value at the untranslated site, plus the affine correction. -/
def placedVal (ch : ℕ → PartialOdometer) (off a : ℕ → ℤ × ℤ) (i : ℕ) (z : ℤ × ℤ) : ℤ :=
  (ch i).val (z - off i) + ((a i).1 * z.1 + (a i).2 * z.2)

/-- The parent flag of piece `i`: pieces `0`, `1` copy the odd register (`false`), pieces `2`, `3` the doubled even register
(`true`). -/
def pieceFlag4 (i : ℕ) : Bool := decide (2 ≤ i)

/-- Input H1 (claim (d), OPEN): placed pieces of different parents meet only inside their marks. -/
def PlacedMixed (ch : ℕ → PartialOdometer) (off : ℕ → ℤ × ℤ) (M : ℕ → Set (ℤ × ℤ)) : Prop :=
  ∀ i j, i < 4 → j < 4 → pieceFlag4 i ≠ pieceFlag4 j →
    ∀ z, z ∈ placedSet ch off i → z ∈ placedSet ch off j → z ∈ M i ∧ z ∈ M j

/-- Input H2 (OPEN): placed pieces of different parents agree at the sites of both marks. -/
def PlacedMarksAgree (ch : ℕ → PartialOdometer) (off a : ℕ → ℤ × ℤ) (M : ℕ → Set (ℤ × ℤ)) : Prop :=
  ∀ i j, i < 4 → j < 4 → pieceFlag4 i ≠ pieceFlag4 j →
    ∀ z, z ∈ M i → z ∈ M j → placedVal ch off a i z = placedVal ch off a j z

/-- Input H3 (OPEN): placed pieces of one parent agree on their whole overlap. -/
def PlacedSameAgree (ch : ℕ → PartialOdometer) (off a : ℕ → ℤ × ℤ) : Prop :=
  ∀ i j, i < 4 → j < 4 → i ≠ j → pieceFlag4 i = pieceFlag4 j →
    ∀ z, z ∈ placedSet ch off i → z ∈ placedSet ch off j → placedVal ch off a i z = placedVal ch off a j z

/-- **The existence assembly.** Given the three inputs, one parent odometer places all four pieces. -/
theorem placed_step_exists (ch : ℕ → PartialOdometer) (off a : ℕ → ℤ × ℤ) (M : ℕ → Set (ℤ × ℤ))
    (H1 : PlacedMixed ch off M) (H2 : PlacedMarksAgree ch off a M) (H3 : PlacedSameAgree ch off a) :
    ∃ parent : PartialOdometer, ∀ i, i < 4 → PlacedPiece parent (ch i) (off i) (a i) := by
  obtain ⟨g, hg⟩ := glue_full 4 (placedSet ch off) M pieceFlag4 (placedVal ch off a) H1 H2 H3
  refine ⟨⟨(Finset.range 4).biUnion (fun i => (ch i).dom.image (· + off i)), g⟩, ?_⟩
  intro i hi
  refine ⟨0, ?_, ?_⟩
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_range.2 hi, Finset.mem_image.2 ⟨x, hx, rfl⟩⟩
  · intro x hx
    have hxD : x ∈ placedSet ch off i := Finset.mem_coe.2 hx
    have hgx := hg i hi x hxD
    simp only [placedVal] at hgx
    simp only [add_zero]
    exact hgx

end FLatticePaper.Tiles.ChildAssembly
