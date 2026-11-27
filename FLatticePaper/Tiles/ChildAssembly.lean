import FLatticePaper.Tiles.SurgicalOdometerStep
import FLatticePaper.Tiles.ChildGlue

/-! The existence assembly of the odd (and even) standard step, with the three inputs named.

The step `IsStdStepP0` has four pieces: two copies of the odd register (flag `false`, pieces `0`, `1`) and two doubled copies
of the even register (flag `true`, pieces `2`, `3`, each a single subodometer on its doubled domain). A parent odometer
places all four pieces if the placed values agree on the overlaps, with the three inputs:

* `PlacedMixed` (H1, claim (d), OPEN): placed pieces of different parents meet only inside their marks;
* `PlacedMarksAgree` (H2, OPEN): placed pieces of different parents agree at the sites of both marks
  (`lemma:stacked_zero_one_string`, i.e. Moreover + (a) + (b) at the interface);
* `PlacedDoubledAgree` (H3, (c), OPEN): the two copies of a doubled piece agree on their whole overlap. The other same-parent
  overlaps are removed by the Step 1 deletion, which keeps one copy on each overlap (`ChildGlue.keptSet`).

The conclusion is one parent odometer that places every piece on its kept part (`placed_step_kept`); this is the existence
content of `IsStdStepP0`, with the glued values on the union of the placed domains. -/

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

/-- Input (c) on doubled pairs (OPEN): the two placed copies of a doubled piece (`Dbl i j`) agree on their whole overlap. No other
same-parent agreement is assumed: the Step 1 deletion makes the other overlaps disjoint on their kept parts. -/
def PlacedDoubledAgree (ch : ℕ → PartialOdometer) (off a : ℕ → ℤ × ℤ) (Dbl : ℕ → ℕ → Prop) : Prop :=
  ∀ i j, i < 4 → j < 4 → i < j → pieceFlag4 i = pieceFlag4 j → Dbl i j →
    ∀ z, z ∈ placedSet ch off i → z ∈ placedSet ch off j → placedVal ch off a i z = placedVal ch off a j z

/-- A placed piece restricted to its kept part `K`: the parent is defined on `K` by the piece's value, placed by `off` with the
affine correction `a` and the constant `0`. -/
def PlacedKeptPiece (parent child : PartialOdometer) (K : Set (ℤ × ℤ)) (off a : ℤ × ℤ) : Prop :=
  (∀ x ∈ K, x ∈ parent.dom) ∧
    ∀ x ∈ K, parent.val x = child.val (x - off) + (a.1 * x.1 + a.2 * x.2)

/-- **The existence assembly on kept domains** (the operator's Step 1, manuscript dbd159d): from the mixed inputs `H1`, `H2` and
the doubled-pair agreement `H3`, one parent odometer, on the union of the placed domains, places every piece on its kept part. -/
theorem placed_step_kept (ch : ℕ → PartialOdometer) (off a : ℕ → ℤ × ℤ) (M : ℕ → Set (ℤ × ℤ)) (Dbl : ℕ → ℕ → Prop)
    (H1 : PlacedMixed ch off M) (H2 : PlacedMarksAgree ch off a M) (H3 : PlacedDoubledAgree ch off a Dbl) :
    ∃ parent : PartialOdometer, ∀ i, i < 4 →
      PlacedKeptPiece parent (ch i) (keptSet (placedSet ch off) pieceFlag4 Dbl i) (off i) (a i) := by
  obtain ⟨g, hg⟩ := glue_kept_gen 4 (placedSet ch off) M pieceFlag4 Dbl (placedVal ch off a) H1 H2 H3
  refine ⟨⟨(Finset.range 4).biUnion (fun i => (ch i).dom.image (· + off i)), g⟩, ?_⟩
  intro i hi
  refine ⟨?_, ?_⟩
  · intro z hz
    have hzD : z ∈ placedSet ch off i := hz.1
    have hzF : z ∈ (ch i).dom.image (· + off i) := Finset.mem_coe.1 hzD
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_range.2 hi, hzF⟩
  · intro x hx
    have hgx := hg i hi x hx
    simp only [placedVal] at hgx
    exact hgx

end FLatticePaper.Tiles.ChildAssembly
