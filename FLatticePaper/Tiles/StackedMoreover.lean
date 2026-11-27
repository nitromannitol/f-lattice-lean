import FLatticePaper.Tiles.PartialBoundary
import FLatticePaper.Tiles.ZeroOneGeneral
import FLatticePaper.Tiles.BinaryWords

/-! # The horizontal half of the Moreover of `lemma:stacked_zero_one_string` (surgical lines 1593-1597, 2540aed)

Statement only; no proof is claimed here. The text: for an almost palindrome `w` there are odometer sequences `{o_i^+}`
respecting `B_w` and `{o_i^-}` respecting the reversed string `B^r_{rev w}` with a common extension to the stacked string, and
(horizontal case) the affine factors of the first odometers differ by `a_{p,2}`.

Choices made here, each taken from the text:
* the zero-one strings have no doubled tiles (the zero and one tiles only; the vertical strings exclude doubled tiles, line 1329,
  and the zero-one strings of `lemma:stacked_zero_one_string` are the letter strings `B_w`);
* the positions of `B_w` are the zero-one positions `posF` (eq:zero-one-bs, lines 1266-1281), and the reversed string has the
  reversed positions `posF _ true`;
* the stacking of the two strings is the horizontal zero-one fixed offset `c(T_1^+) - c(T_1^-) = (-1, 2)` of
  `lemma:zero-one-fixed-offsets` (lines 1361-1364), which holds when `w` starts with `q` and ends with `p`;
* the slope relations are the surgical table `surgicalSlopeDiff` (forward for `o^+`, reversed for `o^-`);
* the common extension is offset zero on every overlap, within each family and across the two families;
* "affine factor" is the parameter `a` of `PTFamily` (the `i`-th odometer is `base(x - c_i) + a_i · x + b_i`).

Both halves are stated (the vertical one for almost palindromes starting with `p` and ending with `q`, with the stacking
`(-1,-1)` of the vertical fixed offsets and equal first affine factors). The non-overlap rule of `PTFamily.Respects` holds after
a shared translation by the affine factor of the first tile of each consecutive pair (see `PartialBoundary`). The vertical
model was checked on `pqpqq` exactly (scratchpad `vert_debug.py`, `exact_solve.py`): the first factors are forced equal. -/

namespace FLatticePaper.Tiles

/-- The horizontal stacking shift `c(T_1^+) - c(T_1^-)` of the zero-one fixed offsets (lines 1361-1364). -/
def horizontalStackShift : GInt := (-1, 2)

/-- The forward zero-one string of the letters `ℓ` on `n` tiles, placed at the zero-one positions. -/
def zoForward (ℓ : ℕ → Letter) (n : ℕ) : List (ZTile × GInt) :=
  (List.range n).map fun k => (letterZTile (ℓ k), posF .horizontal false ℓ k)

/-- The reversed zero-one string of the letters `ℓ` on `n` tiles, placed at the reversed positions, shifted so that the first
plus tile and the first minus tile differ by `horizontalStackShift`. -/
def zoReversedStacked (ℓ : ℕ → Letter) (n : ℕ) : List (ZTile × GInt) :=
  (List.range n).map fun k => (letterZTile (ℓ k), posF .horizontal true ℓ k - horizontalStackShift)

/-- The common extension of two families: the odometers agree (offset zero) on every overlap of two domains, within a family
and across the two families. -/
def WithinCommon (F : PTFamily) : Prop :=
  ∀ k < F.n, ∀ j < F.n, ∀ x ∈ F.dom k, x ∈ F.dom j → F.odo k x = F.odo j x

def CrossCommon (P M : PTFamily) : Prop :=
  ∀ k < P.n, ∀ j < M.n, ∀ x ∈ P.dom k, x ∈ M.dom j → P.odo k x = M.odo j x

/-- Locality of the cross overlaps: the plus tile `k` meets the minus tiles `k` and `k - 1` only. Checked numerically on the
horizontal words of length at most 9 (scratchpad `moreover_local.py`); not proved. This is the local-check structure: the
cross condition is then a finite window condition on consecutive letters. -/
def CrossLocal (P M : PTFamily) : Prop :=
  ∀ k < P.n, ∀ j < M.n, (∃ x, x ∈ P.dom k ∧ x ∈ M.dom j) → j = k ∨ j + 1 = k

/-- The horizontal half of the Moreover (for almost palindromes starting with `q` and ending with `p`): there are families
`P` on the forward string of `w` and `M` on the reversed stacked string, each respecting its string (surgical slope table,
non-overlap rule), with a common extension, and with first affine factors differing by `a_{p,2} = (0, -1)`. -/
def HorizontalMoreover (w : BinaryWord) : Prop :=
  IsAlmostPalindrome w → w.head? = some Letter.q → w.getLast? = some Letter.p →
    ∃ P M : PTFamily,
      P.ts = zoForward (lettersOf w false) w.length ∧
      M.ts = zoReversedStacked (lettersOf w true) w.length ∧
      P.Respects .horizontal false ∧
      M.Respects .horizontal true ∧
      WithinCommon P ∧ WithinCommon M ∧ CrossCommon P M ∧
      P.a 0 - M.a 0 = ((0 : ℤ), (-1 : ℤ))

/-- The vertical stacking shift `c(T_1^+) - c(T_1^-)` of the vertical zero-one fixed offsets (line 1368). -/
def verticalStackShift : GInt := (-1, -1)

/-- The vertical forward zero-one string of the letters `ℓ` on `n` tiles, at the vertical zero-one positions. -/
def zoForwardV (ℓ : ℕ → Letter) (n : ℕ) : List (ZTile × GInt) :=
  (List.range n).map fun k => (letterZTile (ℓ k), posF .vertical false ℓ k)

/-- The reversed vertical zero-one string of the letters `ℓ` on `n` tiles, shifted by `-verticalStackShift`. -/
def zoReversedStackedV (ℓ : ℕ → Letter) (n : ℕ) : List (ZTile × GInt) :=
  (List.range n).map fun k => (letterZTile (ℓ k), posF .vertical true ℓ k - verticalStackShift)

/-- The vertical half of the Moreover (for almost palindromes starting with `p` and ending with `q`): families `P` on the
forward vertical string and `M` on the reversed stacked vertical string, each respecting its string (the vertical table,
no exchange; non-overlap rule after a shared translation), with a common extension, and with equal first affine factors. -/
def VerticalMoreover (w : BinaryWord) : Prop :=
  IsAlmostPalindrome w → w.head? = some Letter.p → w.getLast? = some Letter.q →
    ∃ P M : PTFamily,
      P.ts = zoForwardV (lettersOf w false) w.length ∧
      M.ts = zoReversedStackedV (lettersOf w true) w.length ∧
      P.Respects .vertical false ∧
      M.Respects .vertical true ∧
      WithinCommon P ∧ WithinCommon M ∧ CrossCommon P M ∧
      P.a 0 = M.a 0

end FLatticePaper.Tiles
