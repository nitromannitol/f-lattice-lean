import FLatticePaper.Construction.Native
import FLatticePaper.Tiles.AlternateTiles

/-! # The constructor's tiles, as a second reading of `def:alternate_tiles` (task 34, PROVISIONAL)

`evaluateNative w` (Construction/Native.lean) runs the delivered constructor on the word `w` and returns the four tiles of
its current children, with the payloads normalised by `llCenter`. The definitions below read the cell sets of those payloads.
They are the constructor's own output, so no convention is chosen here; the differences from the literal reading of the
text (`AlternateTiles.lean`) are recorded in `scripts/native_compare.py` and the report of task 34:

* the standard children of the words `23`, `223`, `231`, `232`, `233` differ from `StandardTiles.lean` by exactly two cells
  (7 of 80 child tiles): the constructor's correction slots (`correctedStandardSchedule`, helpers aligned by upper-right
  corners) use parent tiles with corner cells removed (the TeX's truncation `T^{sm}`, `prop:base_cases`), where the text uses
  the full parent tile;
* the alternate children of `23`, `223`, `231`, `232`, `233` differ in the same way (11 child tiles up to translation), and
  the word `31` (odd child) differs by a restoration of the retained alternate parent (`alternateRestoration`, a
  birth-dependent translation not stated in the text). The constructor and the literal reading agree on every word beginning
  with `1`, and the base words `2^k`, `3^k` agree with the literal base tiles.

Rotation clause of `lemma:alternate_tile_properties` (clause 1: `R(T̂(n/d)) = T̂(R(n/d))`), checked on the 33 words of length
at most three that are not all-2 or all-3 (the length-four words are not computed):
* shape failures (no translation makes the two sets equal): literal reading 8, smallest `21` even; constructor reading 14,
  smallest `23` even (`23`, `32`, `223`, `231`, `232`, `233`, `321`, `322`, `323`, `332`); the two sets do not overlap;
* translation-only failures (equal up to a translation, but not by `tF(current)`): literal 46, smallest `1` odd; constructor
  40, smallest `1` odd; the failures at `1` (both parities) are identical in the two readings, so they are not a difference
  between the readings: the offset convention of the rotation identity is not matched by either.
Both readings therefore fail clause 1 at the words above. The rotation clause is referred to the author; this reading is kept
as PROVISIONAL and is not claimed to satisfy `lemma:alternate_tile_properties`.

Nothing here is proved: the constructor is evaluated by its sparse schedules, and the claims of
`lemma:alternate_tile_properties` are checked numerically for the words up to length three (scripts/native_compare.py,
scripts/native_diff.py; extraction in checks/NativeTiles.lean and checks/NativeTilesRoots.lean). -/

namespace FLatticePaper.Tiles.AlternateConstructor

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction

/-- The cells of the constructor's standard odd child of `w` (PROVISIONAL reading, `standard.currentOdd`). -/
def constructorStdOdd (w : Word) : Option (Finset Site) :=
  match evaluateNative w with
  | .ok regs => some regs.standard.currentOdd.val.sites
  | .error _ => none

/-- The cells of the constructor's standard even child of `w` (PROVISIONAL reading, `standard.currentEven`). -/
def constructorStdEven (w : Word) : Option (Finset Site) :=
  match evaluateNative w with
  | .ok regs => some regs.standard.currentEven.val.sites
  | .error _ => none

/-- The cells of the constructor's alternate odd child `T̂(p_0)` of `w` (PROVISIONAL reading, `alternate.currentOdd`). -/
def constructorAltOdd (w : Word) : Option (Finset Site) :=
  match evaluateNative w with
  | .ok regs => some regs.alternate.currentOdd.val.sites
  | .error _ => none

/-- The cells of the constructor's alternate even child `T̂(q_0)` of `w` (PROVISIONAL reading, `alternate.currentEven`). -/
def constructorAltEven (w : Word) : Option (Finset Site) :=
  match evaluateNative w with
  | .ok regs => some regs.alternate.currentEven.val.sites
  | .error _ => none

end FLatticePaper.Tiles.AlternateConstructor
