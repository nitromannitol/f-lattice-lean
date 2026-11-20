import FLatticePaper.Construction.BaseMasks

namespace FLatticePaper.Construction

abbrev NonemptyTile := {tile : HeightTile Site // tile.sites.Nonempty}

namespace NonemptyTile

def place (tile : NonemptyTile) (offset slope : Site) : NonemptyTile :=
  ⟨tile.val.place offset slope, tile.val.place_sites_nonempty offset slope tile.property⟩

def trim (tile : NonemptyTile) : NonemptyTile :=
  ⟨tile.val.trim tile.property, tile.val.trim_sites_nonempty tile.property⟩

def llCenter (tile : NonemptyTile) : NonemptyTile :=
  ⟨tile.val.llCenter tile.property, ⟨0, tile.val.zero_mem_llCenter tile.property⟩⟩

end NonemptyTile

def BaseMask.asNonemptyTile (kind : BaseMask) (den : ℤ) (hden : kind.Valid den) : NonemptyTile :=
  ⟨kind.tile den hden, kind.tile_nonempty den hden⟩

/-- The four source registers for one family, in the original order. -/
structure FourTiles where
  currentOdd : NonemptyTile
  currentEven : NonemptyTile
  retainedOdd : NonemptyTile
  retainedEven : NonemptyTile

structure TileRegisters where
  standard : FourTiles
  alternate : FourTiles

def FourTiles.llCenter (tiles : FourTiles) : FourTiles :=
  ⟨tiles.currentOdd.llCenter, tiles.currentEven.llCenter,
    tiles.retainedOdd.llCenter, tiles.retainedEven.llCenter⟩

def TileRegisters.llCenter (tiles : TileRegisters) : TileRegisters :=
  ⟨tiles.standard.llCenter, tiles.alternate.llCenter⟩

/-- The finite endpoint atoms used as retained source tiles, not plane odometers. -/
inductive EndpointAtom where
  | zero | one

/-- The literal endpoint mask before its attachment to the current standard. -/
def EndpointAtom.atOrigin : EndpointAtom → NonemptyTile
  | .zero =>
    ⟨maskedTile (0, 0) (1, 2) (fun site => some (if site.2 = 2 then -1 else 0)),
      ⟨(0, 0), by decide⟩⟩
  | .one =>
    ⟨maskedTile (0, 0) (1, 1) (fun site => some (if site = (0, 1) then -1 else 0)),
      ⟨(0, 0), by decide⟩⟩

/-- Attach the endpoint at the standard's occupied lower left, then trim. -/
def EndpointAtom.attach (endpoint : EndpointAtom) (standard : NonemptyTile) : NonemptyTile :=
  (endpoint.atOrigin.place (standard.val.lowerLeft standard.property) 0).trim

/-- The common empty word and the two nonempty pure prefixes supported by
`base_quad`. A nonempty run has length `extra + 1`. -/
inductive BaseRun where
  | empty
  | twos (extra : ℕ)
  | threes (extra : ℕ)

/-- All eight registers of the literal initializer, before the final LL centering. -/
def BaseRun.registers : BaseRun → TileRegisters
  | .empty =>
    let odd := BaseMask.asNonemptyTile .stairOdd 3 (by simp [BaseMask.Valid])
    let even := BaseMask.asNonemptyTile .stairEven 3 (by simp [BaseMask.Valid])
    let retainedOdd := EndpointAtom.zero.attach odd
    let retainedEven := EndpointAtom.one.attach even
    let oddAlt := BaseMask.asNonemptyTile .stairOddAlt 3 (by simp [BaseMask.Valid])
    let evenAlt := BaseMask.asNonemptyTile .stairEvenAlt 3 (by simp [BaseMask.Valid])
    ⟨⟨odd, even, retainedOdd, retainedEven⟩, ⟨oddAlt, evenAlt, retainedOdd, retainedEven⟩⟩
  | .twos extra =>
    let den : ℤ := 2 * (extra : ℤ) + 3
    have hprev : 3 ≤ den ∧ den % 2 = 1 := by dsimp [den]; omega
    have hstair : 3 ≤ den + 2 ∧ (den + 2) % 2 = 1 := by omega
    have hladder : 4 ≤ den + 1 ∧ (den + 1) % 2 = 0 := by omega
    let odd := BaseMask.asNonemptyTile .stairOdd (den + 2) hstair
    let even := BaseMask.asNonemptyTile .ladderEven (den + 1) hladder
    let retainedOdd := BaseMask.asNonemptyTile .stairOdd den hprev
    let retainedEven := EndpointAtom.one.attach even
    let oddAlt := BaseMask.asNonemptyTile .stairOddAlt (den + 2) hstair
    let evenAlt := BaseMask.asNonemptyTile .ladderEvenAlt (den + 1) hladder
    let retainedOddAlt := BaseMask.asNonemptyTile .stairOddAlt den hprev
    ⟨⟨odd, even, retainedOdd, retainedEven⟩, ⟨oddAlt, evenAlt, retainedOddAlt, retainedEven⟩⟩
  | .threes extra =>
    let den : ℤ := 2 * (extra : ℤ) + 3
    have hprev : 3 ≤ den ∧ den % 2 = 1 := by dsimp [den]; omega
    have hstair : 3 ≤ den + 2 ∧ (den + 2) % 2 = 1 := by omega
    have hladder : 4 ≤ den + 1 ∧ (den + 1) % 2 = 0 := by omega
    let odd := BaseMask.asNonemptyTile .ladderOdd (den + 1) hladder
    let even := BaseMask.asNonemptyTile .stairEven (den + 2) hstair
    let retainedOdd := EndpointAtom.zero.attach odd
    let retainedEven := BaseMask.asNonemptyTile .stairEven den hprev
    let oddAlt := BaseMask.asNonemptyTile .ladderOddAlt (den + 1) hladder
    let evenAlt := BaseMask.asNonemptyTile .stairEvenAlt (den + 2) hstair
    let retainedEvenAlt := BaseMask.asNonemptyTile .stairEvenAlt den hprev
    ⟨⟨odd, even, retainedOdd, retainedEven⟩, ⟨oddAlt, evenAlt, retainedOdd, retainedEvenAlt⟩⟩

end FLatticePaper.Construction
