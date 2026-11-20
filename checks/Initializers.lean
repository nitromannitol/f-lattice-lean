import FLatticePaper.Construction.BaseRegisters

namespace FLatticePaper.Checks

open Construction

private def parseHeightRow (row : String) : IO (ℤ × ℤ × ℤ) := do
  let [col, line, height] := row.splitOn "\t" | throw (IO.userError ("Invalid row: " ++ row))
  let some col := col.toInt? | throw (IO.userError ("Invalid column: " ++ col))
  let some line := line.toInt? | throw (IO.userError ("Invalid line: " ++ line))
  let some height := height.toInt? | throw (IO.userError ("Invalid height: " ++ height))
  return (col, line, height)

private def compareFixture (name : String) (tile : NonemptyTile) : IO Unit := do
  let filename := "paper/Code/test/fixtures/" ++ name ++ ".tsv"
  let lines ← IO.FS.lines filename
  let rows ← (lines.toList.drop 1).mapM parseHeightRow
  let actual := tile.val.sites.attach.image (fun site => (site.val.1, site.val.2, tile.val.height site))
  unless actual = rows.toFinset do
    throw (IO.userError ("Occupied heights do not match " ++ filename))

private def compareRun (fixtureStem : String) (run : BaseRun) : IO Unit := do
  let tiles := run.registers.llCenter
  compareFixture (fixtureStem ++ "_std_1") tiles.standard.currentOdd
  compareFixture (fixtureStem ++ "_std_2") tiles.standard.currentEven
  compareFixture (fixtureStem ++ "_alt_1") tiles.alternate.currentOdd
  compareFixture (fixtureStem ++ "_alt_2") tiles.alternate.currentEven
  IO.println s!"All four occupied height sets match for {fixtureStem}."

#eval compareRun "empty" .empty
#eval compareRun "22" (.twos 1)
#eval compareRun "33" (.threes 1)

#print axioms BaseMask.tile_nonempty
#print axioms BaseRun.registers

end FLatticePaper.Checks
