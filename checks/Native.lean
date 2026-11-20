import FLatticePaper.Construction.Native

namespace FLatticePaper.Checks

open Construction Farey

private def parseWord (stem : String) : IO Word :=
  if stem = "empty" then pure []
  else stem.toList.mapM fun letter => match letter with
    | '1' => pure .one
    | '2' => pure .two
    | '3' => pure .three
    | _ => throw (IO.userError ("Invalid word: " ++ stem))

private def parseHeightRow (row : String) : IO (ℤ × ℤ × ℤ) := do
  let [col, line, height] := row.splitOn "\t" | throw (IO.userError ("Invalid row: " ++ row))
  let some col := col.toInt? | throw (IO.userError ("Invalid column: " ++ col))
  let some line := line.toInt? | throw (IO.userError ("Invalid line: " ++ line))
  let some height := height.toInt? | throw (IO.userError ("Invalid height: " ++ height))
  return (col, line, height)

private def compareNativeFixtures : IO Unit := do
  let entries ← (System.FilePath.mk "paper/Code/test/fixtures").readDir
  let mut words : List (String × TileRegisters) := []
  let mut count := 0
  for entry in entries do
    if entry.fileName.endsWith ".tsv" then
      let [stem, family, slot] := entry.fileName.splitOn "_" |
        throw (IO.userError ("Invalid fixture name: " ++ entry.fileName))
      let registers ← match words.lookup stem with
        | some registers => pure registers
        | none =>
          match evaluateNative (← parseWord stem) with
          | .ok registers => pure registers
          | .error reason => throw (IO.userError (stem ++ ": " ++ reason))
      words := (stem, registers) :: words
      let donors ← match family with
        | "std" => pure registers.standard
        | "alt" => pure registers.alternate
        | _ => throw (IO.userError ("Invalid family: " ++ family))
      let tile ← match slot with
        | "1.tsv" => pure donors.currentOdd
        | "2.tsv" => pure donors.currentEven
        | _ => throw (IO.userError ("Invalid slot: " ++ slot))
      let rows ← ((← IO.FS.lines entry.path).toList.drop 1).mapM parseHeightRow
      let actual := tile.val.sites.attach.image (fun site => (site.val.1, site.val.2, tile.val.height site))
      unless actual = rows.toFinset do
        throw (IO.userError ("Occupied heights do not match " ++ entry.fileName))
      count := count + 1
  unless count = 31 do throw (IO.userError s!"Expected 31 pinned fixtures, read {count}.")
  IO.println s!"All {count} pinned occupied height sets match the unbounded Lean constructor."

#eval compareNativeFixtures

#print axioms evaluateNativeState_history
#print axioms evaluateNative_base
#print axioms correctionPieces_rest_length
#print axioms PlacedSchedule.eval_ok_iff
#print axioms PlacedSchedule.eval_tile_agrees
#print axioms PlacedSchedule.eval_correction_agrees

end FLatticePaper.Checks
