import FLatticePaper.Tiles.SiteStringsDecide
import FLatticePaper.Tiles.SiteStrings

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.Standard

#print axioms FLatticePaper.Tiles.SiteStringsDecide.fs_2_odd
#print axioms FLatticePaper.Tiles.SiteStringsDecide.fs_nonvacuous
#eval (markedSites (oddTile [Digit.two]) (hWordOf [Digit.two] false) (vWordOf [Digit.two] false)).length
#eval (lowLeft (oddTile [Digit.two]), halfTurnCentre (oddTile [Digit.two]))
#eval (markedSites (oddTile []) (hWordOf [] false) (vWordOf [] false)).length
#eval (lowLeft (oddTile []), halfTurnCentre (oddTile []))
#eval (markedSites (oddTile [Digit.one]) (hWordOf [Digit.one] false) (vWordOf [Digit.one] false)).length
